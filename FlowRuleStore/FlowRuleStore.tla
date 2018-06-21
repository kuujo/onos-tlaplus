--------------------------- MODULE FlowRuleStore ---------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

\* The set of node identifiers
CONSTANT Node

\* The set of available device identifiers
CONSTANT Device

\* The set of available flows
CONSTANT Flow

\* The total number of buckets
CONSTANT NumBuckets

\* A constant value
CONSTANT Nil

\* Message type constants
CONSTANTS
    DigestsRequest,
    DigestsResponse,
    BucketsRequest,
    BucketsResponse,
    BackupRequest,
    BackupResponse

\* A sequence of messages for each node
VARIABLE messages

\* States (terms and mastership) for each node
VARIABLE states

\* The highest term for each device, used to ensure terms are monotonically increasing
VARIABLES terms

\* A queue of mastership changes for each device on each node
VARIABLE masterships

\* The last logical backup time for each bucket/device/node
VARIABLE backups

\* The local logical clock for each node
VARIABLE clocks

\* The flow buckets for each device on each node
VARIABLE flows

----

(* An implementation of lamport clocks for causal ordering of events *)

\* Increments the logical clock for the given node
TickClock(n) == states' = [states EXCEPT ![n].timestamp = states[n].timestamp + 1]

\* Updates the logical clock for the given node using the given timestamp
UpdateClock(n, t) ==
   \/ /\ states[n].timestamp < t
      /\ states' = [states EXCEPT ![n].timestamp = t + 1]
   \/ /\ states[n].timestamp >= t
      /\ states' = [states EXCEPT ![n].timestamp = states[n].timestamp + 1]

----
(*
Messages are modelled as queues for consistency with TCP semantics.
Each node has a separate channel for all requests and responses.
The logical clock is managed on each send/receive by attaching a
timestamp to all outgoing messages and updating the node's clock
on receive.
*)

\* Returns a sequence with the head removed
Pop(q) == SubSeq(q, 2, Len(q))

\* Sends a request on the given node's channel
SendMessage(n, m) ==
    /\ TickClock(n)
    /\ LET message == [m EXCEPT !.clock = clocks'[n]]
       IN messages' = [messages EXCEPT ![n] = Append(messages[n], message)]

\* Removes a message from the given node's channel
ReceiveMessage(n, m) == 
   /\ UpdateClock(n, m.clock)
   /\ messages' = [messages EXCEPT ![n] = Pop(messages[n])]

----

(* This section models flows arbitrarily added to/removed from each node *)

\* Returns the bucket ID for the given flow ID by hashing the flow ID to the number of buckets
GetBucket(fid) == (fid % NumBuckets) + 1

\* Adds a flow 'f' to node 'n' if it believes itself to be the master
\* The given flow is hashed to the appropriate bucket within the device table on node 'n'.
AddFlow(n, f) ==
   /\ states[n][f.did].master
   /\ TickClock(n)
   /\ flows' = [flows EXCEPT ![n][f.did][GetBucket(f.fid)] = [
                   term      |-> states[n][f.did].term, 
                   timestamp |-> clocks'[n], 
                   entries   |-> flows[n][f.did][GetBucket(f.fid)] \cup {f}]]
   /\ UNCHANGED <<messages, states, terms, masterships>>

\* Removes a flow 'f' from node 'n' if it believes itself to be the master
\* The given flow is hashed to the appropriate bucket within the device table on node 'n'.
RemoveFlow(n, f) ==
   /\ states[n][f.did].master
   /\ TickClock(n)
   /\ Cardinality(flows[n][f.did][f.fid % NumBuckets] \cap {f}) = 1
   /\ flows' = [flows EXCEPT ![n][f.did][GetBucket(f.fid)] = [
                   term      |-> states[n][f.did].term, 
                   timestamp |-> clocks'[n], 
                   entries   |-> flows[n][f.did][GetBucket(f.fid)] \ {f}]]
   /\ UNCHANGED <<messages, states, terms, masterships>>

----

(*
Mastership terms are modelled as a queue of monotonically increasing term/master notifications.
Each node has a separate notification queue, and mastership terms are added to all queues in the same
order. This models the fact that different nodes can learn of mastership changes at different times,
but each node sees terms increase with the same master for each term.
*)

\* One significant difference from the spec and the implementation is that the spec does not use limited
\* numbers of backup nodes. If a node is a master it considers all other nodes to be backups.

\* Adds mastership term 't' with master 'n' to the mastership queues for device 'd'
AddTerm(n, d, t) ==
   /\ t > terms[d]
   /\ masterships' = [masterships EXCEPT ![d] = [m \in Node |->
                         Append(masterships[d][m], [node |-> n, term |-> t])]]
   /\ terms' = [terms EXCEPT ![d] = t]
   /\ UNCHANGED <<messages, states, backups, flows>>

\* Notifies node 'n' of mastership term 't' for device 'd'
LearnTerm(n, d, t) ==
   /\ masterships' = [masterships EXCEPT ![d][n] = Pop(masterships[d][n])]
   /\ states' = [states EXCEPT ![n][d].term = t.term, ![n][d].master = t.node = n]
   /\ UNCHANGED <<messages, terms, backups, flows>>

----

(*
This section models the replication protocol. The protocol includes a simple backup mechanism
which uses logical clocks to determine when buckets need to be replicated. Additionally,
an anti-entropy protocol is used to detect out-of-date buckets on backup nodes.
*)

\* Sends a backup request for device 'd' bucket 'b' from node 'n' to node 'm' if the bucket
\* has been updated since the last backup
Backup(n, d, b, m) ==
   /\ n # m
   /\ LET bucket == flows[n][d][b]
      IN 
         /\ backups[n][d][b][m] < bucket.timestamp
         /\ SendMessage(m, [type   |-> BackupRequest,
                            did    |-> d,
                            bid    |-> b,
                            bucket |-> bucket,
                            src    |-> n])
   /\ UNCHANGED <<states, terms, masterships, backups, flows>>

\* Handles a backup request 'm' on node 'n'
\* If the bucket contained in the backup request is more up-to-date than the same bucket
\* on node 'n', node 'n's flows will be updated with the newer bucket and a successful
\* response will be sent. Otherwise, a failed response will be sent.
HandleBackupRequest(n, m) ==
   IF
      /\ states[n][m.did].term = m.term
      /\ flows[n][m.did][m.bid].term <= m.bucket.term
      /\ flows[n][m.did][m.bid].timestamp < m.bucket.timestamp
   THEN
      /\ flows' = [flows EXCEPT ![n][m.did][m.bid] = m.bucket]
      /\ SendMessage(m.src, [type      |-> BackupResponse, 
                             did       |-> m.did,
                             bid       |-> m.bid, 
                             timestamp |-> m.bucket.timestamp, 
                             succeeded |-> TRUE])
      /\ UNCHANGED <<states, terms, masterships, backups>>
   ELSE
      /\ SendMessage(m.src, [type |-> BackupResponse, succeeded |-> FALSE])
      /\ UNCHANGED <<states, terms, masterships, backups, flows>>

\* Handles a backup response 'm' on node 'n'
\* If the backup succeeded, the last backup timestamp on node 'n' is updated from the response.
\* Note the backup timestamp is sent in the response message. This is just a product of the language
\* and not an actual implementation detail.
HandleBackupResponse(n, m) == 
   IF
      /\ m.succeeded
      /\ backups[n][m.did][m.bid][m.src] < m.timestamp
   THEN
      /\ backups' = [backups EXCEPT ![n][m.did][m.bid][m.src] = m.timestamp]
      /\ UNCHANGED <<states, terms, masterships, flows>>
   ELSE
       UNCHANGED <<states, terms, masterships, backups, flows>>

\* Sends a digest request for device 'd' from node 'n' to node 'm'.
\* The digest request is part of the anti-entropy protocol which requests bucket timestamps from a
\* remote node 'm' to determine whether any flows are missing from the local node 'n'.
RequestDigests(n, d, m) ==
   /\ n # m
   /\ SendMessage(m, [type |-> DigestsRequest,
                      did  |-> d,
                      src  |-> n])
   /\ UNCHANGED <<states, terms, masterships, backups, flows>>

\* Handles a digest request 'm' on node 'n'
\* When the digest request is received, a function of buckets is returned containing the bucket digests.
\* Digests include the last term and logical time at which the bucket was updated on node 'n'.
HandleDigestsRequest(n, m) ==
   /\ LET digests == [bucket \in DOMAIN flows[n][m.did] |-> [
                         term      |-> flows[n][m.did][bucket].term,
                         timestamp |-> flows[n][m.did][bucket].timestamp]]
      IN SendMessage(m.src, [type    |-> DigestsResponse,
                             did     |-> m.did,
                             src     |-> n,
                             digests |-> digests])
   /\ UNCHANGED <<states, terms, masterships, backups, flows>>

\* Handles a digest response 'm' on node 'n'
\* Digests are tuples of the term and timestamp at which the bucket was last updated.
\* This implementation defines a function for which the domain is buckets that are more up-to-date
\* than on local node 'n' according to the digests.
HandleDigestsResponse(n, m) ==
   /\ LET buckets == {bucket \in DOMAIN flows[n][m.did] :
                        \/ flows[n][m.did][bucket].term > m.digests[bucket].term
                        \/ flows[n][m.did][bucket].timestamp > m.digests[bucket].timestamp}
      IN SendMessage(m.src, [type    |-> BucketsRequest,
                             did     |-> m.did,
                             src     |-> n,
                             buckets |-> buckets])
   /\ UNCHANGED <<states, terms, masterships, backups, flows>>

\* Handles a bucket request 'm' on node 'n'
\* This implementation differs from the real-world implementation in that it handles an arbitrary number of
\* buckets in the request and thus is not designed for scalability.
HandleBucketsRequest(n, m) ==
   /\ LET buckets == [bucket \in m.buckets |-> flows[n][m.did][bucket]]
      IN SendMessage(m.src, [type |-> BucketsResponse,
                             did |-> m.did,
                             src |-> n,
                             buckets |-> buckets])
   /\ UNCHANGED <<states, terms, masterships, backups, flows>>

\* Handles a bucket response 'm' on node 'n'
\* This implementation differs from the real-world implementation in that it handles an arbitrary number of
\* buckets in the response and thus is not designed for scalability.
HandleBucketsResponse(n, m) ==
   /\ flows' = [flows EXCEPT ![n][m.did] = [b \in 1..NumBuckets |-> 
                  IF b \in DOMAIN m.buckets THEN m.buckets[b] ELSE flows[n][m.did][b]]]
   /\ UNCHANGED <<states, terms, backups, flows>>

\* Handles a message 'm' on node 'n'
HandleMessage(n, m) ==
   /\ \/ /\ m.type = BackupRequest
         /\ HandleBackupRequest(n, m)
      \/ /\ m.type = BackupResponse
         /\ HandleBackupResponse(n, m)
      \/ /\ m.type = DigestsRequest
         /\ HandleDigestsRequest(n, m)
      \/ /\ m.type = DigestsResponse
         /\ HandleDigestsResponse(n, m)
      \/ /\ m.type = BucketsRequest
         /\ HandleBucketsRequest(n, m)
      \/ /\ m.type = BucketsResponse
         /\ HandleBucketsResponse(n, m)
   /\ ReceiveMessage(n, m)

----

vars == <<messages, states, backups, clocks, flows>>

Init ==
   /\ messages = [n \in Node |-> <<>>]
   /\ states = [n \in Node |-> [d \in Device |-> [term |-> 0, master |-> FALSE]]]
   /\ terms = [d \in Device |-> 0]
   /\ masterships = [d \in Device |-> [n \in Node |-> <<>>]]
   /\ backups = [n \in Node |-> [d \in Device |-> [b \in 1..NumBuckets |-> 0]]]
   /\ clocks = [n \in Node |-> 0]
   /\ flows = [n \in Node |-> [d \in Device |-> [b \in 1..NumBuckets |-> [term |-> 0, timestamp |-> 0, entries |-> {}]]]]

Next ==
   \/ \E n \in Node : \E f \in Flow : AddFlow(n, f)
   \/ \E n \in Node : \E f \in Flow : RemoveFlow(n, f)
   \/ \E n \in Node : \E m \in Node : \E d \in Device : \E b \in 1..NumBuckets : Backup(n, d, b, m)
   \/ \E n \in Node : \E m \in Node : \E d \in Device : RequestDigests(n, d, m)
   \/ \E n \in Node : \E d \in Device : \E t \in 1..Nat : AddTerm(n, d, t)
   \/ \E n \in Node : \E d \in Device : \E t \in masterships[d][n] : LearnTerm(n, d, t)
   \/ \E n \in Node : \E m \in messages[n] : HandleMessage(n, m)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Wed Jun 20 17:49:54 PDT 2018 by jordanhalterman
\* Created Mon Jun 18 21:52:20 PDT 2018 by jordanhalterman
