------------------------- MODULE P4RuntimeElection -------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of all ONOS nodes
CONSTANTS Nodes

\* Stream states
CONSTANTS Open, Closed

\* Master arbitration message types
CONSTANTS MasterArbitrationUpdate

\* Write message types
CONSTANTS WriteRequest, WriteResponse

\* Response status constants
CONSTANTS Ok, AlreadyExists, PermissionDenied

\* Empty value
CONSTANT Nil

\* The current state of mastership elections
VARIABLES term, master, backups

\* The current mastership event queue for each node
VARIABLE events

\* The current mastership state for each node
VARIABLE masterships

\* The state of all streams and their requests and responses
VARIABLE streams, requests, responses

\* The current set of elections for the switch, the greatest of which is the current master
VARIABLE elections

\* Counting variables used to enforce state constraints
VARIABLES mastershipChanges, streamChanges, messageCount

\* A sequence of successful writes to the switch used for model checking
VARIABLE writes

----

\* Mastership/consensus related variables
mastershipVars == <<term, master, backups, mastershipChanges>>

\* Node related variables
nodeVars == <<events, masterships>>

\* Stream related variables
streamVars == <<streams, streamChanges>>

\* Message related variables
messageVars == <<requests, responses, messageCount>>

\* Device related variables
deviceVars == <<elections, writes>>

\* A sequence of all variables
vars == <<mastershipVars, nodeVars, streamVars, messageVars, deviceVars>>

----

(*
Helpers
*)

\* Returns a sequence with the head removed
Pop(q) == SubSeq(q, 2, Len(q))

\* Returns a sequences with the element at the given index removed
Drop(q, i) == SubSeq(q, 1, i-1) \circ SubSeq(q, i+1, Len(q))

\* Returns the set of values in f
Range(f) == {f[x] : x \in DOMAIN f}

\* Returns the maximum value from a set or undefined if the set is empty
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----

(*
Messaging between the Nodes and the device are modelled on TCP. For each node, a request
and response sequence provides ordered messaging between the two points. Requests and
responses are always received from the head of the queue and are never duplicated or reordered,
and request and response queues only last the lifetime of the stream. When a stream is closed,
all that stream's requests and responses are lost.
*)

\* Sends request 'm' on the stream for node 'n'
SendRequest(n, m) ==
    /\ requests' = [requests EXCEPT ![n] = Append(requests[n], m)]
    /\ messageCount' = messageCount + 1

\* Indicates whether any requests are in the queue for node 'n'
HasRequest(n, t) == Len(requests[n]) > 0 /\ requests[n][1].type = t

\* Returns the next request in the queue for node 'n'
NextRequest(n) == requests[n][1]

\* Discards the request at the head of the queue for node 'n'
DiscardRequest(n) == requests' = [requests EXCEPT ![n] = Pop(requests[n])]

\* Sends response 'm' on the stream for node 'n'
SendResponse(n, m) ==
    /\ responses' = [responses EXCEPT ![n] = Append(responses[n], m)]
    /\ messageCount' = messageCount + 1

\* Indicates whether any responses are in the queue for node 'n'
HasResponse(n, t) == Len(responses[n]) > 0 /\ responses[n][1].type = t

\* Returns the next response in the queue for node 'n'
NextResponse(n) == responses[n][1]

\* Discards the response at the head of the queue for node 'n'
DiscardResponse(n) == responses' = [responses EXCEPT ![n] = Pop(responses[n])]

----

(*
This section models mastership arbitration on the controller side.
Mastership election occurs in two disctinct types of state changes. One state change occurs
to change the mastership in the consensus layer, and the other occurs when a node actually
learns of the mastership change. Nodes will always learn of mastership changes in the order
in which they occur, and nodes will always learn of a mastership change. This, of course,
is not representative of practice but is sufficient for modelling the mastership election
algorithm.
*)

\* Adds a node to the mastership election
JoinMastershipElection(n) ==
    /\ \/ /\ master = Nil
          /\ term' = term + 1
          /\ master' = n
          /\ backups' = <<>>
          /\ events' = [i \in Nodes |-> Append(events[i], [
                                            term |-> term',
                                            master |-> master',
                                            backups |-> backups'])]
       \/ /\ master # Nil
          /\ master # n
          /\ n \notin Range(backups)
          /\ backups' = Append(backups, n)
          /\ events' = [i \in Nodes |-> Append(events[i], [
                                            term |-> term,
                                            master |-> master,
                                            backups |-> backups'])]
          /\ UNCHANGED <<term, master>>
    /\ mastershipChanges' = mastershipChanges + 1
    /\ UNCHANGED <<masterships, streamVars, messageVars, deviceVars>>

\* Removes a node from the mastership election
LeaveMastershipElection(n) ==
    /\ \/ /\ master = n
          /\ \/ /\ Len(backups) > 0
                /\ term' = term + 1
                /\ master' = backups[1]
                /\ backups' = Pop(backups)
                /\ events' = [i \in Nodes |-> Append(events[i], [
                                                  term |-> term',
                                                  master |-> master',
                                                  backups |-> backups'])]
             \/ /\ Len(backups) = 0
                /\ master' = Nil
                /\ UNCHANGED <<term, backups, events>>
       \/ /\ n \in Range(backups)
          /\ backups' = Drop(backups, CHOOSE j \in DOMAIN backups : backups[j] = n)
          /\ UNCHANGED <<term, master, events>>
    /\ mastershipChanges' = mastershipChanges + 1
    /\ UNCHANGED <<masterships, streamVars, messageVars, deviceVars>>

\* Sets the current master to node 'n' if it's not already set
SetMastership(n) ==
    \/ /\ master = n
       /\ UNCHANGED <<mastershipVars>>
    \/ /\ master # n
       /\ term' = term + 1
       /\ master' = n
       /\ \/ /\ n \in Range(backups)
             /\ backups' = Drop(backups, CHOOSE j \in DOMAIN backups : backups[j] = n)
          \/ /\ n \notin Range(backups)
             /\ UNCHANGED <<backups>>
       /\ mastershipChanges' = mastershipChanges + 1

\* Receives a mastership change event from the consensus layer on node 'n'
LearnMastership(n) ==
    /\ Len(events[n]) > 0
    /\ LET e == events[n][1]
           m == masterships[n]
       IN
           \/ /\ e.term > m.term
              /\ masterships' = [masterships EXCEPT ![n] = [
                                     term    |-> e.term,
                                     master  |-> e.master,
                                     backups |-> e.backups,
                                     sent    |-> FALSE]]
           \/ /\ e.term = m.term
              /\ masterships' = [masterships EXCEPT ![n] = [
                                     term    |-> e.term,
                                     master  |-> e.master,
                                     backups |-> e.backups,
                                     sent    |-> m.sent]]
    /\ events' = [events EXCEPT ![n] = Pop(events[n])]
    /\ UNCHANGED <<mastershipVars, streamVars, messageVars, deviceVars>>

\* Notifies the device of node 'n' mastership info if it hasn't already been sent
SendMasterArbitrationUpdateRequest(n) ==
    /\ streams[n] = Open
    /\ LET m == masterships[n]
       IN
           /\ m.term > 0
           /\ ~m.sent
           /\ \/ /\ m.master = n
                 /\ SendRequest(n, [
                        type        |-> MasterArbitrationUpdate,
                        election_id |-> m.term + Cardinality(Nodes),
                        term        |-> m.term])
              \/ /\ m.master # n
                 /\ n \in Range(m.backups)
                 /\ SendRequest(n, [
                        type        |-> MasterArbitrationUpdate,
                        election_id |-> m.term + Cardinality(Nodes) - CHOOSE i \in DOMAIN m.backups : m.backups[i] = n,
                        term        |-> m.term])
    /\ masterships' = [masterships EXCEPT ![n].sent = TRUE]
    /\ UNCHANGED <<mastershipVars, events, deviceVars, streamVars, responses>>

\* Receives a master arbitration update response on node 'n'
ReceiveMasterArbitrationUpdateResponse(n) ==
    /\ streams[n] = Open
    /\ HasResponse(n, MasterArbitrationUpdate)
    /\ LET m == NextResponse(n)
       IN
           \/ /\ m.status = Ok
              /\ SetMastership(n)
           \/ /\ m.status = AlreadyExists
              /\ UNCHANGED <<mastershipVars>>
    /\ DiscardResponse(n)
    /\ UNCHANGED <<nodeVars, deviceVars, streamVars, requests, messageCount>>

\* Sends a write request to the device from node 'n'
SendWriteRequest(n) ==
    /\ streams[n] = Open
    /\ LET m == masterships[n]
       IN
           /\ m.term > 0
           /\ m.master = n
           /\ SendRequest(n, [
                  type        |-> WriteRequest,
                  election_id |-> m.term + Cardinality(Nodes),
                  term        |-> m.term])
    /\ UNCHANGED <<mastershipVars, nodeVars, deviceVars, streamVars, responses>>

\* Receives a write response on node 'n'
ReceiveWriteResponse(n) ==
    /\ streams[n] = Open
    /\ HasResponse(n, WriteResponse)
    /\ LET m == NextResponse(n)
       IN
           \* TODO: This should be used to determine whether writes from old masters are allowed
           \/ m.status = Ok
           \/ m.status = PermissionDenied
    /\ DiscardResponse(n)
    /\ UNCHANGED <<mastershipVars, nodeVars, deviceVars, streamVars, requests, messageCount>>

----

(*
This section models the P4 switch.
The switch side manages stream states between the device and the controller. Streams are opened
and closed in a single state transition for the purposes of this model.
Switches can handle two types of messages from the controller nodes: MasterArbitrationUpdate and Write.
*)

\* Returns the highest election ID for the given elections
ElectionId(e) == Max(Range(e))

\* Returns the master for the given elections
Master(e) == 
    IF Cardinality({i \in Range(e) : i > 0}) > 0 THEN
        CHOOSE n \in DOMAIN e : e[n] = ElectionId(e)
    ELSE
        Nil

\* Opens a new stream between node 'n' and the device
\* When a new stream is opened, the 'requests' and 'responses' queues for the node are
\* cleared and the 'streams' state is set to 'Open'.
ConnectStream(n) ==
    /\ streams[n] = Closed
    /\ streams' = [streams EXCEPT ![n] = Open]
    /\ requests' = [requests EXCEPT ![n] = <<>>]
    /\ responses' = [responses EXCEPT ![n] = <<>>]
    /\ streamChanges' = streamChanges + 1
    /\ UNCHANGED <<mastershipVars, nodeVars, deviceVars, messageCount>>

\* Closes the open stream between node 'n' and the device
\* When the stream is closed, the 'requests' and 'responses' queues for the node are
\* cleared and a 'MasterArbitrationUpdate' is sent to all remaining connected nodes
\* to notify them of a mastership change if necessary.
CloseStream(n) ==
    /\ streams[n] = Open
    /\ elections' = [elections EXCEPT ![n] = 0]
    /\ streams' = [streams EXCEPT ![n] = Closed]
    /\ requests' = [requests EXCEPT ![n] = <<>>]
    /\ LET oldMaster == Master(elections)
           newMaster == Master(elections')
       IN
           \/ /\ oldMaster # newMaster
              /\ responses' = [i \in DOMAIN streams' |->
                                  IF i = newMaster THEN
                                      Append(responses[i], [
                                          type        |-> MasterArbitrationUpdate,
                                          status      |-> Ok,
                                          election_id |-> ElectionId(elections')])
                                  ELSE
                                      Append(responses[i], [
                                          type        |-> MasterArbitrationUpdate,
                                          status      |-> AlreadyExists,
                                          election_id |-> ElectionId(elections')])]
              /\ messageCount' = messageCount + 1
           \/ /\ oldMaster = newMaster
              /\ responses' = [responses EXCEPT ![n] = <<>>]
              /\ UNCHANGED <<messageCount>>
    /\ streamChanges' = streamChanges + 1
    /\ UNCHANGED <<mastershipVars, nodeVars, writes>>

\* Handles a master arbitration update on the device
\* If the election_id is already present in the 'elections', send an 'AlreadyExists'
\* response to the node. Otherwise, 
HandleMasterArbitrationUpdate(n) ==
    /\ streams[n] = Open
    /\ HasRequest(n, MasterArbitrationUpdate)
    /\ LET m == NextRequest(n)
       IN
           \/ /\ m.election_id \in Range(elections)
              /\ SendResponse(n, [
                     type        |-> MasterArbitrationUpdate,
                     election_id |-> m.election_id,
                     status      |-> AlreadyExists])
              /\ UNCHANGED <<deviceVars>>
           \/ /\ m.election_id \notin Range(elections)
              /\ elections' = [elections EXCEPT ![n] = m.election_id]
              /\ LET oldMaster == Master(elections)
                     newMaster == Master(elections')
                 IN
                     \/ /\ oldMaster # newMaster
                        /\ responses' = [i \in DOMAIN streams |->
                                            IF i = newMaster THEN
                                                Append(responses[i], [
                                                    type        |-> MasterArbitrationUpdate,
                                                    status      |-> Ok,
                                                    election_id |-> ElectionId(elections')])
                                            ELSE
                                                Append(responses[i], [
                                                    type        |-> MasterArbitrationUpdate,
                                                    status      |-> AlreadyExists,
                                                    election_id |-> ElectionId(elections')])]
                        /\ messageCount' = messageCount + 1
                     \/ /\ oldMaster = newMaster
                        /\ SendResponse(n, [
                               type        |-> MasterArbitrationUpdate,
                               status      |-> Ok,
                               election_id |-> ElectionId(elections')])
    /\ DiscardRequest(n)
    /\ UNCHANGED <<mastershipVars, nodeVars, streamVars, writes>>

\* Handles a write request on the device
HandleWrite(n) ==
    /\ streams[n] = Open
    /\ HasRequest(n, WriteRequest)
    /\ LET m == NextRequest(n)
       IN
           \/ /\ Master(elections) # n
              /\ SendResponse(n, [
                     type   |-> WriteResponse,
                     status |-> PermissionDenied])
              /\ UNCHANGED <<writes>>
           \/ /\ Master(elections) = n
              /\ writes' = Append(writes, [node |-> n, term |-> m.term])
              /\ SendResponse(n, [
                     type   |-> WriteResponse,
                     status |-> Ok])
    /\ DiscardRequest(n)
    /\ UNCHANGED <<mastershipVars, nodeVars, elections, streamVars>>

----

\* The invariant asserts that no master can write to the switch after the switch
\* has been notified of a newer master
TypeInvariant == \A i \in DOMAIN writes : i = 1 \/ writes[i-1].term <= writes[i].term

----

Init ==
    /\ term = 0
    /\ master = Nil
    /\ backups = <<>>
    /\ events = [n \in Nodes |-> <<>>]
    /\ masterships = [n \in Nodes |-> [term |-> 0, master |-> 0, backups |-> <<>>, sent |-> FALSE]]
    /\ streams = [n \in Nodes |-> Closed]
    /\ requests = [n \in Nodes |-> <<>>]
    /\ responses = [n \in Nodes |-> <<>>]
    /\ elections = [n \in Nodes |-> 0]
    /\ mastershipChanges = 0
    /\ streamChanges = 0
    /\ messageCount = 0
    /\ writes = <<>>

Next == 
    \/ \E n \in Nodes : ConnectStream(n)
    \/ \E n \in Nodes : CloseStream(n)
    \/ \E n \in Nodes : JoinMastershipElection(n)
    \/ \E n \in Nodes : LeaveMastershipElection(n)
    \/ \E n \in Nodes : LearnMastership(n)
    \/ \E n \in Nodes : SendMasterArbitrationUpdateRequest(n)
    \/ \E n \in Nodes : HandleMasterArbitrationUpdate(n)
    \/ \E n \in Nodes : ReceiveMasterArbitrationUpdateResponse(n)
    \/ \E n \in Nodes : SendWriteRequest(n)
    \/ \E n \in Nodes : HandleWrite(n)
    \/ \E n \in Nodes : ReceiveWriteResponse(n)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sun Feb 17 01:26:56 PST 2019 by jordanhalterman
\* Created Thu Feb 14 11:33:03 PST 2019 by jordanhalterman
