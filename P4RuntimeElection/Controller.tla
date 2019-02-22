----------------------------- MODULE Controller -----------------------------

EXTENDS Naturals, FiniteSets, Sequences, Messages

\* The set of all ONOS nodes
CONSTANTS Nodes

\* The current state of mastership elections
VARIABLES term, master, backups

\* The current mastership event queue for each node
VARIABLE events

\* The current mastership state for each node
VARIABLE mastership

\* The unique stream ID counter used for correlating controller streams to device streams
VARIABLE streamId

\* Stream change counter used for enforcing state constraints
VARIABLE streamChanges

\* The highest term sent to the device for a node
VARIABLE sentTerm

\* Whether the node has received a MasterArbitrationUpdate indicating it is the current master
VARIABLE isMaster

\* Mastership change count used for enforcing state constraints
VARIABLE mastershipChanges

\* A count of all attempted writes to the switch
VARIABLE writeCount

----

\* Mastership/consensus related variables
mastershipVars == <<term, master, backups, mastershipChanges>>

\* Mastership arbitration variables
arbitrationVars == <<streamVars, streamId, streamChanges>>

\* Mastership event variables
eventVars == <<events, mastership>>

\* Node related variables
nodeVars == <<events, mastership, sentTerm, streamId, streamChanges, isMaster, writeCount>>

----

(*
This section models the mastership election service used by the controller to elect masters.
Mastership changes through join and leave steps. Mastership is done through a consensus
service, so these steps are atomic. When a node joins or leaves the mastership election,
events are queued to notify nodes of the mastership change. Nodes learn of mastership
changes independently of the state change in the consensus service.
*)

\* Returns the set of values in f
Range(f) == {f[x] : x \in DOMAIN f}

\* Returns a sequences with the element at the given index removed
Drop(q, i) == SubSeq(q, 1, i-1) \circ SubSeq(q, i+1, Len(q))

\* Node 'n' joins the mastership election
(*
If the current 'master' is Nil, set the master to node 'n', increment the 'term',
and send a mastership change event to each node.
If the current 'master' is non-Nil, append node 'n' to the sequence of 'backups'.
*)
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
    /\ UNCHANGED <<mastership, sentTerm, isMaster, writeCount, messageVars, arbitrationVars>>

\* Node 'n' leaves the mastership election
(*
If node 'n' is the current 'master' and a backup exists, increment the 'term',
promote the first backup to master, and send a mastership change event to each node.
If node 'n' is the current 'master' and no backups exist, set the 'master'
to Nil.
If node 'n' is in the sequence of 'backups', simply remove it.
*)
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
    /\ UNCHANGED <<mastership, sentTerm, isMaster, writeCount, messageVars, arbitrationVars>>

----

(*
This section models controller-side stream management.
*)

\* Opens a new stream on the controller side
OpenStream(n) ==
    /\ requestStream[n].state = Closed
    /\ streamId' = streamId + 1
    /\ requestStream' = [requestStream EXCEPT ![n] = [id |-> streamId', state |-> Open]]
    /\ requests' = [requests EXCEPT ![n] = <<>>]
    /\ responses' = [responses EXCEPT ![n] = <<>>]
    /\ streamChanges' = streamChanges + 1
    /\ UNCHANGED <<mastershipVars, eventVars, sentTerm, isMaster, responseStream, writeCount>>

\* Closes an open stream on the controller side
CloseStream(n) ==
    /\ requestStream[n].state = Open
    /\ requestStream' = [requestStream EXCEPT ![n].state = Closed]
    /\ sentTerm' = [sentTerm EXCEPT ![n] = 0]
    /\ isMaster' = [isMaster EXCEPT ![n] = FALSE]
    /\ streamChanges' = streamChanges + 1
    /\ UNCHANGED <<mastershipVars, eventVars, responseStream, messageVars, streamId, writeCount>>

----

(*
This section models controller-side mastership arbitration. The controller nodes
receive mastership change events from the mastership service and send master
arbitration requests to the device. Additionally, master nodes can send write
requests to the device.
*)

\* Returns master node 'n' election_id for mastership term 'm'
MasterElectionId(m) == m.term + Cardinality(Nodes)

\* Returns backup node 'n' election_id for mastership term 'm'
BackupElectionId(n, m) == m.term + Cardinality(Nodes) - CHOOSE i \in DOMAIN m.backups : m.backups[i] = n

\* Returns the mastership term for MasterArbitrationUpdate 'm'
MasterTerm(m) == m.election_id - Cardinality(Nodes)

\* Node 'n' receives a mastership change event from the mastership service
(*
When a mastership change event is received, the node's local mastership state
is updated. If the mastership term has changed, the node will set a flag to
push the mastership change to the device in the master arbitration step.
*)
LearnMastership(n) ==
    /\ Len(events[n]) > 0
    /\ LET e == events[n][1]
           m == mastership[n]
       IN
           \/ /\ e.term > m.term
              /\ mastership' = [mastership EXCEPT ![n] = [
                                     term    |-> e.term,
                                     master  |-> e.master,
                                     backups |-> e.backups]]
           \/ /\ e.term = m.term
              /\ mastership' = [mastership EXCEPT ![n] = [
                                     term    |-> e.term,
                                     master  |-> e.master,
                                     backups |-> e.backups]]
    /\ events' = [events EXCEPT ![n] = Pop(events[n])]
    /\ UNCHANGED <<mastershipVars, sentTerm, isMaster, writeCount, messageVars, arbitrationVars>>

\* Node 'n' sends a MasterArbitrationUpdate to the device
(*
If the node has an open stream to the device and a valid mastership state,
a MasterArbitrationUpdate is sent to the device. If the node is a backup, the
request's 'election_id' is set to (mastership term) + (number of nodes) - (backup index).
If the node is the master, the 'election_id' is set to (mastership term) + (number of nodes).
This is done to avoid election_ids <= 0.
Note that the actual protocol requires a (device_id, role_id, election_id) tuple, but
(device_id, role_id) have been excluded from this model as we're modelling interaction
only within a single (device_id, role_id) and thus they're irrelevant to correctness.
The mastership term is sent in MasterArbitrationUpdate requests for model checking.
*)
SendMasterArbitrationUpdate(n) ==
    /\ requestStream[n].state = Open
    /\ LET m == mastership[n]
       IN
           /\ m.term > 0
           /\ sentTerm[n] < m.term
           /\ \/ /\ m.master = n
                 /\ SendRequest(n, [
                        type        |-> MasterArbitrationUpdate,
                        election_id |-> MasterElectionId(m),
                        epoch       |-> m.term])
              \/ /\ m.master # n
                 /\ n \in Range(m.backups)
                 /\ SendRequest(n, [
                        type        |-> MasterArbitrationUpdate,
                        election_id |-> BackupElectionId(n, m),
                        epoch       |-> m.term])
           /\ sentTerm' = [sentTerm EXCEPT ![n] = m.term]
    /\ UNCHANGED <<mastershipVars, eventVars, isMaster, writeCount, arbitrationVars, responses>>

\* Node 'n' receives a MasterArbitrationUpdate from the device
(*
If the node has an open stream with a MasterArbitrationUpdate, determine whether
the local node is the master. If the MasterArbitrationUpdate 'status' is Ok, the
'election_id' matches the last requested mastership term, and 'n' is the master
for that term, update the node's state to master. Otherwise, the mastership request
is considered out of date.

Note that the separate 'isMaster' state is maintained to indicate whether the
*device* considers this node to be the current master, and this is necessary for
the safety of the algorithm. Both the node and the device must agree on the
role of the node.
*)
ReceiveMasterArbitrationUpdate(n) ==
    /\ requestStream[n].state = Open
    /\ HasResponse(n, MasterArbitrationUpdate)
    /\ LET r == NextResponse(n)
           m == mastership[n]
       IN
           \/ /\ r.status = Ok
              /\ m.master = n
              /\ m.term = MasterTerm(r)
              /\ sentTerm[n] = m.term
              /\ isMaster' = [isMaster EXCEPT ![n] = TRUE]
           \/ /\ \/ r.status # Ok
                 \/ m.master # n
                 \/ sentTerm[n] # m.term
                 \/ m.term # MasterTerm(r)
              /\ isMaster' = [isMaster EXCEPT ![n] = FALSE]
    /\ DiscardResponse(n)
    /\ UNCHANGED <<mastershipVars, eventVars, sentTerm, arbitrationVars, requests, writeCount>>

\* Master node 'n' sends a WriteRequest to the device
(*
To write to the device, the node must have an open stream, must have received a
mastership change event from the mastership service (stored in 'mastership')
indicating it is the master, and must have received a MasterArbitrationUpdate
from the switch indicating it is the master (stored in 'isMaster') for the same
term as was indicated by the mastership service.
The term is sent with the WriteRequest for model checking.
*)
SendWriteRequest(n) ==
    /\ requestStream[n].state = Open
    /\ LET m == mastership[n]
       IN
           /\ m.term > 0
           /\ m.master = n
           /\ isMaster[n]
           /\ writeCount' = writeCount + 1
           /\ SendRequest(n, [
                  type        |-> WriteRequest,
                  election_id |-> MasterElectionId(m),
                  term        |-> m.term])
    /\ UNCHANGED <<mastershipVars, eventVars, arbitrationVars, isMaster, sentTerm, responses>>

\* Node 'n' receives a write response from the device
ReceiveWriteResponse(n) ==
    /\ requestStream[n].state = Open
    /\ HasResponse(n, WriteResponse)
    /\ LET m == NextResponse(n)
       IN
           \/ m.status = Ok
           \/ m.status = PermissionDenied
    /\ DiscardResponse(n)
    /\ UNCHANGED <<mastershipVars, nodeVars, arbitrationVars, requests>>

=============================================================================
\* Modification History
\* Last modified Thu Feb 21 15:19:30 PST 2019 by jordanhalterman
\* Created Wed Feb 20 23:49:08 PST 2019 by jordanhalterman