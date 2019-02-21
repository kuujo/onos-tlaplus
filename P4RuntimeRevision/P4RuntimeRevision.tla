------------------------- MODULE P4RuntimeRevision -------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of all ONOS nodes
CONSTANTS Nodes

\* Stream states
CONSTANTS Open, Closed

\* Write message types
CONSTANTS WriteRequest, WriteResponse

\* Response status constants
CONSTANTS Ok, PermissionDenied

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

\* The term of the last successful write to the device
VARIABLE lastTerm

\* Counting variables used to enforce state constraints
VARIABLES mastershipChanges, streamChanges, messageCount

\* A history of successful writes to the switch used for model checking
VARIABLE history

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
deviceVars == <<lastTerm, history>>

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
This section models the messaging between controller nodes and the device.
Messaging is modelled on TCP, providing strict ordering between controller and device via
sequences. The 'requests' sequence represents the messages from controller to device for
each node, and the 'responses' sequence represents the messages from device to each node.
Requests and responses are always received from the head of the queue and are never
duplicated or reordered.
*)

\* Sends request 'm' on the stream for node 'n'
SendRequest(n, m) ==
    /\ requests' = [requests EXCEPT ![n] = Append(requests[n], m)]
    /\ messageCount' = messageCount + 1

\* Indicates whether a request of type 't' is at the head of the queue for node 'n'
HasRequest(n, t) == Len(requests[n]) > 0 /\ requests[n][1].type = t

\* Returns the next request in the queue for node 'n'
NextRequest(n) == requests[n][1]

\* Discards the request at the head of the queue for node 'n'
DiscardRequest(n) == requests' = [requests EXCEPT ![n] = Pop(requests[n])]

\* Sends response 'm' on the stream for node 'n'
SendResponse(n, m) ==
    /\ responses' = [responses EXCEPT ![n] = Append(responses[n], m)]
    /\ messageCount' = messageCount + 1

\* Indicates whether a response of type 't' is at the head of the queue for node 'n'
HasResponse(n, t) == Len(responses[n]) > 0 /\ responses[n][1].type = t

\* Returns the next response in the queue for node 'n'
NextResponse(n) == responses[n][1]

\* Discards the response at the head of the queue for node 'n'
DiscardResponse(n) == responses' = [responses EXCEPT ![n] = Pop(responses[n])]

\* Indicates whether the stream for node 'n' is Open
IsStreamOpen(n) == streams[n].state = Open

\* Indicates whether the stream for node 'n' is Closed
IsStreamClosed(n) == streams[n].state = Closed

----

(*
This section models the mastership election service used by the controller to elect masters.
Mastership changes through join and leave steps. Mastership is done through a consensus
service, so these steps are atomic. When a node joins or leaves the mastership election,
events are queued to notify nodes of the mastership change. Nodes learn of mastership
changes independently of the state change in the consensus service.
*)


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
    /\ UNCHANGED <<masterships, streamVars, messageVars, deviceVars>>

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
    /\ UNCHANGED <<masterships, streamVars, messageVars, deviceVars>>

----

(*
This section models controller-side mastership arbitration. The controller nodes
receive mastership change events from the mastership service and send master
arbitration requests to the device. Additionally, master nodes can send write
requests to the device.
*)

\* Node 'n' receives a mastership change event from the mastership service
(*
When a mastership change event is received, the node's local mastership state
is updated. If the mastership term has changed, the node will set a flag to
push the mastership change to the device in the master arbitration step.
*)
LearnMastership(n) ==
    /\ Len(events[n]) > 0
    /\ LET e == events[n][1]
           m == masterships[n]
       IN
           \/ /\ e.term > m.term
              /\ masterships' = [masterships EXCEPT ![n] = [
                                     term    |-> e.term,
                                     master  |-> e.master,
                                     backups |-> e.backups]]
           \/ /\ e.term = m.term
              /\ masterships' = [masterships EXCEPT ![n] = [
                                     term    |-> e.term,
                                     master  |-> e.master,
                                     backups |-> e.backups]]
    /\ events' = [events EXCEPT ![n] = Pop(events[n])]
    /\ UNCHANGED <<mastershipVars, streamVars, messageVars, deviceVars>>

\* Master node 'n' sends a WriteRequest to the device
(*
To write to the device, the node must have an open stream, must have received a
mastership change event from the mastership service (stored in 'masterships')
indicating it is the master, and must have received a MasterArbitrationUpdate
from the switch indicating it is the master (stored in 'isMaster') for the same
term as was indicated by the mastership service.
The term is sent with the WriteRequest for model checking.
*)
SendWriteRequest(n) ==
    /\ IsStreamOpen(n)
    /\ LET m == masterships[n]
       IN
           /\ m.term > 0
           /\ m.master = n
           /\ SendRequest(n, [
                  type        |-> WriteRequest,
                  term        |-> m.term])
    /\ UNCHANGED <<mastershipVars, nodeVars, deviceVars, streamVars, responses>>

\* Node 'n' receives a write response from the device
ReceiveWriteResponse(n) ==
    /\ IsStreamOpen(n)
    /\ HasResponse(n, WriteResponse)
    /\ LET m == NextResponse(n)
       IN
           \/ m.status = Ok
           \/ m.status = PermissionDenied
    /\ DiscardResponse(n)
    /\ UNCHANGED <<mastershipVars, nodeVars, deviceVars, streamVars, requests, messageCount>>

----

(*
This section models a P4 Runtime device. In this spec, the device's only
role is to accept writes from controller nodes. Mastership order is
maintained using a simple fencing token stored in 'lastTerm'. The device
ensures only new masters can write to it by rejecting writes from older
masters according to their provided term.
*)

\* Opens a new stream between node 'n' and the device
(*
When a stream is opened, the 'streams' state for node 'n' is set to Open.
Stream creation is modelled as a single step to reduce the state space.
*)
ConnectStream(n) ==
    /\ IsStreamClosed(n)
    /\ streams' = [streams EXCEPT ![n].state = Open]
    /\ streamChanges' = streamChanges + 1
    /\ UNCHANGED <<mastershipVars, nodeVars, deviceVars, messageVars>>

\* Closes an open stream between node 'n' and the device
(*
When a stream is closed, the 'streams' state for node 'n' is set to Closed,
and the 'requests' and 'responses' queues for the node are cleared.
*)
CloseStream(n) ==
    /\ IsStreamOpen(n)
    /\ streams' = [streams EXCEPT ![n] = [state |-> Closed, term |-> 0]]
    /\ requests' = [requests EXCEPT ![n] = <<>>]
    /\ responses' = [responses EXCEPT ![n] = <<>>]
    /\ streamChanges' = streamChanges + 1
    /\ UNCHANGED <<mastershipVars, nodeVars, deviceVars, messageCount>>

\* The device receives a WriteRequest from node 'n'
(*
If the WriteRequest 'term' is greater than or equal to the highest term received
by the device, the write is accepted, the highest term is updated, and the write
is recorded in history for model checking. Otherwise, the write was sent by an old
master and is rejected with a PermissionDenied error.
*)
HandleWrite(n) ==
    /\ IsStreamOpen(n)
    /\ HasRequest(n, WriteRequest)
    /\ LET m == NextRequest(n)
       IN
           \/ /\ lastTerm <= m.term
              /\ lastTerm' = m.term
              /\ history' = Append(history, [node |-> n, term |-> m.term])
              /\ SendResponse(n, [
                     type   |-> WriteResponse,
                     status |-> Ok])
           \/ /\ lastTerm > m.term
              /\ SendResponse(n, [
                     type   |-> WriteResponse,
                     status |-> PermissionDenied])
              /\ UNCHANGED <<lastTerm, history>>
    /\ DiscardRequest(n)
    /\ UNCHANGED <<mastershipVars, nodeVars, streamVars>>

----

(*
The invariant asserts that the device will not allow a write from an older master
if it has already accepted a write from a newer master. This is determined by
comparing the mastership terms of accepted writes. For this invariant to hold,
terms may only increase in the history of writes.
*)
TypeInvariant ==
    /\ \A x \in 1..Len(history) :
           \A y \in x..Len(history) :
               history[x].term <= history[y].term
    /\ \A x \in 1..Len(history) :
           \A y \in x..Len(history) :
               history[x].term = history[y].term => history[x].node = history[y].node

----

Init ==
    /\ term = 0
    /\ master = Nil
    /\ backups = <<>>
    /\ events = [n \in Nodes |-> <<>>]
    /\ masterships = [n \in Nodes |-> [term |-> 0, master |-> Nil, backups |-> <<>>]]
    /\ streams = [n \in Nodes |-> [state |-> Closed, term |-> 0]]
    /\ requests = [n \in Nodes |-> <<>>]
    /\ responses = [n \in Nodes |-> <<>>]
    /\ lastTerm = 0
    /\ mastershipChanges = 0
    /\ streamChanges = 0
    /\ messageCount = 0
    /\ history = <<>>

Next == 
    \/ \E n \in Nodes : ConnectStream(n)
    \/ \E n \in Nodes : CloseStream(n)
    \/ \E n \in Nodes : JoinMastershipElection(n)
    \/ \E n \in Nodes : LeaveMastershipElection(n)
    \/ \E n \in Nodes : LearnMastership(n)
    \/ \E n \in Nodes : SendWriteRequest(n)
    \/ \E n \in Nodes : HandleWrite(n)
    \/ \E n \in Nodes : ReceiveWriteResponse(n)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Wed Feb 20 16:09:21 PST 2019 by jordanhalterman
\* Created Thu Feb 14 11:33:03 PST 2019 by jordanhalterman
