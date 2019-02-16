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

\* Device/role constants used in P4 master arbitration requests
CONSTANTS DeviceId, RoleId

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

----

\* Mastership/consensus related variables
mastershipVars == <<term, master, backups>>

\* Node related variables
nodeVars       == <<events, masterships>>

\* Stream/communication related variables
streamVars     == <<streams, requests, responses>>

\* Device related variables
deviceVars     == <<elections>>

\* A sequence of all variables
vars           == <<mastershipVars, nodeVars, streamVars, deviceVars>>

----

(*
Helpers
*)

\* Returns a sequence with the head removed
Pop(q) == SubSeq(q, 2, Len(q))

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
SendRequest(n, m) == requests' = [requests EXCEPT ![n] = Append(requests[n], m)]

\* Indicates whether any requests are in the queue for node 'n'
HasRequest(n, t) == Len(requests) > 0 /\ requests[0].type = t

\* Returns the next request in the queue for node 'n'
NextRequest(n) == requests[0]

\* Discards the request at the head of the queue for node 'n'
DiscardRequest(n) == requests' = [requests EXCEPT ![n] = Pop(requests[n])]

\* Sends response 'm' on the stream for node 'n'
SendResponse(n, m) == responses' = [responses EXCEPT ![n] = Append(responses[n], m)]

\* Indicates whether any responses are in the queue for node 'n'
HasResponse(n, t) == Len(responses) > 0 /\ responses[0].type = t

\* Returns the next response in the queue for node 'n'
NextResponse(n) == responses[0]

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
    /\ \/ /\ master # Nil
          /\ n \notin Range(backups)
          /\ backups' = Append(backups, n)
          /\ UNCHANGED <<events>>
    /\ UNCHANGED <<term, master, streamVars, deviceVars>>

\* Removes a node from the mastership election
LeaveMastershipElection(n) ==
    /\ \/ /\ master = n
          /\ \/ /\ Len(backups) > 0
                /\ term' = term + 1
                /\ master' = backups[0]
                /\ backups' = Pop(backups)
                /\ events' = [i \in Nodes |-> Append(events[i], [
                                                  term |-> term',
                                                  master |-> master',
                                                  backups |-> backups'])]
             \/ /\ Len(backups) = 0
                /\ master' = Nil
                /\ UNCHANGED <<term, backups>>
       \/ /\ n \in Range(backups)
          /\ backups' = [j \in DOMAIN backups \ {CHOOSE j \in DOMAIN backups : backups[j] = n} |-> backups[j]]
          /\ UNCHANGED <<term, master>>
    /\ UNCHANGED <<streamVars, deviceVars>>

\* Changes mastership for the device in the consensus layer, adding a mastership
\* change event to each node's event queue
ChangeMastership ==
    /\ term' = term + 1
    /\ master' = backups[0]
    /\ backups' = Append(Pop(backups), master)
    /\ events' = [n \in Nodes |-> Append(events[n], [
                                      term |-> term',
                                      master |-> master',
                                      backups |-> backups'])]
    /\ UNCHANGED <<streamVars, deviceVars>>

\* Receives a mastership change event from the consensus layer on node 'n'
LearnMastership(n) ==
    /\ Len(events[n]) > 0
    /\ LET m == events[n][0]
       IN
           /\ masterships' = [masterships EXCEPT ![n] = [
                                  term    |-> m.term,
                                  master  |-> m.master,
                                  backups |-> m.backups,
                                  sent    |-> FALSE]]
    /\ UNCHANGED <<mastershipVars, streamVars, deviceVars, streams>>

\* Notifies the device of node 'n' mastership info if it hasn't already been sent
SendMasterArbitrationUpdateRequest(n) ==
    /\ masterships[n].term > 0
    /\ ~masterships[n].sent
    /\ streams[n] = Open
    /\ LET m == masterships[n]
       IN
           /\ m.term > 0
           /\ ~m.sent
           /\ \/ /\ m.master = n
                 /\ SendRequest(n, [
                        type        |-> MasterArbitrationUpdate,
                        election_id |-> m.term])
              \/ /\ m.master # n
                 /\ SendRequest(n, [
                        type        |-> MasterArbitrationUpdate,
                        election_id |-> 0])
    /\ UNCHANGED <<mastershipVars, nodeVars, deviceVars, streams>>

\* Receives a master arbitration update response on node 'n'
ReceiveMasterArbitrationUpdateResponse(n) ==
    /\ streams[n] = Open
    /\ HasResponse(n, MasterArbitrationUpdate)
    /\ LET m == NextResponse(n)
       IN
           /\ m \* TODO
    /\ DiscardResponse(n)
    /\ UNCHANGED <<deviceVars, streams>>

\* Sends a write request to the device from node 'n'
SendWriteRequest(n) ==
    /\ streams[n] = Open
    /\ LET m == masterships[n]
       IN
           /\ m.term > 0
           /\ m.master = n
           /\ SendRequest(n, [
                  type        |-> WriteRequest,
                  election_id |-> m.term])
    /\ UNCHANGED <<mastershipVars, nodeVars, deviceVars, streams>>

\* Receives a write response on node 'n'
ReceiveWriteResponse(n) ==
    /\ streams[n] = Open
    /\ HasResponse(n, WriteResponse)
    /\ LET m == NextResponse(n)
       IN
           /\ m \* TODO: Handle the write response
    /\ UNCHANGED <<mastershipVars, deviceVars, streams>>

----

(*
This section models the P4 switch.
The switch side manages stream states between the device and the controller. Streams are opened
and closed in a single state transition for the purposes of this model.
Switches can handle two types of messages from the controller nodes: MasterArbitrationUpdate and Write.
*)

\* Returns the master for the given elections
Master(e) == Max(Range(e))

\* Opens a new stream between node 'n' and the device
\* When a new stream is opened, the 'requests' and 'responses' queues for the node are
\* cleared and the 'streams' state is set to 'Open'.
ConnectStream(n) ==
    /\ streams[n] = Closed
    /\ streams' = [streams EXCEPT ![n] = Open]
    /\ requests' = [requests EXCEPT ![n] = <<>>]
    /\ responses' = [responses EXCEPT ![n] = <<>>]
    /\ UNCHANGED <<mastershipVars, nodeVars, deviceVars>>

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
              /\ responses' = [i \in DOMAIN streams' |-> Append(responses[i], [
                                                             type        |-> MasterArbitrationUpdate,
                                                             status      |-> Ok,
                                                             election_id |-> newMaster])]
           \/ /\ oldMaster = newMaster
              /\ responses' = [responses EXCEPT ![n] = <<>>]
    /\ UNCHANGED <<mastershipVars, nodeVars>>

\* Handles a master arbitration update on the device
\* If the election_id is already present in the 'elections', send an 'AlreadyExists'
\* response to the node. Otherwise, 
HandleMasterArbitrationUpdate(n) ==
    /\ streams[n] = Open
    /\ HasRequest(n, MasterArbitrationUpdate)
    /\ LET m == NextRequest(n)
       IN
           \/ /\ m.election_id \in elections
              /\ SendResponse(n, [
                     type        |-> MasterArbitrationUpdate,
                     election_id |-> m.election_id,
                     status      |-> AlreadyExists])
              /\ UNCHANGED <<deviceVars>>
           \/ /\ LET oldMaster == Master(elections)
                     newMaster == Master(elections')
                 IN
                     \/ /\ oldMaster # newMaster
                        /\ responses' = [i \in DOMAIN streams |-> Append(responses[i], [
                                                                       type        |-> MasterArbitrationUpdate,
                                                                       status      |-> Ok,
                                                                       election_id |-> newMaster])]
                     \/ /\ oldMaster = newMaster
                        /\ SendResponse(n, [
                               type        |-> MasterArbitrationUpdate,
                               status      |-> Ok,
                               election_id |-> newMaster])
    /\ DiscardRequest(n)
    /\ UNCHANGED <<mastershipVars, nodeVars, streams>>

\* Handles a write request on the device
HandleWrite(n) ==
    /\ streams[n] = Open
    /\ HasRequest(n, WriteRequest)
    /\ LET m == NextRequest(n)
       IN
           \/ /\ Cardinality(DOMAIN elections) = 0
              /\ SendResponse(n, [
                     type   |-> WriteResponse,
                     status |-> PermissionDenied])
           \/ /\ Max(Range(elections)) # m.election_id
              /\ SendResponse(n, [
                     type   |-> WriteResponse,
                     status |-> PermissionDenied])
           \/ /\ m.election_id \notin elections
              /\ elections[n] = m.election_id
              /\ SendResponse(n, [
                     type   |-> WriteResponse,
                     status |-> Ok])
    /\ UNCHANGED <<mastershipVars, nodeVars, deviceVars>>

----

Init ==
    /\ term = 0
    /\ master = Nil
    /\ backups = <<>>
    /\ masterships = [n \in DOMAIN Nodes |-> [term |-> 0, master |-> 0, backups |-> <<>>]]
    /\ streams = [n \in DOMAIN Nodes |-> Closed]
    /\ requests = [n \in DOMAIN Nodes |-> <<>>]
    /\ responses = [n \in DOMAIN Nodes |-> <<>>]
    /\ elections = [i \in DOMAIN Nodes |-> 0]

Next == 
    \/ \E n \in DOMAIN Nodes : ConnectStream(n)
    \/ \E n \in DOMAIN Nodes : CloseStream(n)
    \/ \E n \in DOMAIN Nodes : JoinMastershipElection(n)
    \/ \E n \in DOMAIN Nodes : LeaveMastershipElection(n)
    \/ \E n \in DOMAIN Nodes : LearnMastership(n)
    \/ \E n \in DOMAIN Nodes : SendMasterArbitrationUpdateRequest(n)
    \/ \E n \in DOMAIN Nodes : HandleMasterArbitrationUpdate(n)
    \/ \E n \in DOMAIN Nodes : ReceiveMasterArbitrationUpdateResponse(n)
    \/ \E n \in DOMAIN Nodes : SendWriteRequest(n)
    \/ \E n \in DOMAIN Nodes : HandleWrite(n)
    \/ \E n \in DOMAIN Nodes : ReceiveWriteResponse(n)
    \/ ChangeMastership

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Fri Feb 15 18:05:05 PST 2019 by jordanhalterman
\* Created Thu Feb 14 11:33:03 PST 2019 by jordanhalterman
