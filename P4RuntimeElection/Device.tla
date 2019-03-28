------------------------------- MODULE Device -------------------------------

EXTENDS Naturals, FiniteSets, Sequences, Messages

\* Device states
CONSTANTS Running, Stopped

----

(*
The following variables are used by the device to track mastership.
*)

\* The current state of the device, either Running or Stopped
VARIABLE state

\* The election ID of the highest master
VARIABLE electionId

\* The current master node
VARIABLE currentMaster

----

(*
The following variables are used for model checking.
*)

\* A history of successful writes to the switch used for model checking
VARIABLE history

----

\* Election related variables
electionVars == <<electionId, currentMaster>>

\* Device related variables
deviceVars == <<state, history, electionVars>>

\* Device state related variables
stateVars == <<state>>

----

(*
This section models a P4 Runtime device. For the purposes of this spec, the device
has two functions: determine a master controller node and accept writes. Mastership
is determined through MasterArbitrationUpdates sent by the controller nodes. The
'election_id's provided by controller nodes are stored in 'elections', and the master
is computed as the node with the highest 'election_id' at any given time. The device
will only allow writes from the current master node.
*)

\* Shuts down the device
(*
When the device is shutdown, all the volatile device and stream variables
are set back to their initial state. The 'writeTerm' accepted by the device
is persisted through the restart.
*)
Shutdown ==
    /\ state = Running
    /\ state' = Stopped
    /\ responseStream' = [n \in DOMAIN responseStream |-> [id |-> responseStream[n].id, state |-> Closed]]
    /\ requests' = [n \in DOMAIN requests |-> <<>>]
    /\ responses' = [n \in DOMAIN responses |-> <<>>]
    /\ UNCHANGED <<requestStream, electionVars, history>>

\* Starts the device
Startup ==
    /\ state = Stopped
    /\ state' = Running
    /\ UNCHANGED <<messageVars, electionVars, history, streamVars>>

\* Connects a new stream between node 'n' and the device
(*
When a stream is connected, the 'streams' state for node 'n' is set to Open.
Stream creation is modelled as a single step to reduce the state space.
*)
ConnectStream(n) ==
    /\ state = Running
    /\ requestStream[n].state = Open
    /\ responseStream[n].id < requestStream[n].id
    /\ responseStream[n].state = Closed
    /\ responseStream' = [responseStream EXCEPT ![n].state = Open]
    /\ UNCHANGED <<deviceVars, messageVars, requestStream>>

\* Disconnects an open stream between node 'n' and the device
(*
When a stream is disconnected, the 'streams' state for node 'n' is set to Closed,
any 'election_id' provided by node 'n' is forgotten, and the 'requests'
and 'responses' queues for the node are cleared.
Additionally, if the stream belonged to the master node, a new master is
elected and a MasterArbitrationUpdate is sent on the streams that remain
in the Open state. The MasterArbitrationUpdate will be sent to the new master
with a 'status' of Ok and to all slaves with a 'status' of AlreadyExists.
*)
DisconnectStream(n) ==
    /\ state = Running
    /\ responseStream[n].state = Open
    /\ responseStream' = [responseStream EXCEPT ![n].state = Closed]
    /\ requests' = [requests EXCEPT ![n] = <<>>]
    /\ responses' = [responses EXCEPT ![n] = <<>>]
    /\ UNCHANGED <<stateVars, requestStream, electionVars, history>>

\* The device receives and responds to a MasterArbitrationUpdate from node 'n'
(*
If the 'election_id' is already present in the 'elections' and does not
already belong to node 'n', the stream is Closed and 'requests' and 'responses'
are cleared for the node.
If the 'election_id' is not known to the device, it's added to the 'elections'
state. If the change results in a new master being elected by the device,
a MasterArbitrationUpdate is sent on all Open streams. If the change does not
result in a new master being elected by the device, node 'n' is returned a
MasterArbitrationUpdate. The device master will always receive a
MasterArbitrationUpdate response with 'status' of Ok, and slaves will always
receive a 'status' of AlreadyExists.
*)
HandleMasterArbitrationUpdate(n) ==
    /\ state = Running
    /\ responseStream[n].state = Open
    /\ HasRequest(n, MasterArbitrationUpdate)
    /\ LET r == NextRequest(n)
       IN
           \/ /\ r.election_id = electionId
              /\ currentMaster # n
              /\ responseStream' = [responseStream EXCEPT ![n].state = Closed]
              /\ requests' = [requests EXCEPT ![n] = <<>>]
              /\ responses' = [responses EXCEPT ![n] = <<>>]
              /\ UNCHANGED <<deviceVars>>
           \/ /\ r.election_id > electionId
              /\ electionId' = r.election_id
              /\ currentMaster' = n
              /\ responses' = [i \in DOMAIN responseStream |->
                                  IF responseStream[i].state = Open THEN
                                      Append(responses[i], [
                                          type        |-> MasterArbitrationUpdate,
                                          status      |-> Ok,
                                          election_id |-> r.election_id])
                                  ELSE
                                      responses[i]]
              /\ UNCHANGED <<responseStream>>
           \/ /\ r.election_id < electionId
              /\ SendResponse(n, [
                     type        |-> MasterArbitrationUpdate,
                     status      |-> AlreadyExists,
                     election_id |-> electionId])
              /\ UNCHANGED <<deviceVars, responseStream>>
    /\ DiscardRequest(n)
    /\ UNCHANGED <<stateVars, requestStream, history>>

\* The device receives a WriteRequest from node 'n'
(*
The WriteRequest is accepted if:
* The 'election_id' for node 'n' matches the 'election_id' for its stream
* Node 'n' is the current master for the device
* If a 'token' is provided in the WroteRequest and the 'token' is greater than
  or equal to the last 'writeToken' accepted by the device
When the WriteRequest is accepted, the 'writeToken' is updated and the term of
the node that sent the request is recorded for model checking.
If the WriteRequest is rejeceted, a PermissionDenied response is returned.
*)
HandleWrite(n) ==
    /\ state = Running
    /\ responseStream[n].state = Open
    /\ HasRequest(n, WriteRequest)
    /\ LET r == NextRequest(n)
       IN
           \/ /\ r.election_id = electionId
              /\ currentMaster = n
              /\ history' = Append(history, [node |-> n, term |-> r.term])
              /\ SendResponse(n, [
                     type   |-> WriteResponse,
                     status |-> Ok])
           \/ /\ \/ r.election_id # electionId
                 \/ currentMaster # n
              /\ SendResponse(n, [
                     type   |-> WriteResponse,
                     status |-> PermissionDenied])
              /\ UNCHANGED <<history>>
    /\ DiscardRequest(n)
    /\ UNCHANGED <<stateVars, electionVars, streamVars>>

=============================================================================
\* Modification History
\* Last modified Wed Mar 27 17:45:48 PDT 2019 by jordanhalterman
\* Created Wed Feb 20 23:49:17 PST 2019 by jordanhalterman
