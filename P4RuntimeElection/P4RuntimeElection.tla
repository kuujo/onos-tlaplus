------------------------- MODULE P4RuntimeElection -------------------------

EXTENDS Naturals, Sequences, Controller, Device

\* A sequence of all variables
vars == <<mastershipVars, nodeVars, messageVars, streamVars, deviceVars>>

(*
The invariant asserts that the device will not allow a write from an older master
if it has already accepted a write from a newer master. This is determined by
comparing the mastership terms of accepted writes. For this invariant to hold,
terms may only increase in the history of writes.
*)
TypeInvariant ==
    /\ \A x \in 1..Len(history) :
           \A y \in x..Len(history) :
               /\ history[x].term <= history[y].term
               /\ history[x].term = history[y].term => history[x].node = history[y].node

Init ==
    /\ term = 0
    /\ master = Nil
    /\ backups = <<>>
    /\ events = [n \in Nodes |-> <<>>]
    /\ mastership = [n \in Nodes |-> [term |-> 0, master |-> Nil, backups |-> <<>>]]
    /\ streamId = 0
    /\ sentTerm = [n \in Nodes |-> 0]
    /\ isMaster = [n \in Nodes |-> FALSE]
    /\ requestStream = [n \in Nodes |-> [id |-> 0, state |-> Closed]]
    /\ requests = [n \in Nodes |-> <<>>]
    /\ responseStream = [n \in Nodes |-> [id |-> 0, state |-> Closed]]
    /\ responses = [n \in Nodes |-> <<>>]
    /\ election = [n \in Nodes |-> 0]
    /\ writeToken = 0
    /\ state = Stopped
    /\ history = <<>>

Next == 
    \/ \E n \in Nodes : OpenStream(n)
       /\ UNCHANGED <<deviceVars>>
    \/ \E n \in Nodes : CloseStream(n)
       /\ UNCHANGED <<deviceVars>>
    \/ \E n \in Nodes : ConnectStream(n)
       /\ UNCHANGED <<mastershipVars, nodeVars>>
    \/ \E n \in Nodes : DisconnectStream(n)
       /\ UNCHANGED <<mastershipVars, nodeVars>>
    \/ \E n \in Nodes : JoinMastershipElection(n)
       /\ UNCHANGED <<deviceVars>>
    \/ \E n \in Nodes : LeaveMastershipElection(n)
       /\ UNCHANGED <<deviceVars>>
    \/ \E n \in Nodes : LearnMastership(n)
       /\ UNCHANGED <<deviceVars>>
    \/ \E n \in Nodes : SendMasterArbitrationUpdate(n)
       /\ UNCHANGED <<deviceVars>>
    \/ \E n \in Nodes : HandleMasterArbitrationUpdate(n)
       /\ UNCHANGED <<mastershipVars, nodeVars>>
    \/ \E n \in Nodes : ReceiveMasterArbitrationUpdate(n)
       /\ UNCHANGED <<deviceVars>>
    \/ \E n \in Nodes : SendWriteRequest(n)
       /\ UNCHANGED <<deviceVars>>
    \/ \E n \in Nodes : HandleWrite(n)
       /\ UNCHANGED <<mastershipVars, nodeVars>>
    \/ \E n \in Nodes : ReceiveWriteResponse(n)
       /\ UNCHANGED <<deviceVars>>
    \/ Shutdown
       /\ UNCHANGED <<mastershipVars, nodeVars>>
    \/ Startup
       /\ UNCHANGED <<mastershipVars, nodeVars>>

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Mon Feb 25 16:25:03 PST 2019 by jordanhalterman
\* Created Thu Feb 14 11:33:03 PST 2019 by jordanhalterman
