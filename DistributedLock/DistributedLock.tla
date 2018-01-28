-------------------------- MODULE DistributedLock --------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of clients
CONSTANT Clients

\* Client states
CONSTANTS Active, Inactive

\* Message types
CONSTANT LockRequest, LockResponse, TryLockRequest, TryLockResponse, UnlockRequest, UnlockResponse

\* An empty constant
CONSTANT Nil

\* The current lock holder
VARIABLE lock

\* The lock queue
VARIABLE queue

\* The current lock ID
VARIABLE id

\* Session states
VARIABLE sessions

serverVars == <<lock, id, queue, sessions>>

\* Client states
VARIABLE clients

clientVars == <<clients>>

\* Client requests
VARIABLE requests

\* Server responses
VARIABLE responses

\* Variable to track the total number of messages sent for use in state constraints when model checking
VARIABLE messageCount

messageVars == <<requests, responses, messageCount>>

----

(*
The invariant checks that:
  * No client can hold more than one lock at a time
  * No two clients hold a lock with the same ID
  * The lock is held by an active session

Note that more than one client may believe itself to hold the lock at the same time,
e.g. if a client's session has expired but the client hasn't been notified,
but lock IDs must be unique and monotonically increasing.
*)
TypeInvariant ==
    /\ \A c \in DOMAIN clients : Cardinality(clients[c].locks) \in 0..1
    /\ \A c1, c2 \in DOMAIN clients : c1 # c2 => Cardinality(clients[c1].locks \cap clients[c2].locks) = 0
    /\ lock # Nil => sessions[lock.client].state = Active

----

\* Returns a sequence with the head removed
Pop(q) == SubSeq(q, 2, Len(q))

\* Sends a request on the given client's channel
SendRequest(m, c) ==
    /\ requests' = [requests EXCEPT ![c] = Append(requests[c], m)]
    /\ messageCount' = messageCount + 1

\* Sends a response on the given client's channel
SendResponse(m, c) ==
    /\ responses' = [requests EXCEPT ![c] = Append(responses[c], m)]
    /\ messageCount' = messageCount + 1

\* Removes a request from the given client's channel
AcceptRequest(m, c) ==
    /\ requests' = [requests EXCEPT ![c] = Pop(requests[c])]
    /\ messageCount' = messageCount + 1

\* Removes a response from the given client's channel
AcceptResponse(m, c) ==
    /\ responses' = [responses EXCEPT ![c] = Pop(responses[c])]
    /\ messageCount' = messageCount + 1

----

(****************************************************************************)
(* This section models a lock state machine. The state machine supports     *)
(* three types of request:                                                  *)
(*   * LockRequest attempts to acquire the lock. If the lock is owned by    *)
(*     another process, the request is enqueued until the lock is released. *)
(*   * TryLockRequest attempts to acquire the lock and fails if the lock    *)
(*     is already owned by another process.                                 *)
(*   * UnlockRequest attempts to release a lock that's owned by a process.  *)
(*                                                                          *)
(* Additionally, any process's session can be expired, causing any locks    *)
(* held by the session                                                      *)
(* to be released and lock requests enqueued for the session to be removed. *)
(****************************************************************************)

(*
Handles a lock request. If the lock is not currently held by another process, the lock is
granted to the client. If the lock is held by a process, the request is added to a queue.
*)
HandleLockRequest(m, c) ==
    \/ /\ sessions[c].state # Active
       /\ UNCHANGED <<clientVars, serverVars, responses>>
    \/ /\ sessions[c].state = Active
       /\ lock = Nil
       /\ lock' = m @@ ("client" :> c)
       /\ id' = id + 1
       /\ SendResponse([type |-> LockResponse, acquired |-> TRUE, id |-> id'], c)
       /\ UNCHANGED <<queue, sessions, clientVars>>
    \/ /\ sessions[c].state = Active
       /\ lock # Nil
       /\ queue' = Append(queue, m @@ ("client" :> c))
       /\ UNCHANGED <<lock, id, sessions, clientVars, responses>>

(*
Handles a tryLock request. If the lock is not currently held by another process, the lock
is granted to the client. Otherwise, the request is rejected.
*)
HandleTryLockRequest(m, c) ==
    \/ /\ sessions[c].state # Active
       /\ UNCHANGED <<clientVars, serverVars, responses>>
    \/ /\ sessions[c].state = Active
       /\ lock = Nil
       /\ lock' = m @@ ("client" :> c)
       /\ id' = id + 1
       /\ SendResponse([type |-> LockResponse, acquired |-> TRUE, id |-> id'], c)
       /\ UNCHANGED <<queue, sessions, clientVars>>
    \/ /\ sessions[c].state = Active
       /\ lock # Nil
       /\ m.timeout = 1
       /\ queue' = Append(queue, m @@ ("client" :> c))
       /\ UNCHANGED <<clientVars, lock, id, sessions, responses>>
    \/ /\ sessions[c].state = Active
       /\ lock # Nil
       /\ m.timeout = 0
       /\ SendResponse([type |-> LockResponse, acquired |-> FALSE], c)
       /\ UNCHANGED <<clientVars, serverVars>>

(*
Handles an unlock request. If the lock is currently held by the given client, it will be
unlocked. If any client's requests are pending in the queue, the next lock request will
be removed from the queue and the lock will be granted to the requesting client.
*)
HandleUnlockRequest(m, c) ==
    \/ /\ sessions[c].state # Active
       /\ UNCHANGED <<clientVars, serverVars, responses>>
    \/ /\ sessions[c].state = Active
       /\ lock = Nil
       /\ UNCHANGED <<clientVars, serverVars, responses>>
    \/ /\ sessions[c].state = Active
       /\ lock # Nil
       /\ lock.client = c
       /\ lock.id = m.id
       /\ \/ /\ Len(queue) > 0
             /\ LET next == Head(queue)
                IN
                    /\ lock' = next
                    /\ id' = id + 1
                    /\ queue' = Pop(queue)
                    /\ SendResponse([type |-> LockResponse, acquired |-> TRUE, id |-> id'], next.client)
                    /\ UNCHANGED <<sessions>>
          \/ /\ Len(queue) = 0
             /\ lock' = Nil
             /\ UNCHANGED <<queue, id, sessions, responses>>
    /\ UNCHANGED <<clientVars>>

(*
Times out a pending TryLockRequest. When the request is timed out, the request will
be removed from the queue and a response will be sent to the client notifying it of
the failure.
*)
TimeoutTryLock(c) ==
    /\ \E i \in DOMAIN queue : queue[i].client = c /\ queue[i].type = TryLockRequest
    /\ LET i == CHOOSE i \in DOMAIN queue : queue[i].client = c /\ queue[i].type = TryLockRequest condition(m) == m # queue[i]
       IN
           /\ SendResponse([type |-> LockResponse, acquired |-> FALSE], c)
           /\ queue' = SelectSeq(queue, condition)
           /\ UNCHANGED <<clientVars, lock, id, sessions, requests>>

(*
Expires a client's session. If the client currently holds the lock, the lock will be
released and the lock will be granted to another client if possible. Additionally,
pending lock requests from the client will be removed from the queue.
*)
ExpireSession(c) ==
    /\ sessions[c].state = Active
    /\ sessions' = [sessions EXCEPT ![c].state = Inactive]
    /\ LET isActive(m) == sessions'[m.client].state = Active
       IN
           IF lock # Nil /\ lock.client = c THEN
               LET q == SelectSeq(queue, isActive)
               IN
                   \/ /\ Len(q) > 0
                      /\ lock' = Head(q)
                      /\ id' = id + 1
                      /\ queue' = Pop(q)
                      /\ SendResponse([type |-> LockResponse, acquired |-> TRUE, id |-> id'], lock'.client)
                      /\ UNCHANGED <<requests>>
                   \/ /\ Len(queue) = 0
                      /\ lock' = Nil
                      /\ queue' = <<>>
                      /\ UNCHANGED <<id, messageVars>>
           ELSE
               /\ queue' = SelectSeq(queue, isActive)
               /\ UNCHANGED <<lock, id, messageVars>>
    /\ UNCHANGED <<clientVars>>

----

(***************************************************************************)
(* This section models a lock client.  A client can interact with a lock   *)
(* state machine using three types of requests:                            *)
(*   * Lock attempts to acquire a lock and blocks until successful or      *)
(*     the session expires                                                 *)
(*   * TryLock attempts to acquire a lock, failing if the lock is owned    *)
(*     by another process                                                  *)
(*   * Unlock attempts to release a lock owned by the process              *)
(*                                                                         *)
(* Additionally, a client can assume its session has expired either before *)
(* or after it actually has.  This models the possibility that a client    *)
(* believes its session has expired when it hasn't or that the state       *)
(* machine can expire a client's session without the client knowing.       *)
(***************************************************************************)

(*
Sends a lock request to the cluster with a unique ID for the client.
*)
Lock(c) ==
    /\ clients[c].state = Active
    /\ SendRequest([type |-> LockRequest, id |-> clients[c].next], c)
    /\ clients' = [clients EXCEPT ![c].next = clients[c].next + 1]
    /\ UNCHANGED <<serverVars, responses>>

(*
Sends a try lock request to the cluster with a unique ID for the client.
*)
TryLock(c) ==
    /\ clients[c].state = Active
    /\ SendRequest([type |-> TryLockRequest, id |-> clients[c].next, timeout |-> 0], c)
    /\ clients' = [clients EXCEPT ![c].next = clients[c].next + 1]
    /\ UNCHANGED <<serverVars, responses>>
(*
Sends a try lock request to the cluster with a timeout and a unique ID for the client.
*)
TryLockWithTimeout(c) ==
    /\ clients[c].state = Active
    /\ SendRequest([type |-> TryLockRequest, id |-> clients[c].next, timeout |-> 1], c)
    /\ clients' = [clients EXCEPT ![c].next = clients[c].next + 1]
    /\ UNCHANGED <<serverVars, responses>>

(*
Sends an unlock request to the cluster if the client is active and current holds a lock.
*)
Unlock(c) ==
    /\ clients[c].state = Active
    /\ Cardinality(clients[c].locks) > 0
    /\ SendRequest([type |-> UnlockRequest, id |-> CHOOSE l \in clients[c].locks : TRUE], c)
    /\ clients' = [clients EXCEPT ![c].locks = clients[c].locks \ {CHOOSE l \in clients[c].locks : TRUE}]
    /\ UNCHANGED <<serverVars, responses>>

(*
Handles a lock response from the cluster. If the client's session is expired, the response
is ignored. If the lock was acquired successfully, it's added to the client's lock set.
*)
HandleLockResponse(m, c) ==
    /\ \/ /\ clients[c].state = Inactive
          /\ UNCHANGED <<clientVars, serverVars, requests>>
       \/ /\ clients[c].state = Active
          /\ m.acquired
          /\ clients' = [clients EXCEPT ![c].locks = clients[c].locks \cup {m.id}]
          /\ UNCHANGED <<serverVars, requests>>
       \/ /\ clients[c].state = Active
          /\ ~m.acquired
          /\ UNCHANGED <<clientVars, serverVars, requests>>

(*
Closes a client's expired session. This is performed in a separate step to model the
time between the cluster expiring a session and the client being notified. A client
can close its session either before or after it's expired by the cluster. Once the
client believes its session has expired, its locks are removed, meaning a client
can also believe itself to hold a lock after its session has expired in the cluster.
*)
CloseSession(c) ==
    /\ clients[c].state = Active
    /\ clients' = [clients EXCEPT ![c].state = Inactive,
                                  ![c].locks = {}]
    /\ UNCHANGED <<serverVars, messageVars>>

----

(*
Receives a request 'm' from the client 'c' to the cluster.
*)
ReceiveRequest(m, c) ==
    /\ \/ /\ m.type = LockRequest
          /\ HandleLockRequest(m, c)
       \/ /\ m.type = TryLockRequest
          /\ HandleTryLockRequest(m, c)
       \/ /\ m.type = UnlockRequest
          /\ HandleUnlockRequest(m, c)
    /\ AcceptRequest(m, c)

(*
Receives a response 'm' from the cluster to the client 'c'.
*)
ReceiveResponse(m, c) ==
    /\ \/ /\ m.type = LockResponse
          /\ HandleLockResponse(m, c)
    /\ AcceptResponse(m, c)

----

\* Initial state predicate
Init ==
    /\ requests = [c \in Clients |-> <<>>]
    /\ responses = [c \in Clients |-> <<>>]
    /\ messageCount = 0
    /\ lock = Nil
    /\ queue = <<>>
    /\ id = 0
    /\ clients = [c \in Clients |-> [state |-> Active, locks |-> {}, next |-> 1]]
    /\ sessions = [c \in Clients |-> [state |-> Active]]

\* Next state predicate
Next ==
    \/ \E c \in DOMAIN clients : \E i \in DOMAIN requests[c] : ReceiveRequest(requests[c][i], c)
    \/ \E c \in DOMAIN clients : \E i \in DOMAIN responses[c] : ReceiveResponse(responses[c][i], c)
    \/ \E c \in DOMAIN clients : Lock(c)
    \/ \E c \in DOMAIN clients : TryLock(c)
    \/ \E c \in DOMAIN clients : TryLockWithTimeout(c)
    \/ \E c \in DOMAIN clients : Unlock(c)
    \/ \E c \in DOMAIN clients : TimeoutTryLock(c)
    \/ \E c \in DOMAIN clients : ExpireSession(c)
    \/ \E c \in DOMAIN clients : CloseSession(c)

\* The specification includes the initial state predicate and the next state
Spec == Init /\ [][Next]_<<serverVars, clientVars, messageVars>>

=============================================================================
\* Modification History
\* Last modified Sun Jan 28 14:20:59 PST 2018 by jordanhalterman
\* Created Fri Jan 26 13:12:01 PST 2018 by jordanhalterman
