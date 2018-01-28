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

\* Client messages
VARIABLE messages

\* Variable to track the total number of messages sent for use in state constraints when model checking
VARIABLE messageCount

messageVars == <<messages, messageCount>>

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

\* Sends a message on the given client's channel
Send(m, c) ==
    /\ messages' = [messages EXCEPT ![c] = Append(messages[c], m)]
    /\ messageCount' = messageCount + 1

\* Removes a message from the given client's channel
Accept(m, c) ==
    /\ messages' = [messages EXCEPT ![c] = Pop(messages[c])]
    /\ messageCount' = messageCount + 1

\* Removes the last message and appends a message to the given client's channel
Reply(m, c) ==
    /\ messages' = [messages EXCEPT ![c] = Append(Pop(messages[c]), m)]
    /\ messageCount' = messageCount + 1

----

(*
Handles a lock request. If the lock is not currently held by another process, the lock is
granted to the client. If the lock is held by a process, the request is added to a queue.
*)
HandleLockRequest(m, c) ==
    \/ /\ sessions[c].state # Active
       /\ Accept(m, c)
       /\ UNCHANGED <<clientVars, serverVars>>
    \/ /\ sessions[c].state = Active
       /\ lock = Nil
       /\ lock' = m @@ ("client" :> c)
       /\ id' = id + 1
       /\ Reply([type |-> LockResponse, acquired |-> TRUE, id |-> id'], c)
       /\ UNCHANGED <<queue, sessions, clientVars>>
    \/ /\ sessions[c].state = Active
       /\ lock # Nil
       /\ queue' = Append(queue, m @@ ("client" :> c))
       /\ Accept(m, c)
       /\ UNCHANGED <<lock, id, sessions, clientVars>>
(*
Handles a tryLock request. If the lock is not currently held by another process, the lock
is granted to the client. Otherwise, the request is rejected.
*)
HandleTryLockRequest(m, c) ==
    \/ /\ sessions[c].state # Active
       /\ Accept(m, c)
       /\ UNCHANGED <<clientVars, serverVars>>
    \/ /\ sessions[c].state = Active
       /\ lock = Nil
       /\ lock' = m @@ ("client" :> c)
       /\ id' = id + 1
       /\ Reply([type |-> LockResponse, acquired |-> TRUE, id |-> id'], c)
       /\ UNCHANGED <<queue, sessions, clientVars>>
    \/ /\ sessions[c].state = Active
       /\ lock # Nil
       /\ Reply([type |-> LockResponse, acquired |-> FALSE], c)
       /\ UNCHANGED <<clientVars, serverVars>>

(*
Handles an unlock request. If the lock is currently held by the given client, it will be
unlocked. If any client's requests are pending in the queue, the next lock request will
be removed from the queue and the lock will be granted to the requesting client.
*)
HandleUnlockRequest(m, c) ==
    \/ /\ sessions[c].state # Active
       /\ Accept(m, c)
       /\ UNCHANGED <<clientVars, serverVars>>
    \/ /\ sessions[c].state = Active
       /\ lock = Nil
       /\ Accept(m, c)
       /\ UNCHANGED <<clientVars, serverVars>>
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
                    /\ Reply([type |-> LockResponse, acquired |-> TRUE, id |-> id'], next.client)
                    /\ UNCHANGED <<sessions>>
          \/ /\ Len(queue) = 0
             /\ lock' = Nil
             /\ Accept(m, c)
             /\ UNCHANGED <<queue, id, sessions>>
    /\ UNCHANGED <<clientVars>>

----

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
                      /\ Send([type |-> LockResponse, acquired |-> TRUE, id |-> id'], lock'.client)
                   \/ /\ Len(queue) = 0
                      /\ lock' = Nil
                      /\ queue' = <<>>
                      /\ UNCHANGED <<id, messageVars>>
           ELSE
               /\ queue' = SelectSeq(queue, isActive)
               /\ UNCHANGED <<lock, id, messageVars>>
    /\ UNCHANGED <<clientVars>>

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
Sends a lock request to the cluster with a unique ID for the client.
*)
Lock(c) ==
    /\ clients[c].state = Active
    /\ Send([type |-> LockRequest, id |-> clients[c].next], c)
    /\ clients' = [clients EXCEPT ![c].next = clients[c].next + 1]
    /\ UNCHANGED <<serverVars>>

(*
Sends a try lock request to the cluster with a unique ID for the client.
*)
TryLock(c) ==
    /\ clients[c].state = Active
    /\ Send([type |-> TryLockRequest, id |-> clients[c].next], c)
    /\ clients' = [clients EXCEPT ![c].next = clients[c].next + 1]
    /\ UNCHANGED <<serverVars>>

(*
Sends an unlock request to the cluster if the client is active and current holds a lock.
*)
Unlock(c) ==
    /\ clients[c].state = Active
    /\ Cardinality(clients[c].locks) > 0
    /\ Send([type |-> UnlockRequest, id |-> CHOOSE l \in clients[c].locks : TRUE], c)
    /\ clients' = [clients EXCEPT ![c].locks = clients[c].locks \ {CHOOSE l \in clients[c].locks : TRUE}]
    /\ UNCHANGED <<serverVars>>

(*
Handles a lock response from the cluster. If the client's session is expired, the response
is ignored. If the lock was acquired successfully, it's added to the client's lock set.
*)
HandleLockResponse(m, c) ==
    /\ \/ /\ clients[c].state = Inactive
          /\ UNCHANGED <<clientVars, serverVars>>
       \/ /\ clients[c].state = Active
          /\ m.acquired
          /\ clients' = [clients EXCEPT ![c].locks = clients[c].locks \cup {m.id}]
          /\ UNCHANGED <<serverVars>>
       \/ /\ clients[c].state = Active
          /\ ~m.acquired
          /\ UNCHANGED <<clientVars, serverVars>>
    /\ Accept(m, c)

----

(*
Receives a message from/to the given client from the head of the client's message queue.
*)
Receive(c) ==
    /\ Len(messages[c]) > 0
    /\ LET message == Head(messages[c])
       IN
           \/ /\ message.type = LockRequest
              /\ HandleLockRequest(message, c)
           \/ /\ message.type = LockResponse
              /\ HandleLockResponse(message, c)
           \/ /\ message.type = TryLockRequest
              /\ HandleTryLockRequest(message, c)
           \/ /\ message.type = UnlockRequest
              /\ HandleUnlockRequest(message, c)

----

\* Initial state predicate
Init ==
    /\ messages = [c \in Clients |-> <<>>]
    /\ messageCount = 0
    /\ lock = Nil
    /\ queue = <<>>
    /\ id = 0
    /\ clients = [c \in Clients |-> [state |-> Active, locks |-> {}, next |-> 1]]
    /\ sessions = [c \in Clients |-> [state |-> Active]]

\* Next state predicate
Next ==
    \/ \E c \in DOMAIN clients : Receive(c)
    \/ \E c \in DOMAIN clients : Lock(c)
    \/ \E c \in DOMAIN clients : TryLock(c)
    \/ \E c \in DOMAIN clients : Unlock(c)
    \/ \E c \in DOMAIN clients : ExpireSession(c)
    \/ \E c \in DOMAIN clients : CloseSession(c)

\* The specification includes the initial state predicate and the next state
Spec == Init /\ [][Next]_<<serverVars, clientVars, messageVars>>

=============================================================================
\* Modification History
\* Last modified Sun Jan 28 10:10:23 PST 2018 by jordanhalterman
\* Created Fri Jan 26 13:12:01 PST 2018 by jordanhalterman
