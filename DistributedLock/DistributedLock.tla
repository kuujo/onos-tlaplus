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

serverVars == <<lock, id, queue>>

\* Client states
VARIABLE clients

clientVars == <<clients>>

\* Client messages
VARIABLE messages

\* Variable 
VARIABLE messageCount

messageVars == <<messages, messageCount>>

----

\* The invariant checks that no client can hold more than one lock at a time
TypeInvariant ==
    /\ \A c \in DOMAIN clients : Cardinality(clients[c].locks) \in 0..1

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
    \/ /\ lock = Nil
       /\ lock' = m @@ ("client" :> c)
       /\ id' = id + 1
       /\ Reply([type |-> LockResponse, acquired |-> TRUE, id |-> id'], c)
       /\ UNCHANGED <<queue, clientVars>>
    \/ /\ lock /= Nil
       /\ queue' = Append(queue, m @@ ("client" :> c))
       /\ Accept(m, c)
       /\ UNCHANGED <<lock, id, clientVars>>
(*
Handles a tryLock request. If the lock is not currently help by another process, the lock
is granted to the client. Otherwise, the request is rejected.
*)
HandleTryLockRequest(m, c) ==
    \/ /\ lock = Nil
       /\ lock' = m @@ ("client" :> c)
       /\ id' = id + 1
       /\ Reply([type |-> LockResponse, acquired |-> TRUE, id |-> id'], c)
       /\ UNCHANGED <<queue, clientVars>>
    \/ /\ lock /= Nil
       /\ Reply([type |-> LockResponse, acquired |-> FALSE], c)
       /\ UNCHANGED <<clientVars, serverVars>>

(*
Handles an unlock request. If the lock is currently held by the given client, it will be
unlocked. If any client's requests are pending in the queue, the next lock request will
be removed from the queue and the lock will be granted to the requesting client.
*)
HandleUnlockRequest(m, c) ==
    \/ /\ lock = Nil
       /\ Accept(m, c)
       /\ UNCHANGED <<clientVars, serverVars>>
    \/ /\ lock /= Nil
       /\ lock.client = c
       /\ lock.id = m.id
       /\ \/ /\ Len(queue) > 0
             /\ LET next == Head(queue)
                IN
                    /\ lock' = next
                    /\ id' = id + 1
                    /\ queue' = Pop(queue)
                    /\ Reply([type |-> LockResponse, acquired |-> TRUE, id |-> id'], c)
          \/ /\ Len(queue) = 0
             /\ lock' = Nil
             /\ Accept(m, c)
             /\ UNCHANGED <<queue, id>>
    /\ UNCHANGED <<clientVars>>

----

\* Returns whether the client associated with the given message is active
IsActive(m) == clients[m.client].state = Active

(*
Expires a client's session. If the client currently holds the lock, the lock will be
released and the lock will be granted to another client if possible. Additionally,
pending lock requests from the client will be removed from the queue, and the client's
state will be updated to remove any locks.
*)
ExpireSession(c) ==
    /\ clients[c].state = Active
    /\ IF lock /= Nil /\ lock.client = c THEN
           LET q == SelectSeq(queue, IsActive)
           IN
               \/ /\ Len(q) > 0
                  /\ lock' = Head(q) @@ ("client" :> c)
                  /\ id' = id + 1
                  /\ queue' = Pop(q)
                  /\ Send([type |-> LockResponse, acquired |-> TRUE, id |-> id'], lock'.client)
               \/ /\ Len(queue) = 0
                  /\ lock' = Nil
                  /\ queue' = <<>>
                  /\ UNCHANGED <<id, messageVars>>
       ELSE
           /\ queue' = SelectSeq(queue, IsActive)
           /\ UNCHANGED <<lock, id, messageVars>>
    /\ clients' = [clients EXCEPT ![c].state = Inactive,
                                  ![c].locks = {}]

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

\* Next state predicate
Next ==
    \/ \E c \in DOMAIN clients : Receive(c)
    \/ \E c \in DOMAIN clients : Lock(c)
    \/ \E c \in DOMAIN clients : TryLock(c)
    \/ \E c \in DOMAIN clients : Unlock(c)
    \/ \E c \in DOMAIN clients : ExpireSession(c)

\* The specification includes the initial state predicate and the next state
Spec == Init /\ [][Next]_<<serverVars, clientVars, messageVars>>

=============================================================================
\* Modification History
\* Last modified Sat Jan 27 01:50:12 PST 2018 by jordanhalterman
\* Created Fri Jan 26 13:12:01 PST 2018 by jordanhalterman
