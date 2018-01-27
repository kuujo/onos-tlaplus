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

vars == <<serverVars, clientVars, messageVars>>

----

TypeInvariant ==
    /\ \A c \in DOMAIN clients : Cardinality(clients[c].locks) \in 0..1

----

Pop(q) == SubSeq(q, 2, Len(q))

Send(m) ==
    /\ messages' = Append(messages, m)
    /\ messageCount' = messageCount + 1

Accept(m) ==
    /\ messages' = Pop(messages)
    /\ messageCount' = messageCount + 1

Reply(m) ==
    /\ messages' = Pop(messages) \o <<m>>
    /\ messageCount' = messageCount + 1

----

HandleLockRequest(message) ==
    \/ /\ lock = Nil
       /\ lock' = message
       /\ id' = id + 1
       /\ Reply([type |-> LockResponse, client |-> message.client, acquired |-> TRUE, id |-> id])
       /\ UNCHANGED <<queue, clientVars>>
    \/ /\ lock /= Nil
       /\ queue' = Append(queue, message)
       /\ Accept(message)
       /\ UNCHANGED <<lock, id, clientVars>>

HandleTryLockRequest(message) ==
    \/ /\ lock = Nil
       /\ lock' = message
       /\ id' = id + 1
       /\ Reply([type |-> LockResponse, client |-> message.client, acquired |-> TRUE, id |-> id])
       /\ UNCHANGED <<queue, clientVars>>
    \/ /\ lock /= Nil
       /\ Reply([type |-> LockResponse, client |-> message.client, acquired |-> FALSE])
       /\ UNCHANGED <<clientVars, serverVars>>

HandleUnlockRequest(message) ==
    \/ /\ lock = Nil
       /\ Accept(message)
       /\ UNCHANGED <<clientVars, serverVars>>
    \/ /\ lock /= Nil
       /\ lock.client = message.client
       /\ lock.id = message.id
       /\ \/ /\ Len(queue) > 0
             /\ LET m == Head(queue)
                IN
                    /\ lock' = m
                    /\ id' = id + 1
                    /\ queue' = Pop(messages)
                    /\ Reply([type |-> LockResponse, client |-> message.client, acquired |-> TRUE, id |-> id])
          \/ /\ Len(queue) = 0
             /\ lock' = Nil
             /\ Accept(message)
             /\ UNCHANGED <<queue, id>>
    /\ UNCHANGED <<clientVars>>

----

IsActive(m) == clients[m.client] = Active

ExpireSession(c) ==
    /\ IF lock /= Nil /\ lock.client = c THEN
           LET q == SelectSeq(queue, IsActive)
           IN
               \/ /\ Len(q) > 0
                  /\ lock' = Head(q)
                  /\ queue' = Pop(messages)
               \/ /\ Len(queue) = 0
                  /\ lock' = Nil
                  /\ queue' = <<>>
       ELSE
           /\ queue' = SelectSeq(queue, IsActive)
           /\ UNCHANGED <<lock>>
    /\ clients' = [clients EXCEPT ![c].state = Inactive]

----

Lock(c) ==
    /\ clients[c].state = Active
    /\ Send([type |-> LockRequest, client |-> c, id |-> clients[c].next])
    /\ clients' = [clients EXCEPT ![c].next = clients[c].next + 1]
    /\ UNCHANGED <<serverVars>>

TryLock(c) ==
    /\ clients[c].state = Active
    /\ Send([type |-> TryLockRequest, client |-> c, id |-> clients[c].next])
    /\ clients' = [clients EXCEPT ![c].next = clients[c].next + 1]
    /\ UNCHANGED <<serverVars>>

Unlock(c) ==
    /\ clients[c].state = Active
    /\ Cardinality(clients[c].locks) > 0
    /\ Send([type |-> UnlockRequest, client |-> c, id |-> CHOOSE l \in clients[c].locks : TRUE])
    /\ clients' = [clients EXCEPT ![c].locks = clients[c].locks \ {CHOOSE l \in clients[c].locks : TRUE}]
    /\ UNCHANGED <<serverVars>>

HandleLockResponse(message) ==
    /\ \/ /\ message.acquired
          /\ clients' = [clients EXCEPT ![message.client].locks = clients[message.client].locks \cup {message.id}]
          /\ UNCHANGED <<serverVars>>
       \/ /\ ~message.acquired
          /\ UNCHANGED <<clientVars, serverVars>>
    /\ Accept(message)

----

Receive ==
    /\ Len(messages) > 0
    /\ LET message == Head(messages)
       IN
           \/ /\ message.type = LockRequest
              /\ HandleLockRequest(message)
           \/ /\ message.type = LockResponse
              /\ HandleLockResponse(message)
           \/ /\ message.type = TryLockRequest
              /\ HandleTryLockRequest(message)
           \/ /\ message.type = UnlockRequest
              /\ HandleUnlockRequest(message)

----

Init ==
    /\ messages = <<>>
    /\ messageCount = 0
    /\ lock = Nil
    /\ queue = <<>>
    /\ id = 1
    /\ clients = [c \in Clients |-> [state |-> Active, locks |-> {}, next |-> 1]]

Next ==
    \/ Receive
    \/ \E c \in DOMAIN clients : Lock(c)
    \/ \E c \in DOMAIN clients : TryLock(c)
    \/ \E c \in DOMAIN clients : Unlock(c)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Fri Jan 26 18:32:52 PST 2018 by jordanhalterman
\* Created Fri Jan 26 13:12:01 PST 2018 by jordanhalterman
