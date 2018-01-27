------------------------------ MODULE ISSU ------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of all nodes
CONSTANT Nodes

\* A sequence of all versions
CONSTANT Versions

\* Node states
CONSTANT Started, Stopped

\* Upgrade states
CONSTANTS Inactive, Initialized, Upgraded, Committed, RolledBack, Reset

\* The current state of the upgrade
VARIABLE upgradeState

\* The current upgrade version
VARIABLE upgradeVersion

\* The set of node states
VARIABLE nodes

\* The number of versions must be greater than 1
ASSUME Len(Versions) > 1

\* The number of nodes must be greater than 1
ASSUME Cardinality(Nodes) > 1

----

\* The current version domain
CurrentVersion(v) == CHOOSE i \in DOMAIN Versions : Versions[i] = v

\* The next version
NextVersion(v) == Versions[CurrentVersion(v) + 1]

\* The previous version
PreviousVersion(v) == Versions[CurrentVersion(v) - 1]

\* Predicate indicating whether the version can be incremented
CanUpgrade(v) ==
    /\ CurrentVersion(v) < Len(Versions)

\* Helper predicate indicating whether an upgrade can be rolled back during a node state change
CanRollback ==
    /\ upgradeState = Upgraded
    /\ Cardinality({n \in Nodes : nodes[n].version = PreviousVersion(upgradeVersion)}) > 0

----

(*
Checks that there's never more than two versions running in the cluster at a given time
and that only one version may be running if the upgrade is Inactive.
*)
TypeInvariant ==
    /\ \/ /\ upgradeState = Inactive
          /\ Cardinality({nodes[n].version : n \in Nodes}) = 1
       \/ /\ upgradeState /= Inactive
          /\ Cardinality({nodes[n].version : n \in Nodes}) \in 1..2

----

\* Run the command to initialize an upgrade
RunInitialize ==
    /\ upgradeState = Inactive
    /\ \A n \in Nodes : nodes[n].version = upgradeVersion
    /\ upgradeState' = Initialized
    /\ UNCHANGED <<upgradeVersion, nodes>>

\* Run the command to perform an upgrade
RunUpgrade ==
    /\ upgradeState = Initialized
    /\ CanUpgrade(upgradeVersion)
    /\ Cardinality({n \in Nodes : nodes[n].version = NextVersion(upgradeVersion)}) > 0
    /\ upgradeState' = Upgraded
    /\ upgradeVersion' = NextVersion(upgradeVersion)
    /\ UNCHANGED <<nodes>>

\* Run the command to rollback an upgrade
RunRollback ==
    /\ upgradeState = Upgraded
    /\ Cardinality({n \in Nodes : nodes[n].version = PreviousVersion(upgradeVersion)}) > 0
    /\ upgradeState' = RolledBack
    /\ upgradeVersion' = PreviousVersion(upgradeVersion)
    /\ UNCHANGED <<nodes>>

\* Run the command to commit a version change
RunCommit ==
    /\ upgradeState = Upgraded
    /\ \A n \in Nodes : nodes[n].version = upgradeVersion
    /\ upgradeState' = Inactive
    /\ UNCHANGED <<upgradeVersion, nodes>>

\* Run the command to reset ISSU
RunReset ==
    /\ upgradeState = RolledBack
    /\ \A n \in Nodes : nodes[n].version = upgradeVersion
    /\ upgradeState' = Inactive
    /\ UNCHANGED <<upgradeVersion, nodes>>

----

\* Start a node
StartNode(n) ==
    /\ nodes[n].state = Stopped
    /\ nodes' = [nodes EXCEPT ![n].state = Started]
    /\ UNCHANGED <<upgradeState, upgradeVersion>>

\* Stop a node
StopNode(n) ==
    /\ nodes[n].state = Started
    /\ nodes' = [nodes EXCEPT ![n].state = Stopped]
    /\ UNCHANGED <<upgradeState, upgradeVersion>>

\* Upgrade a node
UpgradeNode(n) ==
    /\ \/ /\ upgradeState = Initialized
          /\ nodes[n].state = Stopped
          /\ nodes[n].version = upgradeVersion
       \/ /\ upgradeState = Upgraded
          /\ nodes[n].version = PreviousVersion(upgradeVersion)
    /\ CanUpgrade(nodes[n].version)
    /\ nodes' = [nodes EXCEPT ![n].version = NextVersion(nodes[n].version)]
    /\ UNCHANGED <<upgradeState, upgradeVersion>>

\* Downgrade a node
DowngradeNode(n) ==
    /\ upgradeState = RolledBack
    /\ nodes[n].state = Stopped
    /\ nodes[n].version = NextVersion(upgradeVersion)
    /\ nodes' = [nodes EXCEPT ![n].version = PreviousVersion(nodes[n].version)]
    /\ UNCHANGED <<upgradeState, upgradeVersion>>

\* Crash a node in a single atomic step
CrashNode(n) ==
    /\ \/ /\ CanRollback
          /\ upgradeState' = RolledBack
          /\ upgradeVersion' = PreviousVersion(upgradeVersion)
       \/ /\ ~CanRollback
          /\ UNCHANGED <<upgradeState, upgradeVersion>>
    /\ UNCHANGED <<nodes>>

----

\* Initial state predicate
Init ==
    /\ upgradeState = Inactive
    /\ upgradeVersion = Head(Versions)
    /\ nodes = [n \in Nodes |-> [state |-> Started, version |-> Head(Versions)]]

\* Next state predicate
Next ==
    \/ RunInitialize
    \/ RunUpgrade
    \/ RunCommit
    \/ RunRollback
    \/ RunReset
    \/ \E n \in Nodes :
        \/ StopNode(n)
        \/ StartNode(n)
        \/ UpgradeNode(n)
        \/ DowngradeNode(n)
        \/ CrashNode(n)

=============================================================================
\* Modification History
\* Last modified Fri Jan 26 13:10:09 PST 2018 by jordanhalterman
\* Created Mon Jan 22 23:16:53 PST 2018 by jordanhalterman
