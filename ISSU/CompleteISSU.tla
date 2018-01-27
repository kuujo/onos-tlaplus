------------------------------ MODULE CompleteISSU ------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of all nodes
CONSTANT Nodes

\* The set of all devices
CONSTANT Devices

\* A sequence of all versions
CONSTANT Versions

\* The size of a partition and total number of partitions
CONSTANTS PartitionSize, NumPartitions

\* Upgrade states
CONSTANTS Inactive, Initialized, Upgraded, Committed, RolledBack, Reset

\* An empty value
CONSTANT Nil

\* The current state of the upgrade
VARIABLE upgradeState

\* The current upgrade version
VARIABLE upgradeVersion

\* The set of node states
VARIABLE nodes

\* The set of device states
VARIABLE devices

\* The number of versions must be greater than 1
ASSUME Len(Versions) > 1

\* The number of nodes must be greater than 1
ASSUME Cardinality(Nodes) > 1

\* The partition size is a number
ASSUME PartitionSize \in Nat /\ PartitionSize =< Cardinality(Nodes)

----

\* The current version domain
CurrentVersion(v) == CHOOSE i \in DOMAIN Versions : Versions[i] = v

\* Predicate indicating whether the version can be incremented
CanUpgrade(v) == CurrentVersion(v) < Len(Versions)

\* The next version
NextVersion(v) == Versions[CurrentVersion(v) + 1]

\* The previous version
PreviousVersion(v) == Versions[CurrentVersion(v) - 1]

\* Return the minimum value from a set
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Whether the node has been upgraded
IsUpgraded(n) ==
    /\ nodes[n].version - 1 \in DOMAIN Versions
    /\ Cardinality({i \in Nodes : nodes[i].version = PreviousVersion(nodes[n].version)}) > 0

\* Whether other nodes have been upgraded
NotUpgraded(n) ==
    /\ nodes[n].version + 1 \in DOMAIN Versions
    /\ Cardinality({i \in Nodes : nodes[i].version = NextVersion(nodes[n].version)}) > 0

----

(*
The type invariant asserts that:
 * The total number of versions in the cluster at any given time is <= 2
 * All devices have a master in the current version
*)
TypeInvariant ==
    /\ Cardinality({nodes[n].version : n \in Nodes}) \in {1, 2}
    /\ \A d \in Devices :
           LET master == devices[d].master
           IN master = Nil \/ nodes[master].version = upgradeVersion
    /\ \A n \in Nodes :
           LET active == nodes[n].active
           IN \A p \in DOMAIN active :
               IF IsUpgraded(n) THEN
                   Cardinality(active[p]) = Min({Cardinality({i \in Nodes : nodes[i].version = nodes[n].version}), PartitionSize})
               ELSE
                   Cardinality(active[p]) = PartitionSize

----

\* Selects a master node for a device with the given version
ChooseMaster(v, ns) == 
    LET choices == {n \in ns : nodes[n].version = v}
    IN IF Cardinality(choices) = 0 THEN Nil ELSE CHOOSE n \in choices : TRUE

\* Run the command to initialize an upgrade
RunInitialize ==
    /\ upgradeState = Inactive
    /\ \A n \in Nodes : nodes[n].version = upgradeVersion
    /\ upgradeState' = Initialized
    /\ UNCHANGED <<upgradeVersion, nodes, devices>>

\* Run the command to perform an upgrade
RunUpgrade ==
    /\ upgradeState = Initialized
    /\ CanUpgrade(upgradeVersion)
    /\ Cardinality({n \in Nodes : nodes[n].version = NextVersion(upgradeVersion)}) > 0
    /\ upgradeState' = Upgraded
    /\ upgradeVersion' = NextVersion(upgradeVersion)
    /\ devices' = [d \in Devices |-> [master |-> ChooseMaster(NextVersion(upgradeVersion), Nodes)]]
    /\ UNCHANGED <<nodes>>

\* Run the command to rollback an upgrade
RunRollback ==
    /\ upgradeState = Upgraded
    /\ Cardinality({n \in Nodes : nodes[n].version = PreviousVersion(upgradeVersion)}) > 0
    /\ upgradeState' = RolledBack
    /\ upgradeVersion' = PreviousVersion(upgradeVersion)
    /\ devices' = [d \in Devices |-> [master |-> ChooseMaster(PreviousVersion(upgradeVersion), Nodes)]]
    /\ UNCHANGED <<nodes>>

\* Run the command to commit a version change
RunCommit ==
    /\ upgradeState = Upgraded
    /\ \A n \in Nodes : nodes[n].version = upgradeVersion
    /\ upgradeState' = Inactive
    /\ UNCHANGED <<upgradeVersion, nodes, devices>>

\* Run the command to reset ISSU
RunReset ==
    /\ upgradeState = RolledBack
    /\ \A n \in Nodes : nodes[n].version = upgradeVersion
    /\ upgradeState' = Inactive
    /\ UNCHANGED <<upgradeVersion, nodes, devices>>

----

\* Helper predicate indicating whether an upgrade can be rolled back during a node state change
CanRollback ==
    /\ upgradeState = Upgraded
    /\ Cardinality({n \in Nodes : nodes[n].version = PreviousVersion(upgradeVersion)}) > 0

\* Helper to roll back an upgrade during a node state change
RollbackUpgrade ==
    /\ upgradeState' = RolledBack
    /\ upgradeVersion' = PreviousVersion(upgradeVersion)
    /\ devices' = [d \in Devices |-> [master |-> ChooseMaster(PreviousVersion(upgradeVersion), Nodes)]]

\* Helper to rebalance masters after a node state change
RebalanceMasters(except) ==
    /\ devices' = [d \in Devices |-> [master |-> ChooseMaster(upgradeVersion, Nodes \ except)]]
    /\ UNCHANGED <<upgradeState, upgradeVersion>>

\* Helper to determine whether no nodes are in the given version
IsFirstNode(version) ==
    /\ Cardinality({n \in Nodes : nodes[n].version = version}) = 0

----

\* Upgrade a node in a single atomic step
UpgradeNode(n) ==
    /\ \/ /\ upgradeState = Initialized
          /\ nodes[n].version = upgradeVersion
       \/ /\ upgradeState = Upgraded
          /\ nodes[n].version = PreviousVersion(upgradeVersion)
    /\ CanUpgrade(nodes[n].version)
    /\ RebalanceMasters(IF upgradeState = Upgraded THEN {} ELSE {n})
    /\ IF IsFirstNode(NextVersion(nodes[n].version)) THEN
           nodes' = [nodes EXCEPT ![n].version = NextVersion(nodes[n].version),
                                  ![n].inactive = nodes[n].active,
                                  ![n].active = [i \in 1..NumPartitions |-> {n}]]
       ELSE
           LET active == nodes[CHOOSE x \in Nodes : nodes[x].version = NextVersion(nodes[n].version)].active
           IN nodes' = [nodes EXCEPT ![n].version = NextVersion(nodes[n].version),
                                     ![n].inactive = nodes[n].active,
                                     ![n].active = [i \in 1..NumPartitions |-> IF Cardinality(active[i]) < PartitionSize THEN active[i] \cup {n} ELSE active[i]]]
    /\ UNCHANGED <<upgradeState, upgradeVersion>>

\* Downgrade a node in a single atomic step
DowngradeNode(n) ==
    /\ upgradeState = RolledBack
    /\ nodes[n].version = NextVersion(upgradeVersion)
    /\ RebalanceMasters({})
    /\ nodes' = [nodes EXCEPT ![n].version = PreviousVersion(nodes[n].version),
                              ![n].inactive = [i \in 1..NumPartitions |-> {}],
                              ![n].active = nodes[n].inactive]
    /\ UNCHANGED <<upgradeState, upgradeVersion>>

\* Crash a node in a single atomic step
CrashNode(n) ==
    /\ \/ /\ CanRollback
          /\ RollbackUpgrade
       \/ /\ ~CanRollback
    /\ RebalanceMasters({n})
    /\ UNCHANGED <<nodes>>

----

\* Initial state predicate
Init ==
    /\ upgradeState = Inactive
    /\ upgradeVersion = Head(Versions)
    /\ nodes = [n \in Nodes |-> [
           version |-> Head(Versions),
           inactive |-> [i \in 1..NumPartitions |-> {}],
           active |-> [i \in 1..NumPartitions |-> CHOOSE x \in SUBSET(Nodes) : Cardinality(x) = PartitionSize]]]
    /\ devices = [d \in Devices |-> [master |-> ChooseMaster(upgradeVersion, Nodes)]]

\* Next state predicate
Next ==
    \/ RunInitialize
    \/ RunUpgrade
    \/ RunCommit
    \/ RunRollback
    \/ RunReset
    \/ \E n \in Nodes :
        \/ UpgradeNode(n)
        \/ DowngradeNode(n)
        \/ CrashNode(n)

=============================================================================
\* Modification History
\* Last modified Fri Jan 26 12:57:30 PST 2018 by jordanhalterman
\* Created Mon Jan 22 23:16:53 PST 2018 by jordanhalterman
