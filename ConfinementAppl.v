Require Import ReferencesImpl.
Require Import RefSetsAppl.
Require Import AccessEdgeAppl.
Require Import AccessGraphsAppl.
Require Import SequentialAccessAppl.
Require Import CapabilitiesAppl.
Require Import CapSetsAppl.
Require Import IndicesImpl.
Require Import ObjectsAppl.
Require Import SystemStateAppl.
Require Import SemanticsDefinitionsAppl.
Require Import SemanticsAppl.
Require Import ExecutionAppl.
Require Import MutationAppl.
Require Import SubsystemAppl.

Require Import Confinement.
Require Import ConfinementImpl.


Module NatConfinement <: ConfinementType NatReference NatRefSet NatAccessEdge NatAccessGraph NatSeqAcc NatCapability NatCapSet NatIndex NatObject NatState NatSemDefns NatSemantics NatExecution NatMutation NatSubsystem :=
  MakeConfinement NatReference NatRefSet NatAccessEdge NatAccessGraph NatSeqAcc NatCapability NatCapSet NatIndex NatObject NatState NatSemDefns NatSemantics NatExecution NatMutation NatSubsystem.