Require Import ReferencesImpl.
Require Import CapabilitiesAppl.
Require Import IndicesImpl.
Require Import ObjectsAppl.
Require Import SystemStateAppl.
Require Import SemanticsDefinitionsAppl.
Require Import RefSetsAppl.
Require Import SemanticsAppl.
Require Import ExecutionAppl.
Require Import AccessEdgeAppl.
Require Import AccessGraphsAppl.
Require Import SequentialAccessAppl.
Require Import CapSetsAppl.


Require Import Subsystem.
Require Import SubsystemImpl.

 

Module NatSubsystem <:
  SubsystemType NatReference NatRefSet NatAccessEdge NatAccessGraph NatSeqAcc NatCapability  NatCapSet NatIndex NatObject NatState NatSemDefns NatSemantics NatExecution :=
  MakeSubsystem NatReference NatRefSet NatAccessEdge NatAccessGraph NatSeqAcc NatCapability  NatCapSet NatIndex NatObject NatState NatSemDefns NatSemantics NatExecution.