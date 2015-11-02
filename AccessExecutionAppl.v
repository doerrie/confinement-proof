Require Import Semantics_ConvAppl.
Require Import ReferencesImpl.
Require Import CapabilitiesAppl.
Require Import IndicesImpl.
Require Import ObjectsAppl.
Require Import SystemStateAppl.
Require Import SemanticsDefinitionsAppl.
Require Import SemanticsAppl.
Require Import ExecutionAppl.
Require Import AccessEdgeAppl.
Require Import AccessGraphsAppl.
Require Import SequentialAccessAppl.
Require Import AccessExecutionImpl.
Require Import RefSetsAppl.

Module NatAccessExecution :=
  MakeAccessExecution NatReference NatRefSet NatAccessEdge NatAccessGraph NatSeqAcc NatCapability NatIndex NatObject NatState NatSemDefns NatSemantics NatExecution.