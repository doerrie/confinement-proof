Require Import ReferencesImpl.
Require Import RefSetsAppl.
Require Import AccessEdgeAppl.
Require Import AccessGraphsAppl.
Require Import SequentialAccessAppl.
Require Import CapabilitiesAppl.
Require Import IndicesImpl.
Require Import ObjectsAppl.
Require Import SystemStateAppl.
Require Import SemanticsDefinitionsAppl.
Require Import SemanticsAppl.
Require Import ExecutionAppl.
Require Import MutationAppl.

Require Import MutableSubset.
Require Import MutableSubsetImpl.


Module NatMutableSubset <: 
  MutableSubsetType NatReference NatRefSet NatAccessEdge NatAccessGraph NatSeqAcc NatCapability NatIndex NatObject NatState NatSemDefns NatSemantics NatExecution NatMutation :=
  MakeMutableSubset NatReference NatRefSet NatAccessEdge NatAccessGraph NatSeqAcc NatCapability NatIndex NatObject NatState NatSemDefns NatSemantics NatExecution NatMutation.