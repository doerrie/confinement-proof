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
Require Import DirectAccessImpl.
Require Import RefSetsAppl.
Require Semantics_ConvAppl.


Module SimpleDirectAccess := 
  MakeDirectAccess NatReference NatRefSet NatCapability NatIndex NatObject NatState NatSemDefns NatSemantics NatExecution NatAccessEdge NatAccessGraph NatSeqAcc.