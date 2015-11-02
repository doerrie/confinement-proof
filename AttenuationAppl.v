Require Import Semantics_ConvAppl.
Require Import ReferencesImpl.
Require Import CapabilitiesAppl.
Require Import IndicesImpl.
Require Import ObjectsAppl.
Require Import SystemStateAppl.
Require Import SemanticsDefinitionsAppl.
Require Import SemanticsAppl.
Require Import AccessEdgeAppl.
Require Import AccessGraphsAppl.
Require Import SequentialAccessAppl.
Require Import DirectTrans.
Require Import RefSetsAppl.

Module NatAttenuation :=
  MakeAttenuation NatReference NatRefSet NatAccessEdge NatAccessGraph NatSeqAcc NatCapability NatIndex NatObject NatState NatSemDefns NatSemantics.