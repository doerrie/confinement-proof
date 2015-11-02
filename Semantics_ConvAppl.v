Require Import Semantics_ConvImpl.
Require Import SemanticsAppl.
Require Import ReferencesImpl.
Require Import RefSetsAppl.
Require Import CapabilitiesAppl.
Require Import IndicesImpl.
Require Import ObjectsAppl.
Require Import SystemStateAppl.
Require Import SemanticsDefinitionsAppl.
Require Import SemanticsAppl.
Require Import Semantics_Conv.

Module NatSemanticsConv <:
  SemanticsConv NatReference NatRefSet NatCapability NatIndex NatObject NatState NatSemDefns NatSemantics := 
  MakeSemanticsConv NatReference NatRefSet NatCapability NatIndex NatObject NatState NatSemDefns NatSemantics.