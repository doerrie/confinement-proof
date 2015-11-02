Require Import Semantics.
Require Import SemanticsImpl.
Require Import SystemState_ConvAppl.
Require Import ReferencesImpl.
Require Import CapabilitiesAppl.
Require Import IndicesImpl.
Require Import ObjectsAppl.
Require Import SystemStateAppl.
Require Import SemanticsDefinitionsAppl.
Require Import RefSetsAppl.
Require Import SemanticsDefinitions.


Module NatSemantics <: 
  SemanticsType NatReference NatRefSet NatCapability NatIndex NatObject NatState NatSemDefns:=
  SimpleSemantics NatReference NatRefSet NatCapability NatIndex NatObject NatState NatSemDefns.