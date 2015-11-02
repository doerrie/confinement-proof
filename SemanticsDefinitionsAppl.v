Require Import SemanticsDefinitions.
Require Import SemanticsDefinitionsImpl.
Require Import SystemState_ConvAppl.
Require Import ReferencesImpl.
Require Import CapabilitiesAppl.
Require Import IndicesImpl.
Require Import ObjectsAppl.
Require Import SystemStateAppl.


Module NatSemDefns <: SemanticsDefinitionsType NatReference NatCapability NatIndex NatObject NatState :=
  MakeSemanticsDefns NatReference NatCapability NatIndex NatObject NatState.