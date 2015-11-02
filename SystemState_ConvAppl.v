Require Import References.
Require Import ReferencesImpl.
Require Import Capabilities.
Require Import CapabilitiesAppl.
Require Import Indices.
Require Import IndicesImpl.
Require Import Objects.
Require Import ObjectsAppl.
Require Import SystemState.
Require Import SystemStateAppl.
Require Import SystemState_Conv.
Require Import SystemState_ConvImpl.


Module NatIndexNatReferenceState_Conv <: SystemStateConv NatReference NatCapability NatIndex NatObject NatState :=
  MakeSysStConv NatReference NatCapability NatIndex NatObject NatState.
