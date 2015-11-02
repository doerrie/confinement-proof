Require Import SystemState.
Require Import Objects.
Require Import ObjectsAppl.
Require Import Capabilities.
Require Import CapabilitiesAppl.
Require Import References.
Require Import ReferencesImpl.
Require Import Indices.
Require Import IndicesImpl.
Require Import SystemStateImpl.
Require Import ObjectsAppl.

Module NatState <: SystemStateType NatReference NatCapability NatIndex NatObject :=
    MakePairSystemState NatReference NatCapability NatIndex NatObject.