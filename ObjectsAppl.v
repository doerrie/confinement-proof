Require Import IndicesImpl.
Require Import ObjectsImpl.
Require Import Objects.
Require Import ReferencesImpl.
Require Import CapabilitiesAppl.

Module NatObject <: ObjectType NatReference NatCapability NatIndex :=
    MakeNatObj NatReference NatCapability NatIndex.

