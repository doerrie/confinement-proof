Require Import Objects_ConvImpl.
Require Import ObjectsAppl.
Require Import Objects_Conv.
Require Import ReferencesImpl.
Require Import IndicesImpl.
Require Import CapabilitiesAppl.

Module NatObject_Conv <: ObjectConv NatReference NatCapability NatIndex NatObject :=
    MakeObjConv NatReference NatCapability NatIndex NatObject.

