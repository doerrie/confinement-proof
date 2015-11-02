Require Import References.
Require Import OrderedTypeEx.

Module NatReference <: ReferenceType := Nat_as_OT.

Module NatReferenceFacts := ReferenceTypeFacts NatReference.
