Require Import AccessEdge.
Require Import AccessEdgeImpl.
Require Import ReferencesImpl.

(* Check that our AccessRightCapability satisfies a Capability Type *)
(* Instantiate capabilities using NatReferences and AccessRights *)

Module NatAccessEdge <: AccessEdgeType NatReference := Make NatReference.
