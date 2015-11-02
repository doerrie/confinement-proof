Require Import AccessGraphs.
Require Import AccessGraphsImpl.
Require Import ReferencesImpl.
Require Import AccessEdgeAppl.

(* Check that our AccessRightCapability satisfies a Capability Type *)
(* Instantiate capabilities using NatReferences and AccessRights *)

Module NatAccessGraph <: AccessGraphType NatReference NatAccessEdge := Make NatReference NatAccessEdge.
