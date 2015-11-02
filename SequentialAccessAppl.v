Require Import SequentialAccess.
Require Import SequentialAccessImpl.
Require Import ReferencesImpl.
Require Import AccessEdgeAppl.
Require Import RefSetsAppl.
Require Import AccessGraphsAppl.

(* Check that our AccessRightCapability satisfies a Capability Type *)
(* Instantiate capabilities using NatReferences and AccessRights *)

Module NatSeqAcc <: SeqAccType NatReference NatRefSet NatAccessEdge NatAccessGraph := MakeSeqAcc NatReference NatRefSet NatAccessEdge NatAccessGraph.
