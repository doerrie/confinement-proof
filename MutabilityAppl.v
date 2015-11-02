Require Import ReferencesImpl.
Require Import AccessEdgeAppl.
Require Import AccessGraphsAppl.
Require Import RefSetsAppl.
Require Import SequentialAccessAppl.

Require Import Mutability.
Require Import MutabilityImpl.


(* Check that our AccessRightCapability satisfies a Capability Type *)
(* Instantiate capabilities using NatReferences and AccessRights *)

Module NatMutability <:
  MutabilityType NatReference NatRefSet NatAccessEdge NatAccessGraph NatSeqAcc :=
  MakeMutability NatReference NatRefSet NatAccessEdge NatAccessGraph NatSeqAcc.
