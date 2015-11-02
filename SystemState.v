(* We structurally define what it means to be a system state. *)

(* intuitively, a system state is a mapping of References to Objects *)
Require Import ObjectLabels.
Require Import ObjectTypes.
Require Import ObjectSchedules.
Require Import FMapInterface2.
Require Import OrderedTypeEx.
Require Import References.
Require Import Capabilities.
Require Import Indices.
Require Import Objects.

(* the new tuples are really going to change things around a bit for Semantics
   and other proofs.  I may want to abstract over all of this a bit. *)

(* also, we may want to migrate many of the proofs from Semantics 
   and DirectAccess to this file and others so that we can simplify those 
   libraries *)

Module Type SystemStateType (Ref: ReferenceType) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind).

  Declare Module MapS : Sfun Ref.
  Module P3 := PairOrderedType Obj ObjectLabel.
  Module P2 := PairOrderedType P3 ObjectType.
  Module P := PairOrderedType P2 ObjectSchedule.

    Include (Sord_fun Ref MapS P).
    
    Parameter eq_dec : forall x y, { eq x y } + { ~ eq x y }.
    
End SystemStateType.

