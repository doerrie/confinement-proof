Require Import Decidable.
Require Import References.
Require Import AccessRights.
Require Import OrderedTypeEx.
Require AccessEdge.
Require FSets.


(* Sequential Access is the notion of how to directly relate one access graph to another. *)

Module AccessTrans (RT : ReferenceType).

  Module R := RT.

  Definition access (mayWeak mayRead mayWrite maySend : R.t -> R.t -> Prop) := Prop.

End SequentialAccess.
