Require Import OrderedType.
Require Import ProjectedOrderedType.

Inductive obType :=
| active : obType
| passive : obType.

Module ProjectedObjectType <: ProjectedToNat.

  Definition t := obType.

  Definition project_to_nat l:=
    match l with
      | active => 0
      | passive => 1
    end.

  Theorem project_to_nat_unique: forall x y:t, 
    (project_to_nat x) = (project_to_nat y) <-> x = y.
  Proof.
    intros x y; split; intros H;
      unfold project_to_nat in *;
        destruct x; destruct y; auto; discriminate.
  Qed.

End ProjectedObjectType.

Module ObjectType := POT_to_OT ProjectedObjectType.

(* Module ObjectTypeOT : OrderedType := ObjectType. *)

  Require Import OrderedTypeEquiv.
  Module ObjectType_Equiv := OT_Equiv ObjectType.
  Definition ObjectTypeEQ := ObjectType_Equiv.Equiv.


