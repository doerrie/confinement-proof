Require Import OrderedType.
Require Import ProjectedOrderedType.

Inductive label :=
| unborn : label
| alive : label
| dead : label.
  
Module ProjectedObjectLabel <: ProjectedToNat.

  Definition t := label.
  
  Definition project_to_nat l:=
    match l with
      | unborn => 0
      | alive => 1
      | dead => 2
    end.

  Theorem project_to_nat_unique: forall x y:t, 
    (project_to_nat x) = (project_to_nat y) <-> x = y.
  Proof.
    intros x y; split; intros H;
      unfold project_to_nat in *;
        destruct x; destruct y; auto; discriminate.
  Qed.

End ProjectedObjectLabel.

Module ObjectLabel := POT_to_OT ProjectedObjectLabel.

(* Module ObjectLabelOT : OrderedType := ObjectLabel. *)

  Require Import OrderedTypeEquiv.
  Module ObjectLabel_Equiv := OT_Equiv ObjectLabel.
  Definition ObjectLabelEQ := ObjectLabel_Equiv.Equiv.

