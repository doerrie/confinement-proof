Require Import OrderedType.
Require Import ProjectedOrderedType.

Inductive accessRight  :=
| wk : accessRight
| rd : accessRight
| wr : accessRight
| tx : accessRight.

Module ProjectedAccessRight <: ProjectedToNat.

  Definition t := accessRight.
  
  Definition project_to_nat r:=
    match r with
      | wk => 0
      | rd => 1
      | wr => 2
      | tx => 3
    end.

  Theorem project_to_nat_unique: forall x y:t, 
    (project_to_nat x) = (project_to_nat y) <-> x = y.
  Proof.
    intros x y; split; intros H;
      unfold project_to_nat in *;
        destruct x; destruct y; auto; discriminate.
  Qed.

End ProjectedAccessRight.

Module AccessRight := POT_to_OT ProjectedAccessRight.

(* Module AccessRightOT : OrderedType := AccessRight. *)

