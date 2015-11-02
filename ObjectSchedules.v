Require Import OrderedType.
Require Import ProjectedOrderedType.

Inductive obSched :=
| running : obSched
| blocked : obSched.

Module ProjectedObjectSchedule <: ProjectedToNat.
  
  Definition t := obSched.

  Definition project_to_nat l:=
    match l with
      | running => 0
      | blocked => 1
    end.

  Theorem project_to_nat_unique: forall x y:t, 
    (project_to_nat x) = (project_to_nat y) <-> x = y.
  Proof.
    intros x y; split; intros H;
      unfold project_to_nat in *;
        destruct x; destruct y; auto; discriminate.
  Qed.

End ProjectedObjectSchedule.

Module ObjectSchedule := POT_to_OT ProjectedObjectSchedule.

(* Module ObjectScheduleOT : OrderedType := ObjectSchedule. *)

  Require Import OrderedTypeEquiv.
  Module ObjectSchedule_Equiv := OT_Equiv ObjectSchedule.
  Definition ObjectScheduleEQ := ObjectSchedule_Equiv.Equiv.


