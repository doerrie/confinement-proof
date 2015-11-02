Require Import OrderedType.

Module Type ProjectedToNat.

  Parameter t : Type.

  Parameter project_to_nat: t -> nat.

  Parameter project_to_nat_unique: forall x y:t, 
    (project_to_nat x) = (project_to_nat y) <-> x = y. 

End ProjectedToNat.

Module MiniProjectedOrderedType (P:ProjectedToNat) <: MiniOrderedType.

  Include P.

  Definition eq := @eq t.
  Definition lt l r:= lt (project_to_nat l) (project_to_nat r).

  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_equal t.
  Definition eq_trans := @trans_equal t.

  Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros.
    unfold lt in *.
    eauto with arith.
  Qed.

  Require Import Lt.

  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros.
    unfold lt in *.
    intro H'.
    apply project_to_nat_unique in H'.
    rewrite H' in H.
    apply lt_irrefl in H.
    auto.
  Qed.

  Require Import Compare_dec.
  
  Theorem compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros.
    case (lt_eq_lt_dec (project_to_nat x) (project_to_nat y)); intros H;
      [case H; clear H; intros H; [constructor 1 | constructor 2; apply project_to_nat_unique in H] | constructor 3]; auto with arith.
  Qed.

  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.

End MiniProjectedOrderedType.

Module POT_to_OT (P:ProjectedToNat) <: OrderedType.
  Module MinProj := MiniProjectedOrderedType P.
  Include MinProj.
  Module Proj_OT := MOT_to_OT MinProj.
  Definition eq_dec := Proj_OT.eq_dec.
  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.
End POT_to_OT.


