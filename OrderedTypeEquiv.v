Require Import RelationClasses.
Require Import OrderedType.

Module OT_Equiv (O: OrderedType).

  Theorem Equiv: Equivalence O.eq.
  Proof.
    intros.
    eapply Build_Equivalence.
    unfold Reflexive; apply O.eq_refl; auto.
    unfold Symmetric; apply O.eq_sym; auto.
    unfold Transitive; apply O.eq_trans; auto.
  Qed.

  Theorem Leibniz_eq: forall {x} {x'},
    Logic.eq x x' -> O.eq x x'.
  Proof.
    intros; rewrite H in *; try apply O.eq_refl.
  Qed.

End OT_Equiv.