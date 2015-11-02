Require Import Indices.
Require Import SetoidList.
(* Require Import SetoidListEquiv. *)


Module mkFacts (I:IndexType).

  (* perhaps I should use PairOrderedType and build a ListOrderedType ? *)

  Definition ci_eq  (ci ci': I.t * I.t) := I.eq (fst ci) (fst ci') /\ I.eq (snd ci) (snd ci').

  Theorem ci_eq_refl: forall ci, ci_eq ci ci.
  Proof.
    intros; destruct ci; unfold ci_eq; simpl;  split; apply I.eq_refl.
  Qed.

  Theorem ci_eq_sym: forall ci ci', ci_eq ci ci' -> ci_eq ci' ci.
  Proof.
    intros.
    destruct ci; destruct ci'.
    unfold ci_eq in *; simpl in *; destruct H; split;
      apply I.eq_sym; assumption.
  Qed.

  Theorem ci_eq_trans: forall ci1 ci2 ci3,
    ci_eq ci1 ci2 -> ci_eq ci2 ci3 -> ci_eq ci1 ci3.
  Proof.
    intros.
    destruct ci1; destruct ci2; destruct ci3.
    unfold ci_eq in *; simpl in *; destruct H; destruct H0; split;
      [apply I.eq_trans with t1 |apply I.eq_trans with t2]; auto.
  Qed.

  Theorem ci_eq_Equiv : Equivalence ci_eq.
    apply Build_Equivalence.
    unfold Reflexive; apply ci_eq_refl.
    unfold Symmetric; apply ci_eq_sym.
    unfold Transitive; apply ci_eq_trans.
  Qed.

  Definition cil_eq := eqlistA ci_eq.

  Definition cil_Equiv : Equivalence cil_eq.
  eapply eqlistA_equiv.
  exact ci_eq_Equiv.
  Defined.

End mkFacts.
