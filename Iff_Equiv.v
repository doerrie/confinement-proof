Require Import RelationClasses.

Theorem iff_refl: forall o:Prop, iff o o.
Proof.
  intros;split;auto.
Qed.

Theorem iff_symmetric: forall (o1 o2: Prop),
  iff o1 o2 -> iff o2 o1.
Proof.
  intros.
  destruct H; split; auto.
Qed.

Theorem iff_transitive: forall (o1 o2 o3: Prop),
  iff o1 o2 -> iff o2 o3 -> iff o1 o3.
Proof.
  intros; destruct H; destruct H0; split; auto.
Qed.

Theorem iff_Equiv: Equivalence iff.
Proof.
  intros.
  eapply Build_Equivalence.
  unfold Reflexive; apply iff_refl; auto.
  unfold Symmetric; apply iff_symmetric; auto.
  unfold Transitive; apply iff_transitive; auto.
Qed.