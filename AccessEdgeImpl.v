Require Import Decidable.
Require Import References.
Require Import AccessRights.
Require Import FSets.
Require Import OrderedTypeEx.
(* type_remove *)
Require Import AccessEdge.

Module Make (R: ReferenceType) : AccessEdgeType R.

  Module AccessArrow := !PairOrderedType R AccessRight.

  Module AccessEdge := !PairOrderedType R AccessArrow.

  Definition mkEdge (src tgt:R.t) (rgt:accessRight): AccessEdge.t :=
    (pair src (pair tgt rgt)).

  Definition source (edge : AccessEdge.t) := fst edge.
  Definition target (edge : AccessEdge.t) := fst (snd edge).
  Definition right (edge : AccessEdge.t) := snd (snd edge).

  Theorem eq_equal : forall edge edge',
    AccessEdge.eq edge edge' <-> edge = edge'.
  Proof.
    intros.
    split; intros.
    destruct edge as [src arrow]; destruct arrow as [tgt rgt]; destruct edge' as [src' arrow']; destruct arrow' as [tgt' rgt'].
    unfold AccessEdge.eq in H.
    destruct H as [H H0]; simpl in H;
    destruct H0 as [H0 H1]; simpl in H0; simpl in H1.
    unfold R.eq in *; unfold AccessRight.eq in *.
    rewrite H; rewrite H0; rewrite H1.
    trivial.
    unfold AccessEdge.eq.
    rewrite H.
    unfold AccessArrow.eq; unfold AccessRight.eq; unfold R.eq; 
    auto.
  Qed.

  Theorem eq_source : forall edge edge':AccessEdge.t,
    AccessEdge.eq edge edge' -> R.eq (source edge) (source edge').
  Proof.
    intros.
    unfold AccessEdge.eq in H.
    destruct H.
    unfold AccessArrow.eq in H0.
    destruct H0.
    assumption.
  Qed.

  Theorem eq_target : forall edge edge':AccessEdge.t,
    AccessEdge.eq edge edge' -> R.eq (target edge) (target edge').
  Proof.
    intros.
    unfold AccessEdge.eq in H.
    destruct H.
    unfold AccessArrow.eq in H0.
    destruct H0.
    assumption.
  Qed.

  Theorem eq_right : forall edge edge':AccessEdge.t,
    AccessEdge.eq edge edge' -> AccessRight.eq (right edge) (right edge').
  Proof.
    intros.
    unfold AccessEdge.eq in H.
    destruct H.
    unfold AccessArrow.eq in H0.
    destruct H0.
    assumption.
  Qed.

(*  Hint Resolve eq_source eq_target eq_right. *)

  Theorem edge_equal : forall (src src' tgt tgt':R.t) (rgt rgt':accessRight),
    R.eq src src' -> R.eq tgt tgt' -> AccessRight.eq rgt rgt' -> AccessEdge.eq (mkEdge src tgt rgt) (mkEdge src' tgt' rgt').
  Proof.
    intros.
    unfold mkEdge.
    unfold AccessEdge.eq.
    unfold AccessArrow.eq.
    unfold AccessRight.eq.
    simpl.
    split;[eauto|split;eauto].
  Qed.

  Theorem edge_rewrite : forall edge:AccessEdge.t,
    mkEdge (source edge) (target edge) (right edge) = edge.
  Proof.
    intros.
    destruct edge as [src arrow].
    destruct arrow as [tgt rgt].
    eauto.
  Qed.

  Hint Rewrite edge_rewrite : caps_rewrite.

  Theorem source_rewrite: forall src tgt rgt,
    (source (mkEdge src tgt rgt)) = src.
  Proof.
    intuition.
  Qed.
  Theorem target_rewrite: forall src tgt rgt,
    (target (mkEdge src tgt rgt)) = tgt.
  Proof.
    intuition.
  Qed.
  Theorem right_rewrite: forall src tgt rgt,
    (right (mkEdge src tgt rgt)) = rgt.
  Proof.
    intuition.
  Qed.
 
  Hint Rewrite source_rewrite right_rewrite target_rewrite : caps_rewrite.

End Make.
  