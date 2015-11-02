Require Import FMapInterface2.
Require Import OptionMap2.
Require Import OptionSumbool.
Require Import OrdFMapEquiv.
Require Import FMapFacts2.

(* These properties really don't rely on sortedness, but I'm not dealing with converting
between the two implementations as Coq's libraries are not friendly for this *)

Module MakeAdd (E:OrderedType) (MapS: Sfun E) (Data:OrderedType) (S:Sord_fun E MapS Data).

  Module SOrdProps := OrdProperties_fun E MapS.
  Module SProps := SOrdProps.P.
  Module SFacts := SProps.F.
  Module SEquiv := MakeEquiv_fun E MapS Data S.

Theorem add_add: forall k v k' (v':Data.t) s,
  ~ E.eq k k' ->
  MapS.Equal (MapS.add k v (MapS.add k' v' s))
               (MapS.add k' v' (MapS.add k v s)).
Proof.
   intros.
   intro elem.
   case (E.eq_dec elem k); case (E.eq_dec elem k'); intros Hek Hek'.

   eapply E.eq_trans in Hek; [ | apply E.eq_sym; eapply Hek']; contradiction.

   rewrite SFacts.add_eq_o; auto.
   rewrite SFacts.add_neq_o; auto.
   rewrite SFacts.add_eq_o; auto.

   rewrite SFacts.add_neq_o; auto.
   rewrite SFacts.add_eq_o; auto.
   rewrite SFacts.add_eq_o; auto.

   repeat progress (rewrite SFacts.add_neq_o; auto).

Qed.

Hint Resolve add_add.

Theorem add_eq : forall k v s k' v' s',
  E.eq k k' ->
  Data.eq v v' ->
  S.eq s s' ->
  S.eq (MapS.add k v s)
       (MapS.add k' v' s').
Proof.
    intros.
    apply S.eq_1.
    unfold MapS.Equivb.
    unfold MapS.Equiv.
    unfold Cmp.
    generalize (S.eq_2 H1); intros H1'.
    unfold MapS.Equivb in H1'.
    unfold MapS.Equiv in H1'.
    unfold Cmp in H1'.
    destruct H1' as [H1' H2].
    split; intros; [split; intros|].
    (*case 1 *)
    eapply SFacts.add_in_iff.
    apply SFacts.add_in_iff in H3.
    destruct H3; [left; eauto|  right; eapply H1'; assumption].
    (* case 2, identical to case 1 *)
    eapply SFacts.add_in_iff.
    apply SFacts.add_in_iff in H3.
    destruct H3; [left; eauto|  right; eapply H1'; assumption].
    (* case 3 *)
    (* need to show C.eq e e' *)
    apply SFacts.add_mapsto_iff in H3.
    apply SFacts.add_mapsto_iff in H4.
    destruct H3; destruct H4; destruct H3; destruct H4;
    unfold S.cmp in *;
    generalize (Data.compare e e'); intros CMP.
    (* case 3.1 *)
    destruct CMP as [CMP|CMP|CMP]; rewrite H5 in H0; rewrite H6 in H0.
    apply Data.lt_not_eq in CMP; contradiction.
    trivial. 
    apply Data.lt_not_eq in CMP; apply Data.eq_sym in H0; contradiction.
    (* case 3.2 *)
    apply E.eq_sym in H.
    apply E.eq_trans with (x:= k') (y:= k) (z:= k0) in H; auto.
    (* case 3.3 *)
    apply E.eq_trans with (x:= k) (y:= k') (z:= k0) in H; auto.
    (* case 3.4 *)
    assert (Data.eq e e');
    [eapply SEquiv.mapsTo_eq; [apply E.eq_refl | apply H1 | eauto | eauto] |].
    destruct CMP as [CMP|CMP|CMP]; auto.
    apply Data.lt_not_eq in CMP; contradiction.
    apply Data.lt_not_eq in CMP. apply Data.eq_sym in H7; contradiction.
Qed.

Hint Resolve add_eq.

Theorem sord_add_add: forall k v k' v' s s',
  S.eq s s' ->
  ~ E.eq k k' ->
  S.eq (MapS.add k v (MapS.add k' v' s))
       (MapS.add k' v' (MapS.add k v s')).
Proof.
  intros.
  apply S.eq_trans with (MapS.add k' v' (MapS.add k v s)); auto.
  apply SEquiv.Equal_eq; eapply add_add; auto.
Qed.
End MakeAdd.