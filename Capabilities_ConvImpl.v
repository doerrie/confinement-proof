(* type_remove *)
Require Import Capabilities_Conv.
Require Import References.
Require Import Capabilities.
Require Import AccessRights.
Require Import AccessRightSets.
Require Import Sumbool_dec.
Require Import Bool.
Require Import OrderedTypeEquiv.


Module MakeCapConv (Ref: ReferenceType) (Cap:CapabilityType Ref) : CapabilityConv Ref Cap.

  Module Cap_Equiv := OT_Equiv Cap.
  Definition CapEQ := Cap_Equiv.Equiv.

  Module Ref_Equiv := OT_Equiv Ref.
  Definition RefEQ := Ref_Equiv.Equiv.

  Definition hasRight c rgt:= ARSet.In rgt (Cap.rights c).
  
  Theorem mkCap_target: forall t r,
    Ref.eq (Cap.target (Cap.mkCap t r)) t.
  Proof.
    intros.
    generalize (Cap.mkCap_eq t r (Cap.mkCap t r)); intros.
    destruct H; clear H.
    generalize (H0 (Cap.eq_refl _)); intros; clear H0.
    destruct H.
    apply Ref.eq_sym; auto.
  Qed.

  Theorem mkCap_rights: forall t r,
    ARSet.eq
    (Cap.rights (Cap.mkCap t r)) r.
  Proof.
    intros.
    generalize (Cap.mkCap_eq t r (Cap.mkCap t r)); intros.
    destruct H; clear H.
    generalize (H0 (Cap.eq_refl _)); intros; clear H0.
    destruct H.
    apply ARSet.eq_sym; auto.
  Qed.

  Theorem mkCap_equiv: forall a a' r r',
    Ref.eq a a' ->
    ARSet.eq r r' ->
    Cap.eq (Cap.mkCap a r) (Cap.mkCap a' r').
  Proof.
    intros.
    generalize (Cap.mkCap_eq a r (Cap.mkCap a' r')).
    intros H1.
    destruct H1.
    apply H1.
    split.
    apply Ref.eq_trans with a'; auto.
    apply Ref.eq_sym; apply mkCap_target.
    apply ARSet.eq_trans with r'; auto.
    apply ARSet.eq_sym; apply mkCap_rights.
  Qed.

  (* inter_eq is just inter_m, but we don't use it anymore. *)

  Theorem weaken_target_eq : forall cap,
    Ref.eq (Cap.target (Cap.weaken cap)) (Cap.target cap).
  Proof.
    intros.
    generalize (Cap.weaken_eq cap); intros Hcap_eq.
      (* for some reason, we can't use ... ; [ ... | ... ]. for this one. *)
    eapply Ref.eq_trans.
    eapply Cap.target_eq; eapply Hcap_eq.
    rewrite mkCap_target; eauto.
  Qed.



  Theorem In_weak_weaken : forall cap rgt,
    ARSet.In rgt (Cap.rights (Cap.weaken cap)) -> rgt = wk.
  Proof.
    intros.
    generalize (Cap.weaken_eq cap); intros.
    case (bool_dec 
      (true_bool_of_sumbool
        (ARSetProps.In_dec wk
          (Cap.rights cap))
        || true_bool_of_sumbool
          (ARSetProps.In_dec rd
            (Cap.rights cap))) true); intros Hdec;
    [|eapply not_true_is_false in Hdec]; rewrite Hdec in *; clear Hdec;

      (eapply Cap.rights_eq in H0;
        generalize mkCap_rights; intros Hrights; eapply ARSet.eq_sym in Hrights;
          apply ARSet.eq_sym in H0; eapply ARSet.eq_trans in H0; [clear Hrights | apply Hrights];
            eapply AccessRight.eq_sym; eapply H0 in H; 
              solve[ eapply ARSetFacts.singleton_iff; eauto | eapply ARSetFacts.empty_iff in H; contradiction]).
  Qed.


  Theorem weaken_singleton_or_empty: forall cap,
    {ARSet.eq (Cap.rights (Cap.weaken cap)) (ARSet.singleton wk)} + 
    {ARSet.eq (Cap.rights (Cap.weaken cap)) (ARSet.empty)}.
  Proof.
    intros; generalize (Cap.weaken_eq cap); intros Hcap_eq; intros.

    case (bool_dec 
      (true_bool_of_sumbool
        (ARSetProps.In_dec wk
          (Cap.rights cap))
        || true_bool_of_sumbool
          (ARSetProps.In_dec rd
            (Cap.rights cap))) true); intros Hdec;
    [|eapply not_true_is_false in Hdec]; rewrite Hdec in *;
      [eapply orb_prop in Hdec| eapply orb_false_elim in Hdec]; clear Hdec;
        [left | right]; eapply Cap.rights_eq in Hcap_eq; rewrite mkCap_rights in Hcap_eq; auto.
  Qed.

    (* generalize and toss somewhere *)
  Theorem singleton_is_not_empty: forall x,
    ~ ARSet.Equal ARSet.empty (ARSet.singleton x).
  Proof.
    intros.
    unfold ARSet.Equal.
    intro H.
    generalize (H x); clear H; intro H.
    eapply iff_sym in H.
    eapply iff_trans in H;[| eapply iff_sym; eapply ARSetFacts.singleton_iff].
    destruct H.
    generalize (H (refl_equal _)).
    eapply ARSetFacts.empty_iff.
  Qed.

  Theorem weaken_rights_weak_eq:forall cap,
    ARSet.In wk (Cap.rights cap) \/ ARSet.In rd (Cap.rights cap) <->
    ARSet.eq (Cap.rights (Cap.weaken cap)) (ARSet.singleton wk).
  Proof.
    intros; generalize (Cap.weaken_eq cap); intros Hcap_eq; split; intros.

    eapply ARSet.eq_trans; [eapply Cap.rights_eq; eapply Hcap_eq |].
    destruct H as [H | H];
      unfold true_bool_of_sumbool; rewrite (proof_r_true_bool_of_sumbool _ _ H); simpl;
        try rewrite orb_true_r;
          rewrite mkCap_rights; apply ARSet.eq_refl.
    
    case (bool_dec 
      (true_bool_of_sumbool
        (ARSetProps.In_dec wk
          (Cap.rights cap))
        || true_bool_of_sumbool
          (ARSetProps.In_dec rd
            (Cap.rights cap))) true); intros Hdec;
    [|eapply not_true_is_false in Hdec]; rewrite Hdec in *;
      [eapply orb_prop in Hdec| eapply orb_false_elim in Hdec].
    
    (* true case *)
    unfold true_bool_of_sumbool in *;
      destruct Hdec as [Hdec | Hdec]; eapply true_bool_of_sumbool_l in Hdec; intuition.
    (* false case *)
    clear Hdec.
    eapply Cap.rights_eq in Hcap_eq.
    eapply ARSet.eq_trans in Hcap_eq; [clear H| eapply ARSet.eq_sym; apply H].
    eapply ARSet.eq_sym in Hcap_eq; eapply ARSet.eq_trans in Hcap_eq;
      [| eapply ARSet.eq_sym; eapply mkCap_rights].
    idtac.
    eapply singleton_is_not_empty in Hcap_eq; contradiction.
  Qed.

  Theorem In_weaken_singleton: forall cap,
    ARSet.In wk (Cap.rights (Cap.weaken cap)) ->
    ARSet.eq (Cap.rights (Cap.weaken cap)) (ARSet.singleton wk).
  Proof.
    intros.
    case (weaken_singleton_or_empty cap); intros; auto.
    eapply e in H.
    eapply ARSetFacts.empty_iff in H; contradiction.
  Qed.

  Theorem weaken_equiv: forall cap cap',
    Cap.eq cap cap' ->
    Cap.eq (Cap.weaken cap) (Cap.weaken cap').
  Proof.
    intros.
    eapply Cap.eq_trans; [eapply Cap.weaken_eq|].
    eapply Cap.eq_sym; eapply Cap.eq_trans; [apply Cap.weaken_eq|].
    eapply mkCap_equiv; [eapply Cap.target_eq; auto|].
    apply Cap.rights_eq in H.
    case (ARSetProps.In_dec wk (Cap.rights cap)); intros Hweak; simpl; 
      [eapply H in Hweak; 
        unfold true_bool_of_sumbool; rewrite (proof_r_true_bool_of_sumbool _ _ Hweak); simpl;
          apply ARSet.eq_refl|].
    case (ARSetProps.In_dec rd (Cap.rights cap)); intros Hread; simpl;
      [eapply H in Hread;
        unfold true_bool_of_sumbool; rewrite (proof_r_true_bool_of_sumbool _ _ Hread); simpl;
          rewrite orb_true_r; apply ARSet.eq_refl|].
    unfold true_bool_of_sumbool; repeat progress (rewrite proof_l_true_bool_of_sumbool); simpl;
      try apply ARSet.eq_refl.
    intro; apply Hread; eapply H; auto.
    intro; apply Hweak; eapply H; auto.
  Qed.

End MakeCapConv.
