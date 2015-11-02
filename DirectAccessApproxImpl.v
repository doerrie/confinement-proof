Require Import SequentialAccess.
Require Import Sumbool_dec.
Require OrdFMapEquiv.
Require Import OptionMap2.
Require Import OptionSumbool.
Require Import FMapExists.
Require Import OrdFMapEquiv.
Require FMapFacts.
Require Import List.
Require Import Bool.
Require Import FMapAdd.
Require Import FoldEqual.
Require OrderedTypeEquiv.
Require CapIndexListFacts.
Require Import Semantics_Conv.
Require FoldOrder.
Require Import AccessRights.

Require Import References.
Require Import Capabilities.
Require Import Indices.
Require Import Objects.
Require Import SystemState.
Require Import SemanticsDefinitions.
Require Import Semantics.
Require Import Semantics_ConvImpl.
Require Import AccessRightSets.
(*Require Import DirectAccess.*)
Require Import DirectAccessSemanticsImpl.
Require Import AccessGraphs.
Require Import AccessEdge.
Require Import SequentialAccess.
Require Import RefSets.
(* type_remove *)
(*Require Import DirectAccessApprox.*)



Module MakeDirectAccessApprox (Ref:ReferenceType) (RefS: RefSetType Ref) (Edges: AccessEdgeType Ref) (AccessGraph:AccessGraphType Ref Edges) (Seq:SeqAccType Ref RefS Edges AccessGraph) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) (SemDefns: SemanticsDefinitionsType Ref Cap Ind Obj Sys) (Sem: SemanticsType Ref RefS Cap Ind Obj Sys SemDefns).

  Module DAS := MakeDirectAccessSemantics Ref RefS Edges AccessGraph Seq Cap Ind Obj Sys SemDefns Sem.
  Import DAS.
  Export DAS.

(* If we want to reduce everything, we need a notion of a dependant function as well
   It is not possible to push_cap_by_indices without looking at s. *)

Definition dirAcc_approx_dep Fs Fsa := forall s s' ag ag' ag2, 
  dirAcc_spec s ag -> dirAcc_spec (Fs s) ag2 -> AG.Subset ag ag' -> Sys.eq s s' -> AG.Subset ag2 (Fsa s' ag').

Definition st_equiv Fs := forall s s', Sys.eq s s' -> Sys.eq (Fs s) (Fs s').

Theorem dirAcc_approx_dep_comp: forall Fs Fsa Fs' Fsa',
  st_equiv Fs -> dirAcc_approx_dep Fs Fsa -> dirAcc_approx_dep Fs' Fsa' -> 
    dirAcc_approx_dep (fun s => Fs' (Fs s)) (fun s a => Fsa' (Fs s) (Fsa s a)).  
Proof.
  unfold dirAcc_approx_dep; intros.
  destruct (exists_dirAcc_spec (Fs s)) as [Fs_s HFs_s].
  eapply H1.
    apply HFs_s.
    auto.
    eapply H0; first [apply H2 | auto].
    eauto.
Qed.

Theorem dirAcc_approx_dirAcc_approx_dep: forall Fs Fa,
  dirAcc_approx Fs Fa -> dirAcc_approx_dep Fs (fun s => Fa).
Proof.
  unfold dirAcc_approx; unfold dirAcc_approx_dep.
  intros.
  eauto.  
Qed.

(* we wish to prove that each dependant theorem also commutes over add, et.
the requirements such a theorem yiekld our actual computation. this will allow
us to build operations that work over potacc *)


Definition id_ag (ag:AG.t) := ag.
Definition write_ag := id_ag.
Definition read_ag := id_ag.
Definition revoke_ag := id_ag.
Definition destroy_ag := id_ag.

Theorem dirAcc_approx_read: forall a c,
   dirAcc_approx (Sem.do_read a c) read_ag.
Proof.
   intros.
   unfold dirAcc_approx; intros; unfold read_ag; unfold id_ag.
   eapply AGProps.subset_trans;
     [eapply AGProps.subset_equal; eapply dirAcc_spec_eq;
       [eapply Sys.eq_refl
       |eapply H0
       |eapply dirAcc_read; apply H]
     |auto].
Qed.

Theorem potTransfer_fn_req_id : Seq.ag_potTransfer_fn_req id_ag.
Proof.
  repeat progress (red; simpl; intuition auto).
Qed.

Hint Resolve potTransfer_fn_req_id.

Theorem potTransfer_fn_req_read : Seq.ag_potTransfer_fn_req read_ag.
Proof.
  auto.
Qed.

Theorem dirAcc_approx_write:forall a c,
   dirAcc_approx (Sem.do_write a c) write_ag.
Proof.
   intros.
   unfold dirAcc_approx; intros; unfold read_ag; unfold id_ag.
   eapply AGProps.subset_trans;
     [eapply AGProps.subset_equal; eapply dirAcc_spec_eq;
       [eapply Sys.eq_refl
       |eapply H0
       |eapply dirAcc_write; apply H]
     |auto].
Qed.

Theorem potTransfer_fn_req_write : Seq.ag_potTransfer_fn_req write_ag.
Proof.
  auto.
Qed.

Theorem dirAcc_approx_revoke:forall a t c,
   dirAcc_approx (Sem.do_revoke a t c) revoke_ag.
Proof.
   intros; unfold dirAcc_approx; intros.
   eapply AGProps.subset_trans; [eapply dirAcc_revoke; [apply H | apply H0]| auto].
Qed.

Theorem potTransfer_fn_req_revoke : Seq.ag_potTransfer_fn_req revoke_ag.
Proof.
  auto.
Qed.

Theorem dirAcc_approx_destroy:forall a t,
   dirAcc_approx (Sem.do_destroy a t) destroy_ag.
Proof.
   intros; unfold dirAcc_approx; intros.
   eapply AGProps.subset_trans; [eapply dirAcc_destroy; [apply H | apply H0]| auto].
Qed.

Theorem potTransfer_fn_req_destroy : Seq.ag_potTransfer_fn_req destroy_ag.
Proof.
  auto.
Qed.

Definition store_dep_ag a t c s := ag_push_cap_by_indices a t a c s (fun c=>c) ag_add_cap_valid_std.
Definition allocate_dep_ag a n ixi_list s ag:= 
  if SemDefns.allocate_preReq_dec a n s then ag_add_caps_allocate a n ixi_list s ag else ag.
Definition fetch_dep_ag a t c s :=
  ag_add_cap_by_indirect_index a t c s 
    (if SemDefns.option_hasRight_dec (SC.getCap t a s) AccessRights.rd
     then (fun c => c)
     else Cap.weaken) ag_add_cap_valid_std.
Definition option_map1_eq_tgt_dec t a s:
  {option_map1 (fun cap => Ref.eq a (Cap.target cap)) False (SC.getCap t a s)}+
  {~ option_map1 (fun cap => Ref.eq a (Cap.target cap)) False (SC.getCap t a s)}.
intros;case (SC.getCap t a s); try intros cap'; [simpl; apply Ref.eq_dec |right; auto].
Defined.
Definition send_dep_ag a t ixi_list s:= 
  if (option_map1_eq_tgt_dec t a s)
  then (ag_add_caps_reply a t s)
  else (ag_add_caps_send a t ixi_list s).


Theorem dirAcc_approx_dep_store: forall a t c i,
  dirAcc_approx_dep (Sem.do_store a t c i) (store_dep_ag a t c).
  Proof.
  unfold dirAcc_approx_dep;  intros.
  (* we must reduce the goal: 
     Seq.AG.Subset ag2
      (ag_push_cap_by_indices a t a c s' (fun c0 : Cap.t => c0)
         ag_add_cap_valid_std ag')
     to:
     Seq.AG.Subset ag2
      (ag_push_cap_by_indices a t a c s (fun c0 : Cap.t => c0)
         ag_add_cap_valid_std ag) 
     so that we might apply dirAcc_store*)
  eapply AGProps.subset_trans; [eapply dirAcc_store; [apply H | apply H0]|].
  eapply ag_push_cap_by_indices_subset; try apply Ref.eq_sym; eauto. 
Qed.

Theorem potTransfer_fn_req_store : forall a t c s, Seq.ag_potTransfer_fn_req (store_dep_ag a t c s).
Proof.
  red; simpl; intros; intuition;
    red; simpl; intros; unfold store_dep_ag in *; auto; 
      try (apply ag_push_cap_by_indices_equiv; auto; try apply Sys.eq_refl; try apply Ref.eq_refl).
  eapply ag_push_cap_by_indices_add_commute; eauto.
Qed.

Ltac eapply_cil_refl := let refl := fresh in  destruct CIL_Facts.cil_Equiv as [refl _ _]; eapply refl.

Theorem dirAcc_approx_dep_allocate: forall a n i ixi_list,
  dirAcc_approx_dep (Sem.do_allocate a n i ixi_list) (allocate_dep_ag a n ixi_list).
Proof.
  unfold dirAcc_approx_dep;  intros.
  unfold allocate_dep_ag; case (SemDefns.allocate_preReq_dec a n s'); intros.

  eapply AGProps.subset_trans; [eapply dirAcc_allocate; [apply H | apply H0]|].
  eapply ag_add_caps_allocate_subset; try apply Ref.eq_refl; eauto.
  eapply_cil_refl.  

  eapply Sem.allocate_invalid in n0.
  eapply Sys.eq_sym in n0; eapply Sys.eq_trans in n0;[| apply H2]. 


  eapply dirAcc_spec_eq in H0;
    [eapply AGProps.subset_trans; [eapply AGProps.subset_equal; eapply AG.eq_sym; eapply H0 | apply H1]
    |eapply Sys.eq_trans; [eapply n0 | eapply SemConv.do_allocate_eq; eauto; generalize CIL_Facts.cil_Equiv; intros [cil_refl _ _]; try eapply cil_refl; try apply Ref.eq_refl]
    |eapply H].
Qed.

Theorem potTransfer_fn_req_allocate : forall a t c s, Seq.ag_potTransfer_fn_req (allocate_dep_ag a t c s).
Proof.
  unfold allocate_dep_ag in *; intros; case (SemDefns.allocate_preReq_dec a t s); red; simpl; intros; intuition;
    red; simpl; intros; auto;
      try (apply ag_add_caps_allocate_equiv; auto; try apply Sys.eq_refl; auto); 
        try apply ag_add_caps_allocate_add_commute; auto; (* this should be handled by hint, why not? *)
          try eapply_cil_refl; try apply Ref.eq_refl;auto.
Qed.

Theorem dirAcc_approx_dep_fetch: forall a t c i,
  dirAcc_approx_dep (Sem.do_fetch a t c i) (fetch_dep_ag a t c).
Proof.
  red; intros. unfold fetch_dep_ag.
  case (SemDefns.option_hasRight_dec (SC.getCap t a s')); intros HhasRef.
  Ltac solve_fetch_case dirAcc_fetch_case H H0 HhasR := 
   eapply AGProps.subset_trans;
    [eapply dirAcc_fetch_case;
      [eapply H
      |eapply H0
      |let HhasR' := fresh "HhasR" in 
        try (intro; apply HhasR); eapply SemDefns.option_hasRight_eq; [| | | | try apply HhasR; try apply HhasR']; 
          try apply Ref.eq_refl; try apply AccessRight.eq_refl; auto; try apply Sys.eq_sym; eauto]
    |eapply ag_add_cap_by_indirect_index_subset; try apply Ref.eq_refl; auto].
  solve_fetch_case dirAcc_fetch_read H H0 HhasRef.
  solve_fetch_case dirAcc_fetch_weak H H0 HhasRef.
Qed.

Theorem Fn_cap_equiv_sumbool: forall (P:Prop) (sb:{P}+{~P}) f f' f2 f2',
  Fn_cap_equiv f f' -> Fn_cap_equiv f2 f2' ->
  Fn_cap_equiv (if sb then f else f2) (if sb then f' else f2').
Proof.
  red; intros; destruct sb; auto. 
Qed.

Hint Resolve Fn_cap_equiv_sumbool.

Theorem potTransfer_fn_req_fetch : forall a t c s, Seq.ag_potTransfer_fn_req (fetch_dep_ag a t c s).
Proof.
  red; simpl; intros; intuition;
    red; simpl; intros; unfold fetch_dep_ag in *; auto;
      try (apply ag_add_cap_by_indirect_index_equiv; auto; try apply Sys.eq_refl; try apply Ref.eq_refl).
   eapply ag_add_cap_by_indirect_index_add_commute; eauto.
Qed.

Theorem dirAcc_approx_dep_send: forall a t ixi_list opt_i,
  dirAcc_approx_dep (Sem.do_send a t ixi_list opt_i) (send_dep_ag a t ixi_list).
Proof.
  red; intros. unfold send_dep_ag.
  case (option_map1_eq_tgt_dec t a s'); intros Hcase.
  eapply AGProps.subset_trans.
    eapply dirAcc_send_self.
      apply H.
      apply H0.
      red; red in Hcase;
      generalize (SC.getCap_eq _ _ _ _ _ _ H2 (Ind.eq_refl t) (Ref.eq_refl a)); intros Heq;
        case (option_sumbool (SC.getCap t a s')); intros Hc1; [|destruct Hc1 as [cap1 Hc1]]; rewrite Hc1 in *;
          (case (option_sumbool (SC.getCap t a s)); intros Hc2; [|destruct Hc2 as [cap2 Hc2]]; rewrite Hc2 in *);
            eauto; try solve [intuition auto; contradiction]; simpl in Heq;
              eapply Ref.eq_trans; [apply Hcase |apply Cap.target_eq; auto].
    eapply ag_add_caps_reply_subset; auto; try apply Ref.eq_refl.
  eapply AGProps.subset_trans.
    eapply dirAcc_send_other.
      apply H.
      apply H0.
      intros Hnot; apply Hcase; clear Hcase.
      red; red in Hnot.
      apply Sys.eq_sym in H2.
      generalize (SC.getCap_eq _ _ _ _ _ _ H2 (Ind.eq_refl t) (Ref.eq_refl a)); intros Heq.
        case (option_sumbool (SC.getCap t a s')); intros Hc1; [|destruct Hc1 as [cap1 Hc1]]; rewrite Hc1 in *;
          (case (option_sumbool (SC.getCap t a s)); intros Hc2; [|destruct Hc2 as [cap2 Hc2]]; rewrite Hc2 in *);
            eauto; try solve [intuition auto; contradiction]; simpl in Heq;
              eapply Ref.eq_trans; [apply Hnot |apply Cap.target_eq; auto].
    eapply ag_add_caps_send_subset; auto; try apply Ref.eq_refl.
  eapply_cil_refl.
Qed.

Theorem potTransfer_fn_req_send : forall a t c s, Seq.ag_potTransfer_fn_req (send_dep_ag a t c s).
Proof.
  red; simpl; intros; intuition;
    red; simpl; intros; unfold send_dep_ag in *; auto;
     case (option_map1_eq_tgt_dec t a s); intros;
      first [eapply ag_add_caps_reply_add_commute | eapply ag_add_caps_send_add_commute| 
        apply ag_add_caps_reply_equiv| apply ag_add_caps_send_equiv| idtac]; auto; try apply Sys.eq_refl; 
          try eapply_cil_refl;
            try apply Ref.eq_refl.
Qed.

End MakeDirectAccessApprox.