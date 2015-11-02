Require Import AccessRights.
Require Import References.
Require Import Capabilities.
Require Import Indices.
Require Import Objects.
Require Import SystemState.
Require Import SemanticsDefinitions.
Require Import Semantics.
Require Import Semantics_Conv.
Require Import AccessRightSets.
Require Import AccessGraphs.
Require Import AccessEdge.
Require Import SequentialAccess.
Require Import RefSets.
Require Import DirectAccessApproxImpl.


Module MakeAttenuation (Ref:ReferenceType) (RefS: RefSetType Ref) (Edges: AccessEdgeType Ref) (AccessGraph:AccessGraphType Ref Edges) (Seq:SeqAccType Ref RefS Edges AccessGraph) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) (SemDefns: SemanticsDefinitionsType Ref Cap Ind Obj Sys) (Sem: SemanticsType Ref RefS Cap Ind Obj Sys SemDefns).

  Module DAX := MakeDirectAccessApprox Ref RefS Edges AccessGraph Seq Cap Ind Obj Sys SemDefns Sem.
  Import DAX.
  Export DAX.

(* Import Seq.RefSet_Mod. *)
Import RefS.


(* Read:
   If p' conservatively approximates p [=] (potAcc i), then
   (Fi p') conservatively approximates p2 [=] (potAcc (Fs i)). *)

Definition potAcc_approx Fi Fp := forall i p p' p2, 
  Seq.potAcc i p -> Seq.potAcc (Fi i) p2 -> AG.Subset p p' -> AG.Subset p2 (Fp p').

Theorem potAcc_subset_approx_comp: forall Fi Fa Fi' Fa',
  potAcc_approx Fi Fa -> potAcc_approx Fi' Fa' -> potAcc_approx (fun s => Fi' (Fi s)) (fun a => Fa' (Fa a)).  
Proof.
  unfold potAcc_approx; intros.
  destruct (Seq.exists_potAcc (Fi i)) as [Fi_i HFi_i].
  eapply H0; [apply HFi_i | auto | eapply H; first [apply H1 | auto]].
Qed.

Theorem potAcc_fn_potAcc: forall Fa i p p' p2,
  Seq.ag_potTransfer_fn_req  Fa -> Seq.potAcc i p -> Seq.potAcc (Fa i) p2 -> Seq.potAcc (Fa p) p' -> AG.Equal p2 p'.
Proof.
  intros Fa i p p' p2 Hseq PA1 PA2 PA3.
  generalize PA3; intros [P3 M3].
  eapply AG.eq_sym; eapply M3.
  generalize (Seq.potAcc_commute_monotonic Hseq PA1 p2); intros.
  eapply H in PA2.  
  destruct PA2 as [P2 M2].
  generalize (Seq.potTransfer_lub P2 P3); intros [p'' [P4 P5]].
  eapply M2 in P5.
  eapply Seq.potTransfer_transitive; [apply P4 |].
  apply AG.eq_sym in P5; apply Seq.potTransfer_base in P5; auto.
Qed.

Hint Resolve potAcc_fn_potAcc.

Theorem potAcc_approx_potAcc_fun : forall Fa, 
  Seq.ag_potTransfer_fn_req Fa -> potAcc_approx Fa (fun ag => Seq.potAcc_fun (Fa ag)).
Proof.
unfold potAcc_approx. intros Fa Hreq i p p' p2 HpotAcc_i_p HpotAcc_Fi_p2 Hsubset_p_p'.
(* from (ag_nondecr Fa): AG.Subset i (Fa i).
   from potAcc_monotonic and above: p [<=] p2. *)
generalize (Seq.potAcc_potAcc_fun (Fa p)); intros.
generalize (potAcc_fn_potAcc _ _ _ _ _ Hreq HpotAcc_i_p HpotAcc_Fi_p2 H); intros.
eapply AGProps.subset_trans; [eapply AGProps.subset_equal; apply H0|].
generalize Hreq; intros [Hcomm [Hmono Hequiv]].
eapply Seq.potAcc_monotonic; try solve [eapply Seq.potAcc_potAcc_fun; eauto].
eapply Seq.ag_subset_add_commute; eauto.
Qed.

(* alright, at this point, we need to reduce the primitive operations of dirAcc_approx over potAcc_approx.
   most of these will reduce to the identity operation, so we should start with a
   a list of requirements for turning an ag_add_cap operation over dirAcc into identity over potAcc.
   after that, we should be able to string these together to do the right thing. *)

(* we need:
     dirAcc_fetch_read: 
       ag_add_cap_by_indirect_index id std:
          ag_add_cap_by_obj_index id std
     dirAcc_fetch_weak: 
       ag_add_cap_by_indirect_index weaken std:
          ag_add_cap_by_obj_index weaken std
     dirAcc_store:
       ag_push_cap_by_indices:
          ag_add_cap_by_obj_index id std
     dirAcc_send_self:
       ag_add_caps_reply
     dirAcc_send_other:
       relevant ag_add_caps_send:
          ag_add_caps_by_index_pair_list id std:
             ag_add_cap_by_obj_index id std
          ag_add_caps_reply
             ag_add_cap_valid id std
     dirAcc_allocate:
       relevant ag_add_caps_allocate:
          ag_add_caps_by_index_pair_list id allocate
             ag_add_cap_by_obj_index id allocate


read_cap src o \/ write_cap o src \/ send_cap o src ->
potacc_m (ag_add_cap_by_obj_index src o i s id std) id
*)     

(* We will show that these functions are equivalent to producing a potTransfer.  We can move them using potAcc_approx_potAcc_fun.  Therefore, we can reduce them to identity. *)

(* this theorem requires Fc to be a reduction on rights only, and only solves for all standard Fv cases *)

(* 
we can only potTransfer ag (ag_add_cap_by_obj_index src o i s Fc std ag) when:
* we may assume that src and (target (getCap o i s)) are both alive *

*)

Require Import OptionSumbool.
Require Import Bool.
Require Import ObjectLabels.



  


Theorem potTransfer_reply_dep_ag: forall a t s ag ag',
  SemDefns.send_preReq a t s ->
  dirAcc_spec s ag ->
  Seq.potTransfer ag ag' ->
  Seq.potTransfer ag (ag_add_caps_reply a t s ag').
Proof.
  intros.
  unfold ag_add_caps_reply.
  case ( option_sumbool (SemDefns.SC.getCap t a s)); intros Hcap; [|destruct Hcap as [cap Hcap]]; 
    try rewrite Hcap in *; simpl in *; auto. 
  unfold ag_add_cap_valid.
  case (ag_add_cap_valid_std (Cap.target cap) (Cap.mkCap a (ARSet.singleton AccessRights.tx)) s); simpl; auto.
(*  case (bool_dec (ag_add_cap_valid_std (Cap.target cap) (Cap.mkCap a (A.AccessRightFSet.singleton A.send)) s) true);
    intros Hb; [|eapply not_true_is_false in Hb]; rewrite Hb; simpl; auto. *)
  unfold ag_add_cap_mod; simpl.
  eapply Seq.potTransfer_trans;
    [apply H1
    |eapply Seq.transfer_send_reply with (tgt:=(Cap.target cap)) (src:=a)].
  unfold SemDefns.send_preReq in *.
  unfold SemDefns.preReq in *.
  destruct H as [[[Halive Hactive] Htalive] Hsend].
  unfold SemDefns.target_is_alive in *.
  rewrite Hcap in *; simpl in *.
  (* show that our prereq edge is in ag *)
  apply Seq.potTransfer_subset in H1;
  apply H1; eapply dirAcc_simpl; eauto; try apply Ref.eq_refl.
  (* demonstrate adding an edge is ag_add_cap on a singleton *)
  (* the remainder should be trivial given fold on a singleton and definitions *)
  unfold ag_add_cap.
  generalize (Cap.target cap); intros t0.
  clear H H0 cap Hcap.  
  eapply AGAddEq.Add_eq_complete; [auto | auto | |].
  eapply AG.eq_sym.  eapply AG.eq_trans. eapply AG.eq_sym.
  eapply ARSetFold.fold_foldEqual with (eqA := AG.Equal).
(*    (f:= (fun rgt acc => AG.add (Edges.mkEdge t0 a rgt) acc)). *)
  (* equivalence of AG.Equal *)
  eauto.
  (* reduce singleton *)
  eapply ARSet.eq_trans; [| apply ARSet.eq_sym; eapply CC.mkCap_rights].
  eapply ARSet.eq_sym; eapply ARSetProps.singleton_equal_add.
  (* ag_refl *)
  auto.
  (* reduce fold functions *)
  eapply ARSetFold.foldEqual_refl.
  (* morphism *)
  Require Import Morphisms.
  red; unfold respectful;  intros.
  Ltac solve_f_as_morphism Hxy Hxy0 :=
  eapply AGAddEq.Eq_Add_complete; 
   [eauto | eapply Hxy0 | eapply AGProps.Add_add | rewrite Hxy; eapply AGProps.Add_add].
  solve_f_as_morphism H H0.
  (* f transposes *)
  red; intros; eapply AGProps.add_add.
  (* reduce the fold *)
  eapply ARSetProps.fold_add with (eqA:=AG.eq). eauto.
  (* compat op f *)
  red; unfold Proper; unfold respectful; intros. solve_f_as_morphism H H0.
  (* f transpose *)
  red; intros; eapply AGProps.add_add.
  (* remove send *)
  eapply ARSet.empty_1.
  (* last unroll *)
  rewrite ARSetProps.fold_empty.
  (* use add_eq *)
  eapply AGAddEq.Add_eq_complete; [ auto | auto| | eapply AGProps.Add_add].
  eapply AGAddEq.Eq_Add_complete; [ | eapply AG.eq_refl | eapply AGProps.Add_add | eapply AGProps.Add_add].
  rewrite CC.mkCap_target.
  eapply Edge.eq_refl.
  (* less trivial than expected *)
  Qed.

Theorem potTransfer_ag_add_cap_by_obj_index_std_write_send: forall ag ag' i o s cap f w src,
   SC.is_alive o s ->
   SC.getCap w o s = Some cap ->
   (CC.hasRight cap AccessRights.wr \/ CC.hasRight cap AccessRights.tx) ->
   Ref.eq (Cap.target cap) src ->
   f = (fun c=>c) -> 
   dirAcc_spec s ag ->
   Seq.potTransfer ag ag' ->
   Seq.potTransfer ag (ag_add_cap_by_obj_index src o i s f ag_add_cap_valid_std ag').
Proof.
  intros ag ag' i o s cap f w src Hwitness_alive Hcap Hright Htarget Hf Hda HpotTransfer.
  Ltac reduce_potTransfer_ag_add_cap_by_obj_index i o s src Fvalid:=
  let Hcap := fresh "Hcap" with cap := fresh "cap" with Hb := fresh "Hvalid" in
  unfold ag_add_cap_by_obj_index;
    case (option_sumbool (SC.getCap i o s)); intros Hcap; [|destruct Hcap as [cap Hcap]]; 
      rewrite Hcap; simpl; auto; unfold ag_add_cap_valid;
        case (bool_dec (Fvalid src cap s) true); intros Hb;
          [|eapply not_true_is_false in Hb]; rewrite Hb; simpl; auto.
  reduce_potTransfer_ag_add_cap_by_obj_index i o s src ag_add_cap_valid_std.
  unfold ag_add_cap_mod; unfold ag_add_cap.
  eapply ARSetProps.fold_rec_nodep; auto.
  intros rgt ag2; intros.
  eapply Seq.potTransfer_trans; [apply H0|].
  (* reduce out ag_add_cap_valid_std *)
   eapply andb_true_iff in Hvalid; destruct Hvalid as [Halive_dec Htarget_alive_dec].
   Require Import Sumbool_dec.
   eapply true_bool_of_sumbool_l in Halive_dec.
   eapply true_bool_of_sumbool_l in Htarget_alive_dec.
  (* show that (Cap.target (f cap0)) [=] (Cap.target cap0) *)
  rewrite Hf.
  
  destruct Hright as [Hright | Hright];
  (* write case *)
  [eapply Seq.transfer_write with (rgt:=rgt) (src:=o) (tgt:=src) (tgt':= (Cap.target (f cap0)))
  |eapply Seq.transfer_send with (rgt:=rgt) (src:=o) (tgt:=src) (tgt':= (Cap.target (f cap0)))];
  (* mkEdge o src write *)
  solve [eapply (Seq.potTransfer_subset H0);
  eapply dirAcc_simpl;[
   (* dirAcc *)
   apply Hda
   (* is_alive o s*)
   | auto
   (* getcap w o s*)
   | apply Hcap
   (* src [=] (Cap.target cap) *)
   | apply Ref.eq_sym; auto
   (* is_alive src s *)
   | apply Halive_dec
   (* hasRight cap write *)
   | auto]
  (* mkEdge o (Cap.target (f cap0)) rgt *)  
   | eapply (Seq.potTransfer_subset H0);
   eapply dirAcc_simpl;
   (* dirAcc *)
   [ apply Hda
   (* is_alive o s*)
   | auto
   (* getcap _ o s*)
   | eauto
   (* (Cap.target (f cap0)) [=] (Cap.target cap) *)
   | rewrite Hf; eauto; apply Ref.eq_refl
   (* is_alive (Cap.target (f cap0)) s *)
   | rewrite Hf; auto
   (* hasRight cap0 rgt *)
   | unfold CC.hasRight; rewrite Hf in *; simpl in *; auto]
  (* Add_add *)
  | rewrite Hf; apply AGProps.Add_add].

Qed.

Theorem potTransfer_ag_add_caps_by_index_pair_list_write_send: forall ag ag' t a s cap ixi_list f,
  SC.getCap t a s = Some cap ->
  CC.hasRight cap AccessRights.wr \/ CC.hasRight cap AccessRights.tx ->
  f = (fun c => c) ->
  SC.is_alive a s ->
  dirAcc_spec s ag ->
  Seq.potTransfer ag ag' ->
  Seq.potTransfer ag 
    (ag_add_caps_by_index_pair_list (Cap.target cap) a ixi_list s f ag_add_cap_valid_std ag').
Proof.
  intros ag ag' t a s cap ixi_list f Hcap Hrgt Hcap_fn Halive Hda Hpot.
  unfold ag_add_caps_by_index_pair_list.
  induction ixi_list; simpl; auto.
  eapply potTransfer_ag_add_cap_by_obj_index_std_write_send; eauto. try apply Ref.eq_refl.
Qed.


Theorem potTransfer_send_dep_ag: forall a t ixi_list s ag ag',
  dirAcc_spec s ag ->
  SemDefns.send_preReq a t s ->
  Seq.potTransfer ag ag' ->
  Seq.potTransfer ag (send_dep_ag a t ixi_list s ag').
Proof.
  intros.
  unfold send_dep_ag.
  unfold option_map1_eq_tgt_dec.
  case ( option_sumbool (SC.getCap t a s)); intros Hcap; [|destruct Hcap as [cap Hcap]]; 
    try rewrite Hcap in *; simpl in *;[| case (Ref.eq_dec a (Cap.target cap)); intros HrEq];
(* send None -> reply and send self cases *)
     try solve[try(unfold ag_add_caps_send; rewrite Hcap; simpl); eapply potTransfer_reply_dep_ag; eauto].
(* ag_add_caps_send case *)
    unfold ag_add_caps_send. rewrite Hcap; simpl.
    destruct H0 as [Hpre Hsend].
    rewrite Hcap in Hsend; simpl in *.
  eapply potTransfer_ag_add_caps_by_index_pair_list_write_send; auto; 
    [ apply Hcap
    | unfold SemDefns.preReq in *; unfold SemDefns.preReqCommon in *; intuition 
    | eapply potTransfer_reply_dep_ag; eauto; unfold SemDefns.send_preReq; rewrite Hcap; simpl; intuition].
Qed.

Theorem potTransfer_store_dep_ag: forall a t c s ag ag',
  dirAcc_spec s ag ->
  SemDefns.store_preReq a t s ->
  Seq.potTransfer ag ag' ->
  Seq.potTransfer ag (store_dep_ag a t c s ag'). 
Proof.
  intros.
  unfold store_dep_ag.
  unfold ag_push_cap_by_indices.
   case ( option_sumbool (SC.getCap t a s)); intros Hcap; [|destruct Hcap as [cap Hcap]]; 
    try rewrite Hcap in *; simpl in *; auto.
    destruct H0 as [Hpre Hsend].
  (* very similar to send case, can we generalize tactics ? *)
  eapply potTransfer_ag_add_cap_by_obj_index_std_write_send; auto;
    [ unfold SemDefns.preReq in *; unfold SemDefns.preReqCommon in *; intuition 
    | apply Hcap
    | unfold SemDefns.option_hasRight in *; rewrite Hcap in *;  simpl; intuition
    | apply Ref.eq_refl].
Qed.

Theorem potTransfer_ag_add_cap_by_obj_index_std_read: forall ag ag' i o s cap w src,
   SC.is_alive o s ->
   SC.getCap w src s = Some cap ->
   CC.hasRight cap AccessRights.rd ->
   Ref.eq (Cap.target cap) o ->
   dirAcc_spec s ag ->
   Seq.potTransfer ag ag' ->
   Seq.potTransfer ag (ag_add_cap_by_obj_index src o i s (fun c => c) ag_add_cap_valid_std ag').
Proof.
  intros ag ag' i o s cap w src Hwitness_alive Hcap Hright Htarget Hda HpotTransfer.
  reduce_potTransfer_ag_add_cap_by_obj_index i o s src ag_add_cap_valid_std.
  unfold ag_add_cap_mod; unfold ag_add_cap.
  eapply ARSetProps.fold_rec_nodep; auto.
  intros rgt ag2; intros.
  eapply Seq.potTransfer_trans; [apply H0|].
  (* reduce out ag_add_cap_valid_std *)
   eapply andb_true_iff in Hvalid; destruct Hvalid as [Halive_dec Htarget_alive_dec].
   eapply true_bool_of_sumbool_l in Halive_dec.
   eapply true_bool_of_sumbool_l in Htarget_alive_dec.


  (* read case *)
  eapply Seq.transfer_read with (rgt:=rgt) (src:=src) (tgt:=o) (tgt':= (Cap.target cap0)).
  (* mkEdge o src read *)
  eapply (Seq.potTransfer_subset H0).
  eapply dirAcc_simpl; [
   (* dirAcc *)
   apply Hda
   (* is_alive src s*)
   | auto
   (* getcap w o s*)
   | apply Hcap
   (* src [=] (Cap.target cap) *)
   | apply Ref.eq_sym; eauto
   (* is_alive o s *)
   | auto
   (* hasRight cap write *)
   | eauto].
  (* mkEdge o (Cap.target cap0) rgt *)  
  eapply (Seq.potTransfer_subset H0).
  eapply dirAcc_simpl; [
   (* dirAcc *)
   apply Hda
   (* is_alive o s*)
   | auto
   (* getcap _ o s*)
   | eauto
   (* (Cap.target cap0) [=] (Cap.target cap0) *)
   | auto (* apply Hf_target *)
   (* is_alive (Cap.target cap0) s *)
   | auto 
   (* hasRight cap0 rgt *)
   | auto ]; apply Ref.eq_refl.
  (* Add_add *)
  eapply AGProps.Add_add.
Qed.

Theorem potTransfer_ag_add_cap_by_obj_index_std_weak: forall ag ag' i o s cap w src,
   SC.is_alive o s ->
   SC.getCap w src s = Some cap ->
   CC.hasRight cap AccessRights.wk ->
   Ref.eq (Cap.target cap) o ->
   dirAcc_spec s ag ->
   Seq.potTransfer ag ag' ->
   Seq.potTransfer ag (ag_add_cap_by_obj_index src o i s Cap.weaken ag_add_cap_valid_std ag').
Proof.
  intros ag ag' i o s cap w src Hwitness_alive Hcap Hright Htarget Hda HpotTransfer.
  reduce_potTransfer_ag_add_cap_by_obj_index i o s src ag_add_cap_valid_std.
  unfold ag_add_cap_mod; unfold ag_add_cap.
  eapply ARSetProps.fold_rec_nodep; auto.
  intros rgt ag2; intros.
  eapply Seq.potTransfer_trans; [apply H0|].
  (* reduce out ag_add_cap_valid_std *)
   eapply andb_true_iff in Hvalid; destruct Hvalid as [Halive_dec Htarget_alive_dec].
   eapply true_bool_of_sumbool_l in Halive_dec.
   eapply true_bool_of_sumbool_l in Htarget_alive_dec.
  (* show target-weaken is target *)
  assert (Ref.eq (Cap.target (Cap.weaken cap0)) (Cap.target cap0)) as Hf_target.
  eapply CC.weaken_target_eq.
  (* we need two theorems here *)
  (* first: In rgt (rights (weaken cap)) -> rgt = weak
     second: In weak (rights (weaken cap)) -> In read (rights cap) \/ In weak (rights cap) *)

  generalize (CC.In_weak_weaken _ _ H); intros Hrgt.
  generalize H; intros H'.
  rewrite Hrgt in H'.
  eapply CC.In_weaken_singleton in H'.
  eapply CC.weaken_rights_weak_eq in H'.
  destruct H' as [H' | H'];
  (* weak case *)
  (eapply Seq.transfer_weak with (src:=src) (tgt:=o) (tgt':=(Cap.target (Cap.weaken cap0))); [
  (* mkEdge o src read *)
  eapply (Seq.potTransfer_subset H0);
  eapply dirAcc_simpl; [
   (* dirAcc *)
      apply Hda
   (* is_alive src s*)
    | auto
   (* getcap w src s *)
    | apply Hcap
   (* o [=] (Cap.target cap) *)
    | apply Ref.eq_sym; eauto
   (* is_alive o s *)
    | auto
   (* hasRight cap write *)
    | eauto]
  (* mkEdge o (Cap.target cap0) rgt *)  
  |eapply (Seq.potTransfer_subset H0);
  eapply dirAcc_simpl; [
   (* dirAcc *)
      apply Hda
   (* is_alive o s*)
    | auto
   (* getcap i o s*)
    | eauto
   (* (Cap.target cap0) [=] (Cap.target cap0) *)
    | apply Hf_target
   (* is_alive (Cap.target cap0) s *)
    | eapply SC.isAlive_eq; [eapply Ref.eq_sym; eapply Hf_target | eapply Sys.eq_refl | auto]
   (* hasRight cap0 _ *)
    | unfold CC.hasRight; apply H']
   (* weak | read *)
    |intuition
   (* Add_add *)
    |rewrite Hrgt; eapply AGProps.Add_add]).
Qed.

Theorem potTransfer_fetch_dep_ag: forall a t ixi_list s ag ag',
  dirAcc_spec s ag ->
  SemDefns.fetch_preReq a t s ->
  Seq.potTransfer ag ag' ->
  Seq.potTransfer ag (fetch_dep_ag a t ixi_list s ag').
Proof.
  intros.
  unfold fetch_dep_ag.   unfold ag_add_cap_by_indirect_index.
  (* cases on hasRight_dec and getCap, discharge one by contradiction, another by auto *)
  destruct H0 as [Hpre Hfetch].
  case (SemDefns.option_hasRight_dec (SC.getCap t a s) AccessRights.rd); intros HhasRight;
  (case ( option_sumbool (SC.getCap t a s)); intros Hcap; [|destruct Hcap as [cap Hcap]]; 
    try rewrite Hcap in *; simpl in *); try contradiction; auto.
  (* we are left with the two interesting cases of ag_add_cap_by_obj_index:
     one with read, and one with weaken *)
eapply potTransfer_ag_add_cap_by_obj_index_std_read; eauto; try apply Ref.eq_refl.
unfold SemDefns.preReq in *; unfold SemDefns.preReqCommon in *; unfold SemDefns.target_is_alive in *.
rewrite Hcap in *; simpl in *; intuition.
(* weak case *)
destruct Hfetch as [Hfetch|Hfetch]; try contradiction.
  eapply potTransfer_ag_add_cap_by_obj_index_std_weak; eauto; try apply Ref.eq_refl.
  destruct Hpre as [_ Ht].
  unfold SemDefns.target_is_alive in Ht; rewrite Hcap in Ht; simpl in *; auto.
Qed.

(* using the above theorems, we should be able to reduce every Fp operation to id except allocate. *)

(* moving on to allocate *)

  Theorem iff_or : forall A B C D : Prop,
   (C <-> D) -> (A <-> B \/ D) -> (A <-> B \/ C).
  Proof.
  intros.
  intuition.
  Qed.


(* BTW, this suggests that ag_add_commute -> ag_equiv and ag_nondecr,
   but I'm not sure how to prove that, and it's probably a diversion *)
Theorem  ag_fold_add_commute : forall F, Seq.ag_add_commute F ->
  forall ag a, AG.In a (F (AG.fold AG.add ag AG.empty)) <->
    AG.In a (F AG.empty) \/ AG.In a (AG.fold AG.add ag AG.empty).
Proof.
  intros F Hcomm ag a.
  eapply AGProps.fold_rec_nodep.
  (*base *)
  intuition.
  eapply AG.empty_1 in H0. contradiction.
  (* step *)
  intros a' ag' Hin IH.
  unfold Seq.ag_add_commute in *.
  eapply iff_trans. eapply Hcomm.  eapply AGProps.Add_add.
  (* again, given AGFacts.add_iff, AG.In a (AG.add a' ag') <-> a [=] a' \/ AG.In a ag' *)
  (* we need an iff over disjunction, to replace it, but then we have the IH with the case \/ a [] a' on
     both sides, clearly this is true, and we only used ag_add_commute. *)
  idtac.
  eapply iff_or. 
  eapply AGFacts.add_iff.
  intuition.
Qed.


Theorem  ag_multi_add_commute : forall F, Seq.ag_add_commute F -> Seq.ag_equiv F ->
forall ag, AG.Equal (F ag) (AG.union (F AG.empty) ag).
Proof.
  intros.
  unfold AG.Equal.
  intros.
  eapply iff_sym.  eapply iff_trans. eapply AGFacts.union_iff.
  eapply iff_sym.
  (* reduce to a fold *)
  intros.
  eapply iff_trans.
  eapply H0.
  eapply AG.eq_sym.
  eapply AGProps.fold_identity.
  (* this isn't entirely what we want, we need this theorem *)

  idtac.
  eapply iff_or. eapply iff_sym.
  eapply AGProps.fold_identity.
  eapply ag_fold_add_commute; eauto.
Qed.

(* TODO: This really should go into sequential access *)

Theorem add_commute_increasing_transpose : forall F F',
  Seq.ag_add_commute F -> Seq.ag_equiv F -> Seq.ag_add_commute F' -> Seq.ag_equiv F' ->
  forall ag ag', AG.Equal ag ag' -> AG.Equal (F (F' ag)) (F' (F ag')).
Proof.
  intros F F' Hf_1 Hf_3 Hf'_1 Hf'_3 ag ag' Heq.

(* reminder: ag_add_commute F := forall ag ag' x, AGProps.Add x ag ag' -> AGProps.Add x (F ag) (F ag') 
 That is: 
 forall ag ag' x, (forall y, In y ag' <-> E.eq x y \/ In y ag) -> 
                  (forall y, In y (F ag') <-> E.eq x y \/ In y (F ag)) *)
(* consider the diagram in Evernote "Transpose Strategy" allocated 2011-09-23 *)


generalize (ag_multi_add_commute _ Hf_1 Hf_3); intros HmF.
generalize (ag_multi_add_commute _ Hf'_1 Hf'_3); intros HmF'.
intro a.
generalize (HmF ag' a); intros.
generalize (HmF' (F ag') a); intros.
generalize (HmF' ag a); intros.  
generalize (HmF (F' ag) a); intros.
clear HmF HmF'.
eapply iff_sym in H; eapply iff_trans in H; [apply iff_sym in H| eapply iff_sym; eapply AGFacts.union_iff].
eapply iff_sym in H0; eapply iff_trans in H0; [apply iff_sym in H0| eapply iff_sym; eapply AGFacts.union_iff].
eapply iff_sym in H1; eapply iff_trans in H1; [apply iff_sym in H1| eapply iff_sym; eapply AGFacts.union_iff].
eapply iff_sym in H2; eapply iff_trans in H2; [apply iff_sym in H2| eapply iff_sym; eapply AGFacts.union_iff].
unfold AG.Equal in *.
eapply iff_trans. eapply H2.
eapply iff_sym.
eapply iff_or. eapply H1.
eapply iff_trans. eapply H0.
eapply iff_sym.
eapply iff_or. eapply H.
intuition (eauto; try apply Ref.eq_refl).
Qed.

Definition insert a n ag := 
  (ag_add_cap n (Cap.mkCap a all_rights) (ag_add_cap a (Cap.mkCap n all_rights) ag)).

Definition endow a n ag := (Seq.potAcc_fun (insert a n ag)).

Definition potAcc_approx_dirAcc_dep Fsa Fp := forall i i' p p' p2 s s' s'',
  Sys.eq s s' -> 
  Sys.eq s' s'' ->
  dirAcc_spec s i -> AG.Subset i i' -> 
  Seq.potAcc i' p -> Seq.potAcc (Fsa s' i') p2 ->
  AG.Subset p p' -> AG.Subset p2 (Fp s'' p').


Theorem allocate_reduce_to_add: forall a n ixi_list s s' i i' p,
  dirAcc_spec s i -> AG.Subset i i' -> Sys.eq s s' ->
  Seq.potAcc (ag_add_cap a (Cap.mkCap n all_rights)
               (ag_add_caps_by_index_pair_list n a ixi_list s'
                 (fun c : Cap.t => c) ag_add_cap_valid_allocate i')) p ->
  SemDefns.allocate_preReq a n s' ->
  Seq.potAcc (ag_add_cap a (Cap.mkCap n all_rights) i') p.
Proof.
  intros a n ixi_list s s' i i' p Hda Hi' Hs' Hpa.
  unfold Seq.potAcc in *.  destruct Hpa as [Hpa Hpa']; split; auto; clear Hpa'.
  (*unfold allocate_dep_ag in *;*) unfold ag_add_caps_allocate in *.
  (* Generalzie the problem, but allow for unfolding later *)
  revert Hpa.
  (*case (SemDefns.allocate_preReq_dec a n s'); intros Hc; try (apply Hc in H; contradiction); clear Hc.*)
  set (f := ag_add_caps_by_index_pair_list n a ixi_list s' (fun c => c) ag_add_cap_valid_allocate);
  set (f' := (ag_add_cap a (Cap.mkCap n all_rights)));
  intros Hpa.
  (* now that we can refer to each function as f and f', the following will thranspose them in H. *)
  eapply Seq.potTransfer_eq with (i':=(f (f' i'))) in Hpa;
  [| eapply add_commute_increasing_transpose;
        [eapply ag_add_cap_add_commute|
           unfold Seq.ag_equiv; intros; eapply ag_add_cap_equiv; eauto; try apply Ref.eq_refl|
           eapply ag_add_caps_by_index_pair_list_add_commute|
           unfold Seq.ag_equiv; intros; eapply ag_add_caps_by_index_pair_list_equiv; eauto; try apply Ref.eq_refl;
              try apply Sys.eq_refl; try (destruct CIL_Facts.cil_Equiv as [refl _ _]; eapply refl)|
           eauto]
   | auto].
  (* Having transposed the f and f', eliminate the common (f' i) using potTransfer_transitive *)
  eapply Seq.potTransfer_transitive with (a := f' i') in Hpa; auto; clear Hpa.
  (* We need to demonstrate that f can be transed from f'. *)
  (* This may want to be a new theorem. *)
  (* This theorem uses AccessRights.tx to demonstrate that any copying can occur. *)
  Theorem potTransfer_ag_add_caps_by_index_pair_list_allocate: forall a ixi_list n s s' i i' ag,
  Sys.eq s s' ->
  dirAcc_spec s i ->
  AG.Subset i i' ->
  AG.In (Edges.mkEdge a n AccessRights.tx) i' ->
  Seq.potTransfer i' ag ->
  SC.is_alive a s ->
  Seq.potTransfer i'
    (ag_add_caps_by_index_pair_list n a ixi_list s' (fun c => c) ag_add_cap_valid_allocate ag).
  Proof.
  intros.
  unfold ag_add_caps_by_index_pair_list.
  induction ixi_list; simpl; auto.
  Theorem potTransfer_ag_add_cap_by_obj_index_allocate: forall ag ag' n a i s s' ag_d,
    Sys.eq s s' ->
    dirAcc_spec s ag_d ->
    AG.Subset ag_d ag ->
    AG.In (Edges.mkEdge a n AccessRights.tx) ag ->
    Seq.potTransfer ag ag' ->
    SC.is_alive a s ->
    Seq.potTransfer ag
     (ag_add_cap_by_obj_index n a i s'
        (fun c : Cap.t => c) ag_add_cap_valid_allocate ag').
  Proof.
    intros.
    unfold ag_add_cap_by_obj_index.
    reduce_potTransfer_ag_add_cap_by_obj_index i a s' n ag_add_cap_valid_allocate.
    unfold ag_add_cap_mod; unfold ag_add_cap.
    eapply ARSetProps.fold_rec_nodep; auto.
    intros rgt ag2; intros.
    eapply Seq.potTransfer_trans; [apply H6 |].
    eapply Seq.transfer_send; [| |eapply AGProps.Add_add].
      eapply Seq.potTransfer_subset; [apply H6 | eapply H2].
      eapply Seq.potTransfer_subset; [apply H6 | eapply AGProps.subset_trans; [eapply H1 | eauto |]].
        (* FIXME: go back and use this support theorm where you generalize SC.getCap_eq everywhere for legibility*)
      (* TODO: delete, duplicate in SystemState_ConvImpl.v*)
        Theorem getCap_eq_Some: forall {i i' o o' s s' cap},
          Ind.eq i i' ->
          Ref.eq o o' ->
          Sys.eq s s' ->
          SC.getCap i o s = Some cap ->
          exists cap', SC.getCap i' o' s' = Some cap' /\ Cap.eq cap cap'.
        Proof.
          intros.
          generalize (SC.getCap_eq _ _ _ _ _ _ H1 H H0); intros HEq.
          rewrite H2 in HEq.
          case (option_sumbool (SC.getCap i' o' s')); intros Hcase; [|destruct Hcase as [cap' Hcase]];
          rewrite Hcase in HEq; simpl in *; try contradiction.
          eapply ex_intro.
          split; eauto.          
        Qed.
      idtac.
      generalize (getCap_eq_Some (Ind.eq_refl i) (Ref.eq_refl a) (Sys.eq_sym H) Hcap); intros [cap' [H7 H8]].

      eapply dirAcc_simpl.
        apply H0.
        apply H4.
        apply H7.
        apply Cap.target_eq; auto.
        eapply SC.isAlive_eq; [eapply Cap.target_eq; auto| eauto | apply true_bool_of_sumbool_l in Hvalid; auto].
        eapply Cap.rights_eq; [eapply Cap.eq_sym; eauto | auto].
  Qed.
  (* if the above is admitted, the following solves the proof *)
  eapply potTransfer_ag_add_cap_by_obj_index_allocate; eauto.
  Qed.
  (* if the above is admitted, the following solves the proof *)
  idtac.
  eapply potTransfer_ag_add_caps_by_index_pair_list_allocate.
  eapply Hs'.
  eapply Hda.
  eapply ag_add_cap_nondecr; auto.
  eapply ag_add_cap_spec.
  eapply AG.eq_refl.
  left; intuition eauto; try rewrite CC.mkCap_target; try rewrite Edges.target_rewrite;
    try rewrite Edges.right_rewrite; try rewrite CC.mkCap_rights; try apply Ref.eq_refl.

  (* Toss into the AccessRights library *)
  Theorem in_all_rights : forall r, ARSet.In r all_rights.
  Proof.
    intros; destruct r; unfold all_rights; ARSetFacts.set_iff; auto; try apply Ref.eq_refl; right.
  Qed.
  Hint Resolve in_all_rights.
  eauto.
  eapply Seq.potTransfer_base. eapply ag_add_cap_equiv; auto; try apply Ref.eq_refl; try eapply AG.eq_refl.
  destruct H. destruct H. eapply SC.isAlive_eq; eauto; try apply Ref.eq_refl.
Qed.

(* given our changes, this property will go through.  However, I am now concerned about the fact that
   we are propigating the same problem from dirAcc_approx to potAcc_approx.  We are conservatively approximating
   a failed allocate with a successful one. *)

Definition endow_dep a n s := if SemDefns.allocate_preReq_dec a n s then endow a n else fun ag => ag.

Theorem potAcc_approx_allocate : forall a n ixi_list,
 potAcc_approx_dirAcc_dep (allocate_dep_ag a n ixi_list) (endow_dep a n).
Proof.
  unfold potAcc_approx_dirAcc_dep.
  unfold endow_dep in *; unfold endow in *;  unfold insert in *.
  unfold allocate_dep_ag in *; unfold ag_add_caps_allocate in *. intros a n ixi_list i i' p p' p2 s s' s''.
  Ltac allocate_preReq_eq_contradict Hc Hc':= try (eapply SemDefns.allocate_preReq_eq_iff in Hc ; [eapply Hc' in Hc | | |]; auto; try apply Ref.eq_refl; contradiction).
  case (SemDefns.allocate_preReq_dec a n s'); intros Hc;
  case (SemDefns.allocate_preReq_dec a n s''); intros Hc'; intros;
    allocate_preReq_eq_contradict Hc Hc'; allocate_preReq_eq_contradict Hc' Hc.
  eapply allocate_reduce_to_add in H4; [| apply H1|apply H2|eapply H| eapply Hc]. 
  (* case potAcc_fun *)
  revert H4.
  set (f := ag_add_cap a (Cap.mkCap n all_rights)).
  set (f' := ag_add_cap n (Cap.mkCap a all_rights)).
  intros H4.
  destruct H3 as [H3 H3']. apply Seq.potTransfer_subset in H3.

  (* i' [<=] p [<=] p' by transitivity. *)
  (* Therefore, by ag_add_cap_subset_commute[eapply] (f i') [<=] (f p')  *)
  (* by ag_add_cap_nondecr (f p') [<=] (f' (f p')), 
      and by potAcc_subset_commute[prove add_commute] (potAcc (f p')) [<=] (potAcc (f' (f p')))  *)

  assert (AG.Subset (f i') (f' (f p'))).
  eapply AGProps.subset_trans.
  eapply Seq.ag_subset_add_commute with (Fa := f).
    apply ag_add_cap_add_commute.
    unfold Seq.ag_equiv; intros; eapply ag_add_cap_equiv; eauto; try apply Ref.eq_refl.
    eapply AGProps.subset_trans; [apply H3| eapply H5].
  eapply ag_add_cap_nondecr; auto.

  eapply Seq.potAcc_eq_potAcc_fun in H4.
  eapply AGProps.subset_trans.  eapply AGProps.subset_equal; eapply H4.

Theorem potAcc_fun_subset_commute: Seq.ag_subset_commute Seq.potAcc_fun.
Proof.
  unfold Seq.ag_subset_commute. intros.
  eapply Seq.potAcc_monotonic.
    apply H.
    apply Seq.potAcc_potAcc_fun.
    apply Seq.potAcc_potAcc_fun.
Qed.
  eapply potAcc_fun_subset_commute; auto.
  (* case where nothing happens *)
  eapply AGProps.subset_trans; [eapply AGProps.subset_equal| eapply H5].

(* move to sequential access *)

Theorem potAcc_equiv: forall i i' p p', AG.Equal i i' -> Seq.potAcc i p -> Seq.potAcc i' p' -> AG.Equal p p'.
Proof.
  intros.
  destruct H0 as [H0 H0']; destruct H1 as [H1 H1']. 
  eapply Seq.potTransfer_equality_full in H1; [|eapply AG.eq_sym; eapply H| eapply AG.eq_refl].
  generalize (Seq.potTransfer_lub H0 H1); intros [c [H2 H2']].
  eapply H1' in H2.
  eapply H0' in H2'.
  eapply AG.eq_trans. eapply H2'. eapply AG.eq_sym; eapply H2.
Qed.
idtac.
eapply potAcc_equiv; [eapply AG.eq_refl | eapply H4 | eapply H3].
Qed.

(* Recall that accessgraphs do not encode the notion of infinitely many self-loops, so our reduction
   clause must account for this. *)

Definition AG_attenuating N p p' := forall src tgt, RefSet.In src N -> RefSet.In tgt N ->
  forall rgt, ~ AG.In (Edges.mkEdge src tgt rgt) p -> 
     Ref.eq src tgt \/ ~ AG.In (Edges.mkEdge src tgt rgt) p'.

(* old definition *)
(* Definition AG_attenuating p p' := forall objs, Seq.ag_objs_spec p objs ->  *)
(*   forall src tgt, RefSet.In src objs -> RefSet.In tgt objs -> *)
(*   forall rgt, ~ AG.In (Edges.mkEdge src tgt rgt) p -> ~ AG.In (Edges.mkEdge src tgt rgt) p'. *)


Theorem AG_attenuating_trans : forall N p p' p'', AG_attenuating N p p' -> AG_attenuating N p' p'' -> AG_attenuating N p p''.
Proof.
  unfold AG_attenuating; intros.
  apply H in H3; auto.
  destruct H3 as [H3 | H3]; [solve [intuition auto] |].
  apply H0 in H3; auto.
Qed.

Theorem AG_attenuating_subset_objs: forall N N' p p', AG_attenuating N p p' -> RefSet.Subset N' N -> AG_attenuating N' p p'.
Proof.
  unfold AG_attenuating; intros; auto.
Qed.

Theorem AG_attenuating_subset_ag: forall N p p',  AG.Subset p' p -> AG_attenuating N p p'.
Proof.
  unfold AG_attenuating; intros; auto.
Qed.

Hint Resolve AG_attenuating_trans AG_attenuating_subset_objs AG_attenuating_subset_ag.

Theorem AG_attenuating_trans_subset: forall N p p' N' p'', AG_attenuating N p p' -> AG_attenuating N' p' p'' -> RefSet.Subset N N' -> AG_attenuating N p p''.
Proof.
  intros; eauto.
Qed.

  Theorem ag_Equal_if_eq: forall ag ag',
    AG.eq ag ag' -> AG.Equal ag ag'.
  Proof.
    eauto.
  Qed.


  Theorem AG_all_objs_add_cap: forall A B N a n N',
    Seq.AG_all_objs A N -> AG.Equal (ag_add_cap a (Cap.mkCap n all_rights) A) B ->
    RefSet.Subset N N' -> RefSet.In n N' -> RefSet.In a N' -> 
    Seq.AG_all_objs B N'.
  Proof.
    intros.    
    unfold ag_add_cap in *.
    revert H0.
    revert B.
    eapply ARSetProps.fold_rec_bis with
     (P:= fun s f => forall B, AG.Equal f B -> Seq.AG_all_objs B N'); intros; try solve [intuition auto].
    (* base *)
    esplit; eapply H1; eauto.
    (* step *)
    rename a0 into B'.
    eapply Seq.AG_all_objs_Add; [eapply H5; eapply AG.eq_refl | | eapply RefSetFacts.Subset_refl| eapply H3| eapply H2].
    rewrite CC.mkCap_target in H6.
    eapply AGAddEq.Add_eq. apply H6.
    eapply AGProps.Add_add.
  Qed.


  Theorem ag_objs_spec_insert: forall A N, Seq.ag_objs_spec A N -> 
    forall a n B, AG.Equal (insert a n A) B ->
    forall N', Seq.ag_objs_spec B N' ->
    forall x, RefSet.In x N' -> ~ Ref.eq x a -> ~ Ref.eq x n -> RefSet.In x N.
  Proof.
    intros.    
    unfold insert in *.
    eapply ag_objs_spec_add_cap;
      [eapply H | eapply AG.eq_refl| eapply Seq.ag_objs_spec_ag_objs| | apply H3 | apply H4].
    (* eauto is throwing errors, likely due to applying the wrong hypothesis first as there are
       existentials floating about. *)
    eapply ag_objs_spec_add_cap; [eapply Seq.ag_objs_spec_ag_objs | eauto | eauto | auto | eapply H4| eapply H3].
  Qed.


Theorem AG_all_objs_insert : forall ag N, Seq.AG_all_objs ag N -> 
  forall a n ag', AG.Equal (insert a n ag) ag' -> 
  forall b, Seq.potTransfer ag' b ->
  forall N', RefSet.Subset N N' -> RefSet.In a N' -> RefSet.In n N' -> 
  Seq.AG_all_objs b N'.
Proof.
  intros.
  eapply Seq.ag_all_objs_potTransfer in H1; eauto.  clear H1; clear b.
  (* move this to sequential access *)
  unfold insert in *.
  eapply AG_all_objs_add_cap; try solve [apply H0| apply RefSetFacts.Subset_refl| apply H3 | apply H4].
  eapply AG_all_objs_add_cap;  try solve [apply H2 | apply AG.eq_refl | apply H3 | apply H4 | apply H].
Qed.

(* I'm not sure we can get this far with AG_all_objs, we may need to simply start with that:
   Seq.AG_all_objs ag N -> AG.Equal (insert a n ag) ag' -> Seq.AG_all_objs ag' N' ->
   In x N' -> ~ x[=]a -> ~ x[=]n -> In x N. 
   This probably all requires ag_objs_spec.*)

Theorem ag_objs_spec_transfer_2: forall A B, Seq.transfer A B -> 
  forall N, (Seq.ag_objs_spec A N <-> Seq.ag_objs_spec B N).
Proof.
    intros; split; intros.
    generalize (@Seq.fold_AG_complete_ag N); set (C:=(Seq.complete_ag N));intros H1.
    generalize (Seq.ag_objs_spec_AG_all_objs H0); intros H'.
    generalize (Seq.transfer_in_complete H' H1 H); intros [edge [H2 H3]].
    unfold Seq.ag_objs_spec; intros.
    rewrite <- (Edges.edge_rewrite edge) in *.
    split; intros.
    (* case one *)
    unfold Seq.AG_all_objs in *.
    unfold Seq.ag_objs_spec in *.
    eapply H0 in H4.
    destruct H4 as [obj [rgt [H4 | H4]]];
    edestruct H2 as [_ H2']; simpl in *;
    do 2 eapply ex_intro; [left|right]; (eapply H2'; right; apply H4).
    (* other case *)
    destruct H4 as [obj [rgt [H4 | H4]]];
    (eapply H2 in H4; simpl in *;
    destruct H4 as [[H4 [H5 H6]] | H4]; [| eapply (H' _ _ _ H4)];
    rewrite H4 in *; rewrite H5 in *; rewrite H6 in *; clear H4 H5 H6;
    apply (Seq.complete_AG_conv_complete_ag N H3)).

    (* other split *)
    unfold Seq.ag_objs_spec in *; intros.
    generalize (H0 x); clear H0; intros H0.
    eapply iff_trans.
    eapply H0. 
    clear H0.
    rename H into Htrans.
    split.

    intros [obj [rgt [H|H]]];
    (* goal 1 *)
    destruct Htrans;
    try (first [eapply H1 in H| eapply H2 in H | eapply H3 in H];
      simpl in *; destruct H as [H | H]; [
      generalize (Edges.eq_source _ _ H); intros H'; do 2 rewrite Edges.source_rewrite in H';
      generalize (Edges.eq_target _ _ H); intros H''; do 2 rewrite Edges.target_rewrite in H'';
      generalize (Edges.eq_right _ _ H); intros H'''; do 2 rewrite Edges.right_rewrite in H''';
        try rewrite H' in *; try rewrite H'' in *; try rewrite H''' in * |];
    do 2 eapply ex_intro; 
      solve [left; eapply H0 | right; eapply H0
        | left; eapply H | right; eapply H
        | left; eapply H1 | right; eapply H1]).
    (* goal 2 *)
    intros [obj [rgt [H|H]]];
    (apply Seq.transfer_subset in Htrans;
    apply Htrans in H;
    do 2 eapply ex_intro; solve [left; eapply H | right; eapply H]).
Qed.

Hint Resolve ag_objs_spec_transfer_2.


  Theorem ag_objs_spec_transfer: forall A N B, Seq.ag_objs_spec A N -> Seq.transfer A B -> Seq.ag_objs_spec B N.
  Proof.
    intros.
    eapply ag_objs_spec_transfer_2 with (A:=A); auto.
  Qed.

  Hint Resolve ag_objs_spec_transfer.


    Theorem ag_objs_spec_eq: forall A A' N N', 
      RefSet.Equal N N' -> AG.Equal A A' -> (Seq.ag_objs_spec A N <-> Seq.ag_objs_spec A' N').
    Proof.
      intros.
      unfold Seq.ag_objs_spec in *.
      split; intros;
        (eapply iff_trans; [solve [eapply iff_sym; eapply H| eapply H] |];
          eapply iff_trans; [eapply H1|];
            split;
              (intros [obj [rgt [H2 | H2]]];
                do 2 eapply ex_intro; [left|right]; (eapply H0; apply H2))).
    Qed.

    Theorem ag_objs_spec_potTransfer_2: forall A B, 
      Seq.potTransfer A B -> forall N, (Seq.ag_objs_spec A N <-> Seq.ag_objs_spec B N).
    Proof.
      intros; split; intros.
      (* case 1 *)
    induction H; eauto.
    eapply ag_objs_spec_eq.
    apply RefSet.eq_refl.
    apply AG.eq_sym; apply H.
    auto.
    (* case 2 *)
    induction H; eauto.
    (* base *)
    eapply ag_objs_spec_eq.
    apply RefSet.eq_refl.
    apply H; auto.
    auto.
    (* step *)
    eapply IHpotTransfer; clear IHpotTransfer.
    eapply ag_objs_spec_transfer_2 in H0; eauto.
    Qed.

    Hint Resolve ag_objs_spec_potTransfer_2.

  Theorem ag_objs_spec_potTransfer: forall A N B, 
    Seq.ag_objs_spec A N -> Seq.potTransfer A B -> Seq.ag_objs_spec B N.
  Proof.
    intros; eapply ag_objs_spec_potTransfer_2 with (A:=A); auto.
  Qed.

  Hint Resolve ag_objs_spec_potTransfer.

Theorem maxTransfer_in_by_tgt_read: forall p, Seq.maxTransfer p -> forall src a,
  AG.In (Edges.mkEdge src a AccessRights.rd) p -> forall rgt, AG.In (Edges.mkEdge src a rgt) p.
Proof.
  intros.
  eapply H.
    eapply Seq.transfer_read.
      eapply H0.
      eapply H.
        eapply Seq.transfer_self_tgt.
          eapply H0.
          eapply AGProps.Add_add.  
        eapply AGProps.Add_add; simpl; left; eauto.
      eapply AGProps.Add_add.
    eapply AGProps.Add_add; simpl; left; eauto.
Qed.

Theorem maxPotTransfer_in_by_tgt_read: forall p, Seq.maxPotTransfer p -> forall src a,
  AG.In (Edges.mkEdge src a AccessRights.rd) p -> forall rgt, AG.In (Edges.mkEdge src a rgt) p.
Proof.
intuition auto; apply maxTransfer_in_by_tgt_read; auto; eapply Seq.maxTransfer_maxPotTransfer; auto.
Qed.
Hint Resolve maxPotTransfer_in_by_tgt_read.


Theorem maxTransfer_in_by_src_write: forall p, Seq.maxTransfer p -> forall tgt a,
  AG.In (Edges.mkEdge a tgt AccessRights.wr) p -> forall rgt, AG.In (Edges.mkEdge tgt a rgt) p.
Proof.
  intros.
  eapply H.
    eapply Seq.transfer_write.
      eapply H0.
      eapply H.
        eapply Seq.transfer_self_src.
          eapply H0.
          eapply AGProps.Add_add.  
        eapply AGProps.Add_add; simpl; left; eauto.
      eapply AGProps.Add_add.
    eapply AGProps.Add_add; simpl; left; eauto.
Qed.

Theorem maxPotTransfer_in_by_src_write: forall p, Seq.maxPotTransfer p -> forall tgt a,
  AG.In (Edges.mkEdge a tgt AccessRights.wr) p -> forall rgt, AG.In (Edges.mkEdge tgt a rgt) p.
Proof.
intros; apply maxTransfer_in_by_src_write; auto; eapply Seq.maxTransfer_maxPotTransfer; auto.
Qed.
Hint Resolve maxPotTransfer_in_by_src_write.

Theorem maxTransfer_in_by_src_send: forall p, Seq.maxTransfer p -> forall tgt a,
  AG.In (Edges.mkEdge a tgt AccessRights.tx) p -> forall rgt, AG.In (Edges.mkEdge tgt a rgt) p.
Proof.
  intros.
  eapply H.
    eapply Seq.transfer_send.
      eapply H0.
      eapply H.
        eapply Seq.transfer_self_src.
          eapply H0.
          eapply AGProps.Add_add.  
        eapply AGProps.Add_add; simpl; left; eauto.
      eapply AGProps.Add_add.
    eapply AGProps.Add_add; simpl; left; eauto.
Qed.

Theorem maxPotTransfer_in_by_src_send: forall p, Seq.maxPotTransfer p -> forall tgt a,
  AG.In (Edges.mkEdge a tgt AccessRights.tx) p -> forall rgt, AG.In (Edges.mkEdge tgt a rgt) p.
Proof.
intros; apply maxTransfer_in_by_src_send; auto; eapply Seq.maxTransfer_maxPotTransfer; auto.
Qed.
Hint Resolve maxPotTransfer_in_by_src_send.


Theorem maxTransfer_in_by_tgt_weak: forall p, Seq.maxTransfer p ->
  forall src a, AG.In (Edges.mkEdge src a AccessRights.wk) p -> AG.In (Edges.mkEdge src a AccessRights.wk) p.
Proof.
  intros.
  eapply H.
    eapply Seq.transfer_weak.
      eapply H0.
      eapply H.
        eapply Seq.transfer_self_tgt.
          eapply H0.
          eapply AGProps.Add_add.  
        eapply AGProps.Add_add; simpl; left; eauto.
        auto.
      eapply AGProps.Add_add.
    eapply AGProps.Add_add; simpl; left; eauto.
Qed.

Theorem maxPotTransfer_in_by_tgt_weak: forall p, Seq.maxPotTransfer p -> forall src a,
  AG.In (Edges.mkEdge src a AccessRights.wk) p -> AG.In (Edges.mkEdge src a AccessRights.wk) p.
Proof.
intuition auto; apply maxTransfer_in_by_tgt_weak; auto; eapply Seq.maxTransfer_maxPotTransfer; auto.
Qed.
Hint Resolve maxPotTransfer_in_by_tgt_read. 


(* this should really be iff in the last impl, but we want to focus on the hard case first *)
Theorem endow_spec_1 : forall a n ag p ag' p' N, 
  Seq.potAcc ag p -> Seq.ag_objs_spec p N -> ~ RefSet.In n N -> 
  AG.Equal (insert a n p) ag' -> Seq.potAcc ag' p' -> 
  forall src tgt rgt, 
   AG.In (Edges.mkEdge src tgt rgt) p' ->
    (AG.In (Edges.mkEdge src tgt rgt) p \/ 
     AG.In (Edges.mkEdge src a rgt) p /\ Ref.eq tgt n \/ 
     AG.In (Edges.mkEdge a tgt rgt) p /\ Ref.eq src n \/
     Ref.eq src n /\ Ref.eq tgt a \/
     Ref.eq src a /\ Ref.eq tgt n \/
     Ref.eq src n /\ Ref.eq tgt n \/
     Ref.eq src a /\ Ref.eq tgt a).
Proof.
  intros a n ag p ag' p' N Hpa Hobjs Hnin Heq Hpa' src tgt rgt Hin.
  destruct Hpa' as [Htr' _].
  revert Hin;  revert src tgt rgt.
  induction Htr'; intros src tgt rgt Hin.
  (* base case *)
  eapply AG.eq_trans in H; [| eapply Heq].
  unfold insert in H.
  eapply ag_Equal_if_eq in H.
  eapply H in Hin; clear H.
  eapply ag_add_cap_spec_b in Hin; [|eapply AG.eq_refl].
  destruct Hin as [Hin | Hin]; [destruct Hin as [Hin1 [Hin2 Hin3]]|].
  (* case first add *)
  (* clean up *)
  rewrite Edges.source_rewrite in *.
  rewrite Edges.target_rewrite in *.
  rewrite Edges.right_rewrite in *.
  rewrite CC.mkCap_target in *.
  eapply (CC.mkCap_rights _ all_rights) in Hin3.
  do 3 right; left; split; try apply Ref.eq_sym; auto.
  (* case second add *)
  eapply ag_add_cap_spec_b in Hin; [|eapply AG.eq_refl].    
  destruct Hin as [Hin | Hin]; [destruct Hin as [Hin1 [Hin2 Hin3]]|].
  (* second add reduced *)
  (* clean up *)
  rewrite Edges.source_rewrite in *.
  rewrite Edges.target_rewrite in *.
  rewrite Edges.right_rewrite in *.
  rewrite CC.mkCap_target in *.
  eapply (CC.mkCap_rights _ all_rights) in Hin3.
  do 4 right; left; split; apply Ref.eq_sym; auto.
  (* remainder *)
  left; auto.
  (* inductive step *)
  destruct H.
  (* case: transfer self src *)
  eapply H0 in Hin; simpl in Hin.
  destruct Hin as [HeqE |Hin]; try solve [intuition auto].
  generalize (Edges.eq_source _ _ HeqE); intros HeqS; do 2 rewrite Edges.source_rewrite in HeqS;
    generalize (Edges.eq_target _ _ HeqE); intros HeqT; do 2 rewrite Edges.target_rewrite in HeqT;
      generalize (Edges.eq_right _ _ HeqE); intros HeqR; do 2 rewrite Edges.right_rewrite in HeqR.
  generalize H; intros H'.
  eapply IHHtr' in H'.
  unfold Ref.eq in HeqS; unfold Ref.eq in HeqT; unfold AccessRight.eq in HeqR;
  rewrite HeqS in *; rewrite HeqT in *; rewrite HeqR in *.
  clear IHHtr'.


  (* subcase 1 - 2: In (tgt _ _) p. Transfer_self_src on p with maxtransfer. *)
  (* subcase 3 - 7: tgt [=] n ; case tgt [=] n (x2) *)
  do 7 (try destruct H' as [H'' | H']); try rename H'' into H';
   try solve [intuition |
     left; destruct Hpa as [Htr Hm];
     eapply Hm;
       [eapply Seq.potTransfer_trans;
         [eapply Seq.potTransfer_base; eapply AG.eq_refl
         |eapply Seq.transfer_self_src; [eapply H'| eapply AGProps.Add_add]]
       |eapply AGProps.Add_add; simpl; eauto] ].
  (* case: transfer self tgt *)
  eapply H0 in Hin; simpl in Hin.
  destruct Hin as [HeqE |Hin]; try solve [intuition auto].
  generalize (Edges.eq_source _ _ HeqE); intros HeqS; do 2 rewrite Edges.source_rewrite in HeqS;
    generalize (Edges.eq_target _ _ HeqE); intros HeqT; do 2 rewrite Edges.target_rewrite in HeqT;
      generalize (Edges.eq_right _ _ HeqE); intros HeqR; do 2 rewrite Edges.right_rewrite in HeqR;
  unfold Ref.eq in HeqS; unfold Ref.eq in HeqT; unfold AccessRight.eq in HeqR.
  generalize H; intros H'.
  eapply IHHtr' in H'.
  rewrite HeqS in *; rewrite HeqT in *; rewrite HeqR in *.
  clear IHHtr'.
  (* subcase 1 - 2: In (tgt _ _) p. Transfer_self_tgt on p with maxtransfer. *)
  (* subcase 3 - 7: intuition *)
  do 7 (try destruct H' as [H'' | H']); try rename H'' into H'; 
   try solve [intuition |
     left; destruct Hpa as [Htr Hm];
     eapply Hm;
       [eapply Seq.potTransfer_trans;
         [eapply Seq.potTransfer_base; eapply AG.eq_refl
         |eapply Seq.transfer_self_tgt; [eapply H'| eapply AGProps.Add_add]]
       |eapply AGProps.Add_add; simpl; eauto] ].
  (* case: transfer read *)
  eapply H1 in Hin; simpl in Hin.
  destruct Hin as [HeqE |Hin]; try solve [intuition auto].
  generalize (Edges.eq_source _ _ HeqE); intros HeqS; do 2 rewrite Edges.source_rewrite in HeqS;
    generalize (Edges.eq_target _ _ HeqE); intros HeqT; do 2 rewrite Edges.target_rewrite in HeqT;
      generalize (Edges.eq_right _ _ HeqE); intros HeqR; do 2 rewrite Edges.right_rewrite in HeqR;
  unfold Ref.eq in HeqS; unfold Ref.eq in HeqT; unfold AccessRight.eq in HeqR.
  generalize H; intros H'.
  generalize H0; intros H0'.
  eapply IHHtr' in H'.
  eapply IHHtr' in H0'.
  rewrite HeqS in *; rewrite HeqT in *; rewrite HeqR in *.
  clear IHHtr'.


  do 7 (try destruct H' as [H'' | H']); try rename H'' into H';
  do 7 (try destruct H0' as [H'' | H0']); try rename H'' into H0';
    (* I'd rather not unfold Ref.eq, but it takes hours otherwise. *)
  try (unfold Ref.eq in H'; destruct H' as [H' Heq1]; try rewrite Heq1 in *; try rewrite H' in *);
  try (unfold Ref.eq in H0'; destruct H0' as [H0' Heq2]; try rewrite Heq2 in *; try rewrite H0' in *);
   try (unfold Ref.eq in *; solve [destruct Hpa as [Htr Hmax]; intuition auto
           |eapply Seq.not_in_ag_objs_spec_tgt in H'; try contradiction; try apply Hobjs; auto
           |eapply Seq.not_in_ag_objs_spec_src in H'; try contradiction; try apply Hobjs; auto
           |eapply Seq.not_in_ag_objs_spec_tgt in H0'; try contradiction; try apply Hobjs; auto
           |eapply Seq.not_in_ag_objs_spec_src in H0'; try contradiction; try apply Hobjs; auto]).
    (* 8 (4 new) cases *)
  left; destruct Hpa as [Htr Hm];
    eapply Hm;
      [eapply Seq.potTransfer_trans;
        [eapply Seq.potTransfer_base; eapply AG.eq_refl
        |eapply Seq.transfer_read;
          [eapply H'
          |eapply H0'
          |eapply AGProps.Add_add]]
      |eapply AGProps.Add_add; simpl; auto].
  right; left; split; auto; try apply Ref.eq_refl; destruct Hpa as [Htr Hm];
    eapply Hm.
      eapply Seq.potTransfer_trans.
        eapply Seq.potTransfer_base; eapply AG.eq_refl.
        eapply Seq.transfer_read.
          eapply H'.
          eapply H0'.
          eapply AGProps.Add_add .
      eapply AGProps.Add_add; simpl; auto .
(* case: (src a read) in p /\ (a tgt rgt) in p -> add (src tgt rgt).  duh *)
  left; destruct Hpa as [Htr Hm];
    eapply Hm;
      [eapply Seq.potTransfer_trans;
        [eapply Seq.potTransfer_base; eapply AG.eq_refl
        |eapply Seq.transfer_read;
          [eapply H'
          |eapply H0'
          |eapply AGProps.Add_add]]
      |eapply AGProps.Add_add; simpl; auto].
(* case: (a tgt0 read) in p /\ (tgt0 tgt rgt) in p -> add (n tgt rgt). (a tgt rgt) in p /\ n = n *)
  do 2 right; left; split; auto; try apply Ref.eq_refl; destruct Hpa as [Htr Hm];
    eapply Hm.
      eapply Seq.potTransfer_trans.
        eapply Seq.potTransfer_base; eapply AG.eq_refl.
        eapply Seq.transfer_read.
          eapply H'.
          eapply H0'.
          eapply AGProps.Add_add .
      eapply AGProps.Add_add; simpl; auto .
(* case: transfer write *)
 eapply H1 in Hin; simpl in Hin.
  destruct Hin as [HeqE |Hin]; try solve [intuition auto].
  generalize (Edges.eq_source _ _ HeqE); intros HeqS; do 2 rewrite Edges.source_rewrite in HeqS;
    generalize (Edges.eq_target _ _ HeqE); intros HeqT; do 2 rewrite Edges.target_rewrite in HeqT;
      generalize (Edges.eq_right _ _ HeqE); intros HeqR; do 2 rewrite Edges.right_rewrite in HeqR;
  unfold Ref.eq in HeqS; unfold Ref.eq in HeqT; unfold AccessRight.eq in HeqR.
  generalize H; intros H'.
  generalize H0; intros H0'.
  eapply IHHtr' in H'.
  eapply IHHtr' in H0'.
  rewrite HeqS in *; rewrite HeqT in *; rewrite HeqR in *.
  clear IHHtr'.

  do 7 (try destruct H' as [H'' | H']); try rename H'' into H';
  do 7 (try destruct H0' as [H'' | H0']); try rename H'' into H0';
(*  try solve [ *)
  try (unfold Ref.eq in H'; destruct H' as [H' Heq1]; try rewrite Heq1 in *; try rewrite H' in *);
  try (unfold Ref.eq in H0'; destruct H0' as [H0' Heq2]; try rewrite Heq2 in *; try rewrite H0' in *);
   try (unfold Ref.eq in *; solve [destruct Hpa as [Htr Hmax]; intuition auto
           |eapply Seq.not_in_ag_objs_spec_tgt in H'; try contradiction; try apply Hobjs; auto
           |eapply Seq.not_in_ag_objs_spec_src in H'; try contradiction; try apply Hobjs; auto
           |eapply Seq.not_in_ag_objs_spec_tgt in H0'; try contradiction; try apply Hobjs; auto
           |eapply Seq.not_in_ag_objs_spec_src in H0'; try contradiction; try apply Hobjs; auto])
(* ] *)
.
(* 7 (4 new) subgoals *)
left; destruct Hpa as [Htr Hm];
    eapply Hm;
      [eapply Seq.potTransfer_trans;
        [eapply Seq.potTransfer_base; eapply AG.eq_refl
        |eapply Seq.transfer_write;
          [eapply H'
          |eapply H0'
          |eapply AGProps.Add_add]]
      |eapply AGProps.Add_add; simpl; auto].
right; left; split; auto; try apply Ref.eq_refl; destruct Hpa as [Htr Hm];
    eapply Hm.
      eapply Seq.potTransfer_trans.
        eapply Seq.potTransfer_base; eapply AG.eq_refl.
        eapply Seq.transfer_write.
          eapply H'.
          eapply H0'.
          eapply AGProps.Add_add .
      eapply AGProps.Add_add; simpl; auto .
do 2 right; left; split; auto; try apply Ref.eq_refl; destruct Hpa as [Htr Hm];
    eapply Hm;
      [eapply Seq.potTransfer_trans;
        [eapply Seq.potTransfer_base; eapply AG.eq_refl
        |eapply Seq.transfer_write;
          [eapply H'
          |eapply H0'
          |eapply AGProps.Add_add]]
      |eapply AGProps.Add_add; simpl; auto].
left; destruct Hpa as [Htr Hm];
    eapply Hm;
      [eapply Seq.potTransfer_trans;
        [eapply Seq.potTransfer_base; eapply AG.eq_refl
        |eapply Seq.transfer_write;
          [eapply H'
          |eapply H0'
          |eapply AGProps.Add_add]]
      |eapply AGProps.Add_add; simpl; auto].
(* case: transfer_send *)
 eapply H1 in Hin; simpl in Hin.
  destruct Hin as [HeqE |Hin]; try solve [intuition auto].
  generalize (Edges.eq_source _ _ HeqE); intros HeqS; do 2 rewrite Edges.source_rewrite in HeqS;
    generalize (Edges.eq_target _ _ HeqE); intros HeqT; do 2 rewrite Edges.target_rewrite in HeqT;
      generalize (Edges.eq_right _ _ HeqE); intros HeqR; do 2 rewrite Edges.right_rewrite in HeqR;
  unfold Ref.eq in HeqS; unfold Ref.eq in HeqT; unfold AccessRight.eq in HeqR.
  generalize H; intros H'.
  generalize H0; intros H0'.
  eapply IHHtr' in H'.
  eapply IHHtr' in H0'.
  rewrite HeqS in *; rewrite HeqT in *; rewrite HeqR in *.
  clear IHHtr'.


  do 7 (try destruct H' as [H'' | H']); try rename H'' into H';
  do 7 (try destruct H0' as [H'' | H0']); try rename H'' into H0';
(*  try solve [ *)
  try (unfold Ref.eq in H'; destruct H' as [H' Heq1]; try rewrite Heq1 in *; try rewrite H' in *);
  try (unfold Ref.eq in H0'; destruct H0' as [H0' Heq2]; try rewrite Heq2 in *; try rewrite H0' in *);
   try (unfold Ref.eq in *; solve [destruct Hpa as [Htr Hmax]; intuition auto
           |eapply Seq.not_in_ag_objs_spec_tgt in H'; try contradiction; try apply Hobjs; auto
           |eapply Seq.not_in_ag_objs_spec_src in H'; try contradiction; try apply Hobjs; auto
           |eapply Seq.not_in_ag_objs_spec_tgt in H0'; try contradiction; try apply Hobjs; auto
           |eapply Seq.not_in_ag_objs_spec_src in H0'; try contradiction; try apply Hobjs; auto])
(* ] *)
.
(* 6 (4 new) subgoals *)
left; destruct Hpa as [Htr Hm];
    eapply Hm;
      [eapply Seq.potTransfer_trans;
        [eapply Seq.potTransfer_base; eapply AG.eq_refl
        |eapply Seq.transfer_send;
          [eapply H'
          |eapply H0'
          |eapply AGProps.Add_add]]
      |eapply AGProps.Add_add; simpl; auto].
right; left; split; auto; try apply Ref.eq_refl; destruct Hpa as [Htr Hm];
    eapply Hm.
      eapply Seq.potTransfer_trans.
        eapply Seq.potTransfer_base; eapply AG.eq_refl.
        eapply Seq.transfer_send.
          eapply H'.
          eapply H0'.
          eapply AGProps.Add_add .
      eapply AGProps.Add_add; simpl; auto .
do 2 right; left; split; auto; try apply Ref.eq_refl; destruct Hpa as [Htr Hm];
    eapply Hm.
      eapply Seq.potTransfer_trans.
        eapply Seq.potTransfer_base; eapply AG.eq_refl.
        eapply Seq.transfer_send.
          eapply H'.
          eapply H0'.
          eapply AGProps.Add_add .
      eapply AGProps.Add_add; simpl; auto .
left; destruct Hpa as [Htr Hm];
    eapply Hm;
      [eapply Seq.potTransfer_trans;
        [eapply Seq.potTransfer_base; eapply AG.eq_refl
        |eapply Seq.transfer_send;
          [eapply H'
          |eapply H0'
          |eapply AGProps.Add_add]]
      |eapply AGProps.Add_add; simpl; auto].
(* case: transfer_send_reply *)
  eapply H0 in Hin; simpl in Hin.
  destruct Hin as [HeqE |Hin]; try solve [intuition auto].
  generalize (Edges.eq_source _ _ HeqE); intros HeqS; do 2 rewrite Edges.source_rewrite in HeqS;
    generalize (Edges.eq_target _ _ HeqE); intros HeqT; do 2 rewrite Edges.target_rewrite in HeqT;
      generalize (Edges.eq_right _ _ HeqE); intros HeqR; do 2 rewrite Edges.right_rewrite in HeqR;
  unfold Ref.eq in HeqS; unfold Ref.eq in HeqT; unfold AccessRight.eq in HeqR.
  generalize H; intros H'.
  eapply IHHtr' in H'.
  rewrite HeqS in *; rewrite HeqT in *; rewrite <- HeqR in *.
  clear IHHtr'.
do 7 (try destruct H' as [H'' | H']); try rename H'' into H'; 
  try (unfold Ref.eq in H'; destruct H' as [H' Heq1]; try rewrite Heq1 in *; try rewrite H' in *);
   try solve [intuition]. 
     left; destruct Hpa as [Htr Hm];
     eapply Hm;
       [eapply Seq.potTransfer_trans;
         [eapply Seq.potTransfer_base; eapply AG.eq_refl
         |eapply Seq.transfer_send_reply; [eapply H'| eapply AGProps.Add_add]]
       |eapply AGProps.Add_add; simpl; eauto].
     do 2 right; left; split; auto; try apply Ref.eq_refl; destruct Hpa as [Htr Hm];
     eapply Hm;
       [eapply Seq.potTransfer_trans;
         [eapply Seq.potTransfer_base; eapply AG.eq_refl
         |eapply Seq.transfer_send_reply; [eapply H'| eapply AGProps.Add_add]]
       |eapply AGProps.Add_add; simpl; eauto].
     right; left; split; auto; try apply Ref.eq_refl; destruct Hpa as [Htr Hm];
     eapply Hm;
       [eapply Seq.potTransfer_trans;
         [eapply Seq.potTransfer_base; eapply AG.eq_refl
         |eapply Seq.transfer_send_reply; [eapply H'| eapply AGProps.Add_add]]
       |eapply AGProps.Add_add; simpl; eauto].
(* case: transfer_weak *)
  eapply H2 in Hin; simpl in Hin.
  destruct Hin as [HeqE |Hin]; try solve [intuition auto].
  generalize (Edges.eq_source _ _ HeqE); intros HeqS; do 2 rewrite Edges.source_rewrite in HeqS;
    generalize (Edges.eq_target _ _ HeqE); intros HeqT; do 2 rewrite Edges.target_rewrite in HeqT;
      generalize (Edges.eq_right _ _ HeqE); intros HeqR; do 2 rewrite Edges.right_rewrite in HeqR;
        unfold Ref.eq in HeqS; unfold Ref.eq in HeqT; unfold AccessRight.eq in HeqR.
  generalize H; intros H'.
  generalize H0; intros H0'.
  eapply IHHtr' in H'.
  eapply IHHtr' in H0'.
  rewrite HeqS in *; rewrite HeqT in *; rewrite <- HeqR in *.
  clear IHHtr'.



  do 7 (try destruct H' as [H'' | H']); try rename H'' into H';
  do 7 (try destruct H0' as [H'' | H0']); try rename H'' into H0';
(*  try solve [ *)
  try (unfold Ref.eq in H'; destruct H' as [H' Heq1]; try rewrite Heq1 in *; try rewrite H' in *);
  try (unfold Ref.eq in H0'; destruct H0' as [H0' Heq2]; try rewrite Heq2 in *; try rewrite H0' in *);
   try (unfold Ref.eq in *; solve [destruct Hpa as [Htr Hmax]; intuition auto
           | destruct Hpa as [Htr Hmax]; destruct H1 as [H1 | H1]; rewrite H1 in *; intuition auto
           |eapply Seq.not_in_ag_objs_spec_tgt in H'; try contradiction; try apply Hobjs; auto
           |eapply Seq.not_in_ag_objs_spec_src in H'; try contradiction; try apply Hobjs; auto
           |eapply Seq.not_in_ag_objs_spec_tgt in H0'; try contradiction; try apply Hobjs; auto
           |eapply Seq.not_in_ag_objs_spec_src in H0'; try contradiction; try apply Hobjs; auto])
(* ] *)
.
  (* 4 (4 new) cases *)
  left; destruct Hpa as [Htr Hm];
    eapply Hm;
      [eapply Seq.potTransfer_trans;
        [eapply Seq.potTransfer_base; eapply AG.eq_refl
        |eapply Seq.transfer_weak;
          [eapply H'
          |eapply H0'
          |auto
          |eapply AGProps.Add_add]]
      |eapply AGProps.Add_add; simpl; auto].
  right; left; split; auto; try apply Ref.eq_refl; destruct Hpa as [Htr Hm];
    eapply Hm.
      eapply Seq.potTransfer_trans.
        eapply Seq.potTransfer_base; eapply AG.eq_refl.
        eapply Seq.transfer_weak.
          eapply H'.
          eapply H0'.
          auto.
          eapply AGProps.Add_add .
      eapply AGProps.Add_add; simpl; auto .
  left; destruct Hpa as [Htr Hm];
    eapply Hm;
      [eapply Seq.potTransfer_trans;
        [eapply Seq.potTransfer_base; eapply AG.eq_refl
        |eapply Seq.transfer_weak;
          [eapply H'
          |eapply H0'
          |auto
          |eapply AGProps.Add_add]]
      |eapply AGProps.Add_add; simpl; auto].
  do 2 right; left; split; auto; try apply Ref.eq_refl; destruct Hpa as [Htr Hm];
    eapply Hm.
      eapply Seq.potTransfer_trans.
        eapply Seq.potTransfer_base; eapply AG.eq_refl.
        eapply Seq.transfer_weak.
          eapply H'.
          eapply H0'.
          auto.
          eapply AGProps.Add_add .
      eapply AGProps.Add_add; simpl; auto .
Qed.


  Theorem AG_attenuating_insert: forall ag p a n ag' p' objs N, 
    Seq.potAcc ag p -> 
    Seq.ag_objs_spec p N ->
    ~ RefSet.In n N ->
    ~ RefSet.In n objs ->
    AG.Equal (insert a n p) ag' ->
    Seq.potAcc ag' p' ->
    AG_attenuating objs p p'.
  Proof.
    red. intros ag p a n ag' p' objs N Hpa Hobjs HninN' HninN Hinsert Hpa' src tgt HinS HinT rgt HninP.
    case (Ref.eq_dec src tgt); intros Hneq; [left; auto| right; intro Hin].
    (* eliminate objs0 *)
(*    eapply ag_objs_spec_equiv in H4.
      [
      |apply H0
      |apply AG.eq_refl].
    eapply H4 in H5.
    eapply H4 in H6.     
    clear H4; clear objs0. *)
    (* use endow_spec_1 *)
    generalize Hpa; intros Hpa2.
    eapply endow_spec_1  with (ag:=ag) (ag':=ag')in Hpa2;
      [
      | apply Hobjs
      | apply HninN'
      | apply Hinsert
      | apply Hpa'
      | apply Hin].
    (* blast through cases *) 
    do 7 (try unfold Ref.eq in Hpa2; try destruct Hpa2 as [Hpa2' | Hpa2]); try rename Hpa2' into Hpa2; 
      try (try unfold Ref.eq in Hpa2; destruct Hpa2 as [Hpa2 Heq1]; try rewrite Heq1 in *; try rewrite Hpa2 in *);
        try solve [intuition auto | apply Hneq; apply Ref.eq_refl].
    (* That seems too easy *)
  Qed.


Theorem AG_attenuating_endow : forall ag p a n objs Np, Seq.ag_objs_spec p Np -> 
   ~ RefSet.In n objs -> ~ RefSet.In n Np ->Seq.potAcc ag p -> AG_attenuating objs p (endow a n p).
Proof.

intros.
unfold endow in *.
generalize (Seq.potAcc_potAcc_fun (insert a n p)); intros.
revert H3; generalize (Seq.potAcc_fun (insert a n p)); intros p' H3.
eapply AG_attenuating_insert;
  [ apply H2
    | apply H
    | apply H1
    | apply H0
    | apply AG.eq_refl; auto
    | apply H3].
Qed.

Theorem potAcc_approx_potAcc_approx_dirAcc_dep: forall Fa Fp , 
  potAcc_approx Fa Fp -> potAcc_approx_dirAcc_dep (fun s => Fa) (fun s => Fp).
Proof.
  red; intros.
  eapply H;
    [eapply H4
    |eapply H5
    |eapply H6].
Qed.

(* dirAcc_approx_dep Fs Fsa := forall s s'ag ag' ag2,
dirAcc_spec s ag -> dirAcc_spec (Fs s) ag2 ->
AG.Subset ag ag' -> SemDefns.Sys.eq s s' -> AG.Subset ag2 (Fsa s' ag')

potAcc_approx_dirAcc_dep Fsa Fp = forall i i' p p' p2 s s' s'',
SemDefns.Sys.eq s s' -> SemDefns.Sys.eq s' s'' ->
dirAcc_spec s i -> AG.Subset i i' -> Seq.potAcc i' p ->
Seq.potAcc (Fsa s' i') p2 -> AG.Subset p p' -> AG.Subset p2 (Fp s'' p') *)


Definition dirAcc_op op s :=
match op with
| Sem.read a t => read_ag
| Sem.write a t => write_ag
| Sem.fetch a t c i => if SemDefns.fetch_preReq_dec a t s then fetch_dep_ag a t c s else id_ag
| Sem.store a t c i => if SemDefns.store_preReq_dec a t s then store_dep_ag a t c s else id_ag
| Sem.revoke a t c => revoke_ag
| Sem.send a t ixi_list opt_i => if SemDefns.send_preReq_dec a t s then send_dep_ag a t ixi_list s else id_ag
| Sem.allocate a n i ixi_list => if SemDefns.allocate_preReq_dec a n s then allocate_dep_ag a n ixi_list s else id_ag
| Sem.destroy a t => destroy_ag
end.

Theorem Proper_dirAcc_op: Proper (eq ==> Sys.eq ==> AG.eq ==> AG.eq) dirAcc_op.
Proof.
  unfold Proper; unfold respectful.
  intros op op' Hop s s' Hsys ag ag' Hag.
  unfold dirAcc_op.
  destruct op; destruct op'; simpl; (* solve nonsensical cases *) try discriminate Hop;
    (* solve id_ag cases *)
  unfold read_ag; unfold write_ag; unfold revoke_ag; unfold destroy_ag; unfold id_ag; auto;
    (* find eq in Hop *)
  inversion Hop.
  (* fetch *)
  Ltac Proper_dirAcc_op_inner_solve Hcase Hcase' :=
    solve 
    [apply Hcase' in Hcase; contradiction
      | auto
      | apply Ref.eq_refl
      | apply AccessRight.eq_refl
    ].

  unfold fetch_dep_ag.
  case (SemDefns.fetch_preReq_dec t3 t4 s); intros Hcase;
  case (SemDefns.fetch_preReq_dec t3 t4 s'); intros Hcase'; 
    try solve [eapply SemDefns.fetch_preReq_eq_iff in Hcase; Proper_dirAcc_op_inner_solve Hcase Hcase'
    | eapply SemDefns.fetch_preReq_eq_iff in Hcase'; Proper_dirAcc_op_inner_solve Hcase' Hcase
    | auto].
  eapply ag_add_cap_by_indirect_index_equiv; eauto; try apply Ref.eq_refl.
  unfold Fn_cap_equiv; intros.
  case (SemDefns.option_hasRight_dec (SC.getCap t4 t3 s)); intros Hcase2;
  case (SemDefns.option_hasRight_dec (SC.getCap t4 t3 s')); intros Hcase2';
    auto;
      solve [eapply SemDefns.option_hasRight_eq in Hcase2; Proper_dirAcc_op_inner_solve Hcase2 Hcase2'
        | eapply SemDefns.option_hasRight_eq in Hcase2'; Proper_dirAcc_op_inner_solve Hcase2' Hcase2].

  (* store *)
  unfold store_dep_ag.
  case (SemDefns.store_preReq_dec t3 t4 s); intros Hcase;
  case (SemDefns.store_preReq_dec t3 t4 s'); intros Hcase'; 
    try solve [eapply SemDefns.store_preReq_eq_iff in Hcase; Proper_dirAcc_op_inner_solve Hcase Hcase'
    | eapply SemDefns.store_preReq_eq_iff in Hcase'; Proper_dirAcc_op_inner_solve Hcase' Hcase
    | auto].
  eapply ag_push_cap_by_indices_equiv; eauto; try apply Ref.eq_refl.

  (* send *)
  unfold send_dep_ag.
  case (SemDefns.send_preReq_dec t1 t2 s); intros Hcase;
  case (SemDefns.send_preReq_dec t1 t2 s'); intros Hcase'; 
    try solve [eapply SemDefns.send_preReq_eq_iff in Hcase; Proper_dirAcc_op_inner_solve Hcase Hcase'
    | eapply SemDefns.send_preReq_eq_iff in Hcase'; Proper_dirAcc_op_inner_solve Hcase' Hcase
    | auto].

  generalize (SC.getCap_eq _ _ _ _ _ _ Hsys (Ind.eq_refl t2) (Ref.eq_refl t1) ); intros HcapEq.
  case (option_map1_eq_tgt_dec t2 t1 s); intros Hcase3;
  case (option_map1_eq_tgt_dec t2 t1 s'); intros Hcase3';
  try solve [apply ag_add_caps_reply_equiv; eauto; try apply Ref.eq_refl
    | eapply ag_add_caps_send_equiv; eauto; try apply Ref.eq_refl; try apply CIL_Facts.cil_Equiv
    | case (option_sumbool (SC.getCap t2 t1 s)); intros Hcap; [|destruct Hcap as [cap Hcap]]; rewrite Hcap in *;
      (case (option_sumbool (SC.getCap t2 t1 s')); intros Hcap'; [|destruct Hcap' as [cap' Hcap']];
        rewrite Hcap' in *); simpl in *; try contradiction;
        solve [eapply Cap.target_eq in HcapEq; 
          solve [eapply Ref.eq_trans in HcapEq; [| eapply Hcase3]; contradiction
            |eapply Ref.eq_sym in HcapEq; eapply Ref.eq_trans in HcapEq; [|eapply Hcase3']; contradiction]
        ]].

  (* allocate *)
  unfold allocate_dep_ag.
  case (SemDefns.allocate_preReq_dec t2 t3 s); intros Hcase;
  case (SemDefns.allocate_preReq_dec t2 t3 s'); intros Hcase'; 
    try solve [eapply SemDefns.allocate_preReq_eq_iff in Hcase; Proper_dirAcc_op_inner_solve Hcase Hcase'
    | eapply SemDefns.allocate_preReq_eq_iff in Hcase'; Proper_dirAcc_op_inner_solve Hcase' Hcase
    | auto].
  eapply ag_add_caps_allocate_equiv; eauto; try apply Ref.eq_refl; try apply CIL_Facts.cil_Equiv.

Qed.


Theorem dirAcc_op_nondecr: forall op s i, AG.Subset i (dirAcc_op op s i).
Proof.
Admitted.

Theorem dirAcc_approx_dep_op : forall op, dirAcc_approx_dep (Sem.do_op op) (dirAcc_op op).
Proof.
  intros; destruct op; unfold dirAcc_op.
  apply dirAcc_approx_dirAcc_approx_dep; apply dirAcc_approx_read with (a:=t) (c:=t0).
  apply dirAcc_approx_dirAcc_approx_dep; apply dirAcc_approx_write with (a:=t) (c:=t0).

  (* fetch *)
  red; intros.
  case ( SemDefns.fetch_preReq_dec t t0 s'); intros.
  eapply dirAcc_approx_dep_fetch;  [apply H | apply H0 | apply H1 | apply H2].
  unfold id_ag in *.
  eapply Sem.fetch_invalid in n.
  simpl in *.
  eapply AGProps.subset_trans; [ | apply H1].
  eapply AGProps.subset_equal.
  eapply dirAcc_spec_eq; [ | apply H0 | apply H].
  eapply Sys.eq_trans; [| apply Sys.eq_sym; eapply H2].
  eapply Sys.eq_trans; [|apply n].
  eapply SemConv.do_fetch_eq; eauto; try apply Ind.eq_refl; try apply Ref.eq_refl.

  (* store *)
  red; intros.
  case ( SemDefns.store_preReq_dec t t0 s'); intros.
  eapply dirAcc_approx_dep_store;  [apply H | apply H0 | apply H1 | apply H2].
  unfold id_ag in *.
  eapply Sem.store_invalid in n.
  simpl in *.
  eapply AGProps.subset_trans; [ | apply H1].
  eapply AGProps.subset_equal.
  eapply dirAcc_spec_eq; [ | apply H0 | apply H].
  eapply Sys.eq_trans; [| apply Sys.eq_sym; eapply H2].
  eapply Sys.eq_trans; [|apply n].
  eapply SemConv.do_store_eq; eauto; try apply Ind.eq_refl; try apply Ref.eq_refl.

  (* revoke *)
  apply dirAcc_approx_dirAcc_approx_dep; eapply dirAcc_approx_revoke.

  Require Import OptionMap2.
  (* send *)
  red; intros.
  case ( SemDefns.send_preReq_dec t t0 s'); intros.
  eapply dirAcc_approx_dep_send;  [apply H | apply H0 | apply H1 | apply H2].
  unfold id_ag in *.
  eapply Sem.send_invalid in n.
  simpl in *.
  eapply AGProps.subset_trans; [ | apply H1].
  eapply AGProps.subset_equal.
  eapply dirAcc_spec_eq; [ | apply H0 | apply H].
  eapply Sys.eq_trans; [| apply Sys.eq_sym; eapply H2].
  eapply Sys.eq_trans; [|apply n].
  eapply SemConv.do_send_eq; eauto; 
    try apply Ind.eq_refl; try apply Ref.eq_refl; try eapply_cil_refl; 
      try (apply option_map_eq_refl; split; eauto).

  (* allocate *)
  red; intros.
  case ( SemDefns.allocate_preReq_dec t t0 s'); intros.
  eapply dirAcc_approx_dep_allocate;  [apply H | apply H0 | apply H1 | apply H2].
  unfold id_ag in *.
  eapply Sem.allocate_invalid in n.
  simpl in *.
  eapply AGProps.subset_trans; [ | apply H1].
  eapply AGProps.subset_equal.
  eapply dirAcc_spec_eq; [ | apply H0 | apply H].
  eapply Sys.eq_trans; [| apply Sys.eq_sym; eapply H2].
  eapply Sys.eq_trans; [|apply n].
  eapply SemConv.do_allocate_eq; eauto; 
    try apply Ind.eq_refl; try apply Ref.eq_refl; try eapply_cil_refl; 
      try (apply option_map_eq_refl; split; eauto).
  
  (* destroy *)
  apply dirAcc_approx_dirAcc_approx_dep; eapply dirAcc_approx_destroy.

Qed.

Definition potAcc_op op s := 
match op with
| Sem.read a t => id_ag
| Sem.write a t => id_ag
| Sem.fetch a t c i => id_ag
| Sem.store a t c i => id_ag
| Sem.revoke a t c => id_ag
| Sem.send a t ixi_list opt_i => id_ag
| Sem.allocate a n i ixi_list => endow_dep a n s
| Sem.destroy a t => id_ag
end.

 (* TODO: put in a set library *)

  Theorem subset_exists_fn : forall s s', let f s'' := AG.union s'' (AG.diff s' s) in
    AG.Subset s s' -> AG.eq (f s) s'.
  Proof.
    intros.
    unfold f; simpl.
    generalize (AGProps.diff_inter_all s' s); intros.
    rewrite AGProps.inter_sym in H0.
    rewrite (AGProps.inter_subset_equal H) in H0.
    rewrite AGProps.union_sym. 
    auto.
  Qed.

  Implicit Arguments subset_exists_fn [s s'].

  (* TODO: move to sequential access 
     Also, rename as it is only union now.  We require a different fn for a diff bound over s'. *)
  Theorem union_diff_fn_req : forall s, Seq.ag_potTransfer_fn_req (fun s' => AG.union s' s).
  Proof.
    intros.
    split; [|split].
    (* ag_add_commute *)
    unfold Seq.ag_add_commute; intros.
    eapply AGProps.union_Add with (s'':=s)in H.
    auto.
    (* ag_nondecr *)
    unfold ag_nondecr; intros.
    eapply AGProps.subset_trans; [apply H | apply AGProps.union_subset_1].
    (* ag_equiv *)
    unfold Seq.ag_equiv; intros.
    apply AGProps.union_equal_1; auto.
  Qed.

  (* TODO: move to set library *)
  Theorem double_fold_union_add : forall ag ag',
    AG.eq (AG.fold AG.add ag (AG.fold AG.add ag' AG.empty)) (AG.union ag ag').
  Proof.
    intros.
    eapply AG.eq_trans.
    eapply AGProps.fold_init; [eapply AGAddEq.compat_op_add |  eapply AGProps.fold_identity].

    Theorem fold_union_add: forall ag ag',
      AG.eq (AG.fold AG.add ag ag') (AG.union ag ag').
    Proof.
      intros.  
      eapply AGProps.fold_rec_bis; intros.
      (* compat *)
      rewrite AGProps.union_equal_1; [apply H0 | eapply AG.eq_sym; auto].
      (* base *)
      rewrite AGProps.empty_union_1; auto; try apply AG.eq_refl.
      (* step *)
      eapply AG.eq_trans; [eapply AGAddEq.add_equal_complete; [apply H1 | apply Edge.eq_refl]|].
      eapply AG.eq_sym.
      eapply AGProps.union_add.
    Qed.
    eapply fold_union_add.
    Qed.


Theorem potAcc_approx_dirAcc_dep_op : forall op, potAcc_approx_dirAcc_dep (dirAcc_op op) (potAcc_op op).
Proof.
  intros.
   Ltac solve_potAcc_approx_dirAcc_dep_id H4 H3 := eapply potAcc_equiv in H4; [ | apply AG.eq_refl | apply H3 ];
    eapply AGProps.subset_trans; [apply AGProps.subset_equal; apply AG.eq_sym; apply H4| auto].
  destruct op; red; simpl;
    try unfold read_ag in *; try unfold write_ag in *; try unfold revoke_ag in *; try unfold revoke_ag in *;
      unfold id_ag in *; 
  (* read, write, revoke, destroy *)
        try (intros; solve 
          [ solve_potAcc_approx_dirAcc_dep_id H4 H3 
          | solve_potAcc_approx_dirAcc_dep_id H4 H3 
          | solve_potAcc_approx_dirAcc_dep_id H4 H3 
          | solve_potAcc_approx_dirAcc_dep_id H4 H3 ]).


  (* fetch *)
  intros i i' p p' p2 s s' s''; case (SemDefns.fetch_preReq_dec t t0 s');
    intros Hcase HeqS HeqS' Hda Hsub Hpa Hpa2 Hsub'; [clear HeqS' |solve_potAcc_approx_dirAcc_dep_id Hpa2 Hpa].
  
  eapply dirAcc_spec_iff in Hda; [clear HeqS s s'' | apply Sys.eq_sym; apply HeqS | apply AG.eq_refl].
  eapply AGProps.subset_trans; [clear Hsub' p'|apply Hsub'].
  eapply AGProps.subset_equal.
  eapply potAcc_equiv; [ apply AG.eq_refl| | apply Hpa].
  eapply Seq.potAcc_potTransfer; [| apply Hpa2].

  generalize (potTransfer_fn_req_fetch t t0 t1 s'); intros [HcommD [HmonD HequivD]].
  generalize (union_diff_fn_req (AG.diff i' i));intros Hreq_F_union_delt.
  generalize Hreq_F_union_delt; intros [HcommU [HmonU HequivU]].

  eapply Seq.potTransfer_equality_full; 
    [apply (subset_exists_fn Hsub)
      |   eapply AG.eq_trans; [ | eapply HequivD; apply (subset_exists_fn Hsub)]
      | eapply (Seq.potTransfer_commute_monotonic Hreq_F_union_delt); eapply potTransfer_fetch_dep_ag; 
        [ apply Hda 
          | apply Hcase
          | eapply Seq.potTransfer_base; apply AG.eq_refl]
    ].
  eapply (add_commute_increasing_transpose _ _ HcommU HequivU HcommD HequivD); auto.


  (* store *)
  intros i i' p p' p2 s s' s''; case (SemDefns.store_preReq_dec t t0 s');
    intros Hcase HeqS HeqS' Hda Hsub Hpa Hpa2 Hsub'; [clear HeqS' |solve_potAcc_approx_dirAcc_dep_id Hpa2 Hpa].
  
  eapply dirAcc_spec_iff in Hda; [clear HeqS s s'' | apply Sys.eq_sym; apply HeqS | apply AG.eq_refl].
  eapply AGProps.subset_trans; [clear Hsub' p'|apply Hsub'].
  eapply AGProps.subset_equal.
  eapply potAcc_equiv; [ apply AG.eq_refl| | apply Hpa].
  eapply Seq.potAcc_potTransfer; [| apply Hpa2].

  generalize (potTransfer_fn_req_store t t0 t1 s'); intros [HcommD [HmonD HequivD]].
  generalize (union_diff_fn_req (AG.diff i' i));intros Hreq_F_union_delt.
  generalize Hreq_F_union_delt; intros [HcommU [HmonU HequivU]].

  eapply Seq.potTransfer_equality_full; 
    [apply (subset_exists_fn Hsub)
      |   eapply AG.eq_trans; [ | eapply HequivD; apply (subset_exists_fn Hsub)]
      | eapply (Seq.potTransfer_commute_monotonic Hreq_F_union_delt); eapply potTransfer_store_dep_ag; 
        [ apply Hda 
          | apply Hcase
          | eapply Seq.potTransfer_base; apply AG.eq_refl]
    ].
  eapply (add_commute_increasing_transpose _ _ HcommU HequivU HcommD HequivD); auto.

  (* send *)
  intros i i' p p' p2 s s' s''; case (SemDefns.send_preReq_dec t t0 s');
    intros Hcase HeqS HeqS' Hda Hsub Hpa Hpa2 Hsub'; [clear HeqS' |solve_potAcc_approx_dirAcc_dep_id Hpa2 Hpa].
  
  eapply dirAcc_spec_iff in Hda; [clear HeqS s s'' | apply Sys.eq_sym; apply HeqS | apply AG.eq_refl].
  eapply AGProps.subset_trans; [clear Hsub' p'|apply Hsub'].
  eapply AGProps.subset_equal.
  eapply potAcc_equiv; [ apply AG.eq_refl| | apply Hpa].
  eapply Seq.potAcc_potTransfer; [| apply Hpa2].

  generalize (potTransfer_fn_req_send t t0 l s'); intros [HcommD [HmonD HequivD]].
  generalize (union_diff_fn_req (AG.diff i' i));intros Hreq_F_union_delt.
  generalize Hreq_F_union_delt; intros [HcommU [HmonU HequivU]].

  eapply Seq.potTransfer_equality_full; 
    [apply (subset_exists_fn Hsub)
      |   eapply AG.eq_trans; [ | eapply HequivD; apply (subset_exists_fn Hsub)]
      | eapply (Seq.potTransfer_commute_monotonic Hreq_F_union_delt); eapply potTransfer_send_dep_ag; 
        [ apply Hda 
          | apply Hcase
          | eapply Seq.potTransfer_base; apply AG.eq_refl]
    ].
  eapply (add_commute_increasing_transpose _ _ HcommU HequivU HcommD HequivD); auto.

  (* allocate *)
  
  intros i i' p p' p2 s s' s''.
  generalize (potAcc_approx_allocate t t0 l); intros Hfoo. 
  unfold potAcc_approx_dirAcc_dep in *.
  generalize (Hfoo i i' p p' p2 s s' s''); clear Hfoo.
  unfold endow_dep.
  case (SemDefns.allocate_preReq_dec t t0 s'); case (SemDefns.allocate_preReq_dec t t0 s'');
    intros Hcase Hcase2 Hallocate HeqS HeqS' Hda Hsub Hpa Hpa2 Hsub';
    try (generalize Hcase; intros Hcase'; eapply SemDefns.allocate_preReq_eq_iff in Hcase'; 
      try apply Ref.eq_refl; try solve[apply Sys.eq_sym; apply HeqS'| apply HeqS']);
    try (generalize Hcase2; intros Hcase2'; eapply SemDefns.allocate_preReq_eq_iff in Hcase2';
      try apply Ref.eq_refl; try solve[apply Sys.eq_sym; apply HeqS' | apply HeqS']); 
    try contradiction; try solve_potAcc_approx_dirAcc_dep_id Hpa2 Hpa.

  eapply Hallocate; eauto.
Qed.

Theorem AG_attenuating_eq: forall ag ag', AG.eq ag ag' -> forall objs, AG_attenuating objs ag ag'.
Proof.
  unfold AG_attenuating; intros. 
  case (Ref.eq_dec src tgt); intros Hneq ; [left; auto|right].
  intro Not; apply H2; eauto.
Qed.


  Theorem unborn_not_in_ag_objs: forall s ag, dirAcc_spec s ag -> 
    forall p, Seq.potAcc ag p -> forall n, SC.is_unborn n s ->
      forall N, Seq.ag_objs_spec p N -> ~ RefSet.In n N.
  Proof.
    intros.
    eapply ag_objs_spec_potTransfer_2 in H2; [clear H0 | apply H0].
    unfold Seq.ag_objs_spec in H2.
    intros Hnot.
    eapply H2 in Hnot; clear H2.
    unfold SC.is_unborn in *.
    unfold SC.is_label in *.
    unfold SC.getLabel in *.
    unfold SC.getObjTuple in *.
    unfold SC.tupleGetLabel in *.


    Ltac solve_unborn_not_in_dirAcc HeqEdge HmapS HeqS HmapS HeqP H1 Halive:=
    destruct HeqEdge as [Heq_src [Heq_tgt Heq_rgt]]; simpl in *;
      rewrite Heq_src in *; rewrite Heq_tgt in *; rewrite Heq_rgt in *;
    eapply Sys_MapEquiv.exists_mapsTo_eq in HmapS; [ | apply Sys.eq_sym; apply HeqS | apply Ref.eq_refl ];
    destruct HmapS as [[[[obj1 lbl1] type1] sched1] [[[[HeqOb1 HeqL1] HeqT1] HeqD1] HmapS]]; simpl in *;
    rewrite HeqL1 in *;
    eapply Sys.MapS.find_1 in HmapS; rewrite HmapS in *; simpl in *;
    destruct HeqP as [[[HeqO2 HeqL2] HeqT2] HeqD2]; simpl in *;
    rewrite HeqL2 in *; unfold ObjectLabel.eq in *; rewrite H1 in *;
    discriminate Halive.

    destruct Hnot as [obj [rgt [Hnot|Hnot]]]; eapply H in Hnot;

    destruct_dirAcc Hnot s'' HeqS src_ref src lbl srcType srcSched HmapS 
    src' lbl' srcType' srcSched' HeqP Halive ind cap HmapSrc'
    cap_obj cap_lbl cap_type cap_sched HmapScap cap_obj' cap_lbl' cap_type' cap_sched' 
    HeqPcap HaliveCap rgt' HinR HeqEdge;

    solve [solve_unborn_not_in_dirAcc HeqEdge HmapS HeqS HmapS HeqP H1 Halive
      | solve_unborn_not_in_dirAcc HeqEdge HmapScap HeqS HmapScap HeqPcap H1 HaliveCap].
  Qed.

Definition objs_not_unborn objs s := forall x : RefSet.elt, RefSet.In x objs -> ~ SC.is_unborn x s.

Theorem AG_attenuating_potAcc_op: forall s op ag p, dirAcc_spec s ag -> Seq.potAcc ag p -> 
  forall Np, Seq.ag_objs_spec p Np -> forall objs, objs_not_unborn objs s ->
      AG_attenuating objs p (potAcc_op op s p).
Proof.
  intros s op ag p H H0 Np H1 objs H2.
  destruct op; simpl; try unfold id_ag; try solve [apply AG_attenuating_eq; apply AG.eq_refl].
  unfold endow_dep.
  case (SemDefns.allocate_preReq_dec t t0 s); intros H'; try solve [apply AG_attenuating_eq; apply AG.eq_refl].
  destruct H'.
  eapply AG_attenuating_endow;
    try solve [apply H1| eapply unborn_not_in_ag_objs; eauto| apply H0 |
  intro Hnot; apply H2 in Hnot; apply Hnot; auto].
Qed.

  Definition AG_attenuating_converse n p p' := forall src tgt, RefSet.In src n -> RefSet.In tgt n -> 
    forall rgt, AG.In (Edges.mkEdge src tgt rgt) p' -> 
      Ref.eq src tgt \/ AG.In (Edges.mkEdge src tgt rgt) p.
  

  Theorem AG_attenuating_converse_iff : forall n p p', AG_attenuating n p p' <-> AG_attenuating_converse n p p'.
  Proof.
    intros n p p'; split.
    
    intros Hreduce src tgt HinS HinT rgt  HinP'.
    generalize (Hreduce src tgt HinS HinT rgt); clear Hreduce; intros Hreduce.
    case (AGProps.In_dec (Edges.mkEdge src tgt rgt) p); intros Hcase; [intuition|].
    eapply Hreduce in Hcase; destruct Hcase as [Hin | Hnin]; [intuition|contradiction].
    
    intros Hreduce src tgt HinS HinT rgt  HinP'.
    generalize (Hreduce src tgt HinS HinT rgt); clear Hreduce; intros Hreduce.
    case (AGProps.In_dec (Edges.mkEdge src tgt rgt) p'); intros Hcase; intuition.
  Qed.


End MakeAttenuation.
















