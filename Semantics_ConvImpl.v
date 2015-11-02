Require Import Semantics.
(* type_remove *)
Require Import Semantics_Conv.
Require Import OptionMap2.
Require Import FMapFacts.
Require Import AccessRights.
Require Import AccessRightSets.
Require Import References.
Require Import RefSets.
Require Import Capabilities.
Require Import Indices.
Require Import Objects.
Require Import SystemState.
Require Import SemanticsDefinitions.
Require Import Semantics.

Module MakeSemanticsConv (Ref:ReferenceType) (RefS: RefSetType Ref) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) (SemDefns: SemanticsDefinitionsType Ref Cap Ind Obj Sys) (Sem: SemanticsType Ref RefS Cap Ind Obj Sys SemDefns) : SemanticsConv Ref RefS Cap Ind Obj Sys SemDefns Sem.

Require Import SystemState_ConvImpl.

  Module SC := SemDefns.SC.
  Module OC := SC.OC.
  Module CC := SC.CC.


  Module CIL_Facts := SC.CIL_Facts.
  (* type_remove *)
  Module Sys_MapEquiv := SC.Sys_MapEquiv.

  (* type_remove *)
  Definition SysEQ := SC.SysEQ.
  (* type_remove *)
  Definition CapEQ := CC.CapEQ.
  (* type_remove *)
  Definition ObjEQ := OC.ObjEQ.
  (* type_remove *)
  Definition RefEQ := CC.RefEQ.
  (* type_remove *)
  Definition IndEQ := OC.IndEQ.
  (* type_remove *)
  Definition PEQ := SC.PEQ.

  Hint Resolve SC.addCap_eq.
  Hint Resolve ARSet.eq_refl.
  Hint Resolve Cap.mkCap_eq.
  Hint Immediate Sys.eq_sym.

  Theorem do_store_eq : forall a a' t t' c c' i i' s s',
    Sys.eq s s' ->
    Ref.eq a a' ->
    Ind.eq t t' ->
    Ind.eq c c' ->
    Ind.eq i i' ->
    Sys.eq (Sem.do_store a t c i s) (Sem.do_store a' t' c' i' s').
  Proof.
    intros.
    case (SemDefns.store_preReq_dec a t s); simpl; intros.
    
    (* case where preReq occurs *)
    eapply Sys.eq_trans. eapply Sem.store_valid; auto.
    eapply SemDefns.store_preReq_eq_iff in s0;
      [
      |apply Ref.eq_sym in H0; apply H0
      |apply Ind.eq_sym in H1; apply H1
      |apply Sys.eq_sym in H; apply H].
    eapply Sys.eq_sym. eapply Sys.eq_trans. eapply Sem.store_valid; auto.

    apply option_map1_Equiv with
      (EqA := RefEQ)
      (EqB := SysEQ); try apply SemDefns.option_target_eq; try apply Ref.eq_sym; eauto.
    (* probably a new theorem here *)
    unfold option_map1_compat_op.
    intros.
    unfold SC.copyCap.
    eapply option_map1_Equiv with
      (EqA := CapEQ)
      (EqB := SysEQ); try apply SC.getCap_eq; try apply Ref.eq_sym; auto.
    (* probably a new theorem here *)
    unfold option_map1_compat_op.
    intros.
    unfold SC.addCap.
    eapply option_map1_Equiv with
      (EqA := ObjEQ)
      (EqB := SysEQ); try apply SC.getObj_eq; auto.
    (* probably a new theorem here *)
    unfold option_map1_compat_op.
    intros.
    unfold SC.updateObj.
    eapply option_map1_Equiv with
      (EqA := PEQ)
      (EqB := SysEQ); try apply SC.getObjTuple_eq; eauto.
    (* probably a new theroem here *)
    unfold option_map1_compat_op.
    intros.
    (* And here is the meat of the theorem *)
    unfold SC.addObjTuple.
    unfold SC.update_pair_object. 
    repeat progress (destruct a3; destruct a'3).
    repeat progress (destruct p; destruct p0).
    simpl in *.
    repeat progress destruct H7.
    apply SC.addObjTuple_eq; auto.
    unfold Sys.P.eq. 
    simpl.
    repeat progress (split; auto).
    apply OC.addCap_eq; auto.
    (* and the case where things are not equal *)
    eapply Sys.eq_trans. eapply Sem.store_invalid; auto.    
    eapply Sys.eq_sym. eapply Sys.eq_trans;[ eapply Sem.store_invalid; auto|auto].
    intro n'. apply n.
    eapply SemDefns.store_preReq_eq_iff in n'; eauto.
  Qed.

  Theorem do_send_eq : forall a a' t t' cil cil' op_i op_i' s s',
    Sys.eq s s' ->
    Ref.eq a a' ->
    Ind.eq t t' ->
    CIL_Facts.cil_eq cil cil' ->
    option_map_eq Ind.eq op_i op_i' ->
    Sys.eq (Sem.do_send a t cil op_i s) (Sem.do_send a' t' cil' op_i' s').
  Proof.
    intros.
    case (SemDefns.send_preReq_dec a t s); simpl; intros.
    eapply Sys.eq_trans. eapply Sem.send_valid; auto.
    eapply SemDefns.send_preReq_eq_iff in s0;
      [
      |apply Ref.eq_sym in H0; apply H0
      |apply Ind.eq_sym in H1; apply H1
      |apply Sys.eq_sym in H; apply H].
    eapply Sys.eq_sym. eapply Sys.eq_trans. eapply Sem.send_valid; auto.


    Ltac apply_cil_sym := let cil_sym := fresh "cil_sym" in 
        destruct CIL_Facts.cil_Equiv as [_ cil_sym _]; unfold Symmetric in cil_sym; apply cil_sym.

    Hint Extern 1 (CIL_Facts.cil_eq _ _) => apply_cil_sym.

    eapply option_map1_Equiv with
      (EqA := RefEQ)
      (EqB := SysEQ); try apply SemDefns.option_target_eq; try apply Ref.eq_sym; auto.
    (* probably a new theorem here *)
    unfold option_map1_compat_op.
    intros.
    apply SC.copyCapList_eq; try apply Ref.eq_sym; eauto.
    destruct op_i; destruct op_i'.
    simpl in *.
    unfold SC.addCap.
    eapply option_map1_Equiv with
      (EqA := ObjEQ)
      (EqB := SysEQ); try apply SC.getObj_eq; auto.
    unfold option_map1_compat_op; intros.
    unfold SC.updateObj.
    eapply option_map1_Equiv with
      (EqA := PEQ)
      (EqB := SysEQ); simpl in *;  try apply SC.getObjTuple_eq; auto.
    (*case 1*)
    unfold option_map1_compat_op; intros.
    apply SC.addObjTuple_eq; auto.
    repeat progress destruct a2; destruct a'2.
    repeat progress destruct p0.
    repeat progress destruct p.
    repeat progress destruct H6.
    unfold Sys.P.eq; simpl.
    simpl in *.
    repeat progress split; auto.
    apply OC.addCap_eq; auto.
    apply CC.mkCap_equiv; try apply Ref.eq_sym; auto.
    
    (* next 3 cases *)
    unfold option_map_eq in H3; simpl in H3; contradiction.
    unfold option_map_eq in H3; simpl in H3; contradiction.
    simpl; auto.

    (* and the case where things are not equal *)
    eapply Sys.eq_trans. eapply Sem.send_invalid; auto.    
    eapply Sys.eq_sym. eapply Sys.eq_trans;[ eapply Sem.send_invalid; auto|auto].
    intro n'. apply n.
    eapply SemDefns.send_preReq_eq_iff in n'; eauto.
  Qed.

Theorem do_revoke_eq : forall a a' t t' c c' s s',
    Sys.eq s s' ->
    Ref.eq a a' ->
    Ind.eq t t' ->
    Ind.eq c c' ->
    Sys.eq (Sem.do_revoke a t c s) (Sem.do_revoke a' t' c' s').
  Proof.
    intros.
    case (SemDefns.revoke_preReq_dec a t s); simpl; intros.
    eapply Sys.eq_trans. eapply Sem.revoke_valid; auto.
    eapply SemDefns.revoke_preReq_eq_iff in r;
      [|apply Ref.eq_sym in H0; apply H0
       |apply Ind.eq_sym in H1; apply H1
       |apply Sys.eq_sym in H; apply H].
    eapply Sys.eq_sym. eapply Sys.eq_trans. eapply Sem.revoke_valid; auto.

    eapply option_map1_Equiv with
      (EqA := RefEQ)
      (EqB := SysEQ); try apply SemDefns.option_target_eq; try apply Ref.eq_sym; auto.
    (* probably a new theorem here *)
    unfold option_map1_compat_op.
    intros.
    unfold SC.rmCap.
    eapply option_map1_Equiv with
      (EqA := ObjEQ)
      (EqB := SysEQ); try apply SC.getObj_eq; auto.
    (* probably a new theorem here *)
    unfold option_map1_compat_op.
    intros.
    unfold SC.updateObj.
    eapply option_map1_Equiv with
      (EqA := PEQ)
      (EqB := SysEQ); simpl;  try apply SC.getObjTuple_eq; auto.
    (* probably a new theorem here *)
    unfold option_map1_compat_op.
    intros.
    (* And here is the meat of the theorem *)
    apply SC.addObjTuple_eq; auto.
    unfold SC.update_pair_object.
    repeat progress destruct a2; destruct a'2.
    repeat progress destruct p0.
    repeat progress destruct p.
    repeat progress destruct H5.
    unfold Sys.P.eq.
    simpl in *.
    repeat progress split; auto.
    apply OC.removeCap_eq; auto. 
    (* and the case where things are not equal *)
    eapply Sys.eq_trans. eapply Sem.revoke_invalid; auto.    
    eapply Sys.eq_sym. eapply Sys.eq_trans;[ eapply Sem.revoke_invalid; auto|auto].
    intro n'. apply n.
    eapply SemDefns.revoke_preReq_eq_iff in n'; eauto.
  Qed.

  Theorem do_destroy_eq : forall a a' t t' s s',
    Sys.eq s s' ->
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq (Sem.do_destroy a t s) (Sem.do_destroy a' t' s').
  Proof.
    intros.
    case (SemDefns.destroy_preReq_dec a t s); simpl; intros.
    eapply Sys.eq_trans. eapply Sem.destroy_valid; auto.
    eapply SemDefns.destroy_preReq_eq_iff in d;
      [|apply Ref.eq_sym in H0; apply H0
       |apply Ind.eq_sym in H1; apply H1
       |apply Sys.eq_sym in H; apply H].
    eapply Sys.eq_sym. eapply Sys.eq_trans. eapply Sem.destroy_valid; auto.
    eapply option_map1_Equiv with
      (EqA := RefEQ)
      (EqB := SysEQ); try apply SemDefns.option_target_eq; try apply Ref.eq_sym; auto.
    unfold option_map1_compat_op.
    intros.
    (* probably a new theorem here *)
    unfold SC.set_dead.
    unfold SC.set_label.
    eapply option_map1_Equiv with
      (EqA:=PEQ)
      (EqB:=SysEQ); try apply SC.getObjTuple_eq; auto.
    (* the meat of the theorem *)
    unfold option_map1_compat_op.
    intros.
    apply SC.addObjTuple_eq; auto.
    unfold SC.update_pair_label.
    repeat progress destruct a1; destruct a'1.
    repeat progress destruct p0.
    repeat progress destruct p.
    repeat progress destruct H3.
    (* TODO: really want a remove and relabel eq *)
    unfold Sys.P.eq.
    simpl in *.
    repeat progress split; auto.
    (* and the case where things are not equal *)
    eapply Sys.eq_trans. eapply Sem.destroy_invalid; auto.    
    eapply Sys.eq_sym. eapply Sys.eq_trans;[ eapply Sem.destroy_invalid; auto|auto].
    intro n'. apply n.
    eapply SemDefns.destroy_preReq_eq_iff in n'; eauto.
  Qed.

  Theorem do_read_eq : forall a a' t t' s s',
    Sys.eq s s' ->
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq (Sem.do_read a t s) (Sem.do_read a' t' s').
  Proof.
    intros.
    eapply Sys.eq_trans. eapply Sem.read_spec; auto.
    eapply Sys.eq_sym. eapply Sys.eq_trans. eapply Sem.read_spec; auto.
    eapply Sys.eq_sym; auto.
  Qed.

  Theorem do_write_eq : forall a a' t t' s s',
    Sys.eq s s' ->
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq (Sem.do_write a t s) (Sem.do_write a' t' s').
  Proof.
    intros.
    eapply Sys.eq_trans. eapply Sem.write_spec; auto.
    eapply Sys.eq_sym. eapply Sys.eq_trans. eapply Sem.write_spec; auto.
    eapply Sys.eq_sym; auto.
  Qed.

Theorem do_fetch_eq : forall a a' t t' c c' i i' s s',
    Sys.eq s s' ->
    Ref.eq a a' ->
    Ind.eq t t' ->
    Ind.eq c c' ->
    Ind.eq i i' ->
    Sys.eq (Sem.do_fetch a t c i s) (Sem.do_fetch a' t' c' i' s').
  Proof.
    intros.
    case (SemDefns.fetch_preReq_dec a t s); simpl; intros.
    (* case where preReq occurs *)
    generalize f; intros [Hf Hf'].
    case (SemDefns.option_hasRight_dec (SC.getCap t a s) rd); intros Hread.
    (* read case *)
    eapply Sys.eq_trans. eapply Sem.fetch_read; auto.
    eapply SemDefns.fetch_preReq_eq_iff in f;
      [|apply Ref.eq_sym in H0; apply H0
       |apply Ind.eq_sym in H1; apply H1
       |apply Sys.eq_sym in H; apply H].
    eapply Sys.eq_sym. eapply Sys.eq_trans. eapply Sem.fetch_read; auto.
    eapply SemDefns.option_hasRight_eq;
     [eapply Ind.eq_sym; eauto | apply Ref.eq_sym; eauto | apply Sys.eq_sym; eauto | apply AccessRight.eq_refl | eauto].
    
    
    eapply option_map1_Equiv with
      (EqA := RefEQ) 
      (EqB := SysEQ); try apply SemDefns.option_target_eq; try apply Ref.eq_sym; auto.
    (* probably a new theorem here *)
    unfold option_map1_compat_op.
    intros.
    unfold SC.copyCap.
    eapply option_map1_Equiv with
      (EqA := CapEQ)
      (EqB := SysEQ); try apply SC.getCap_eq; auto.
    (* probably a new theorem here *)
    unfold option_map1_compat_op.
    intros.
    unfold SC.addCap.
    eapply option_map1_Equiv with
      (EqA := ObjEQ)
      (EqB := SysEQ); try apply SC.getObj_eq; try apply Ref.eq_sym; auto.
    (* probably a new theorem here *)
    unfold option_map1_compat_op.
    intros.
    unfold SC.updateObj.
    eapply option_map1_Equiv with
      (EqA := PEQ)
      (EqB := SysEQ); try apply SC.getObjTuple_eq; try apply Ref.eq_sym; auto.
    (* probably a new theroem here *)
    unfold option_map1_compat_op.
    intros.
    (* And here is the meat of the theorem *)
    unfold SC.addObjTuple.
    unfold SC.update_pair_object. 
    repeat progress destruct a3; destruct a'3.
    repeat progress destruct p0.
    repeat progress destruct p.
    repeat progress destruct H7.
    apply SC.addObjTuple_eq; try apply Ref.eq_sym; auto.
    simpl in *.
    unfold Sys.P.eq. 
    simpl.
    repeat progress split; auto.
    apply OC.addCap_eq; auto.
    (* now the weak case *)
    destruct Hf' as [Hf'|Hf']; try contradiction.

    eapply Sys.eq_trans. eapply Sem.fetch_weak; auto.
    eapply SemDefns.fetch_preReq_eq_iff in f;
      [|apply Ref.eq_sym in H0; apply H0
       |apply Ind.eq_sym in H1; apply H1
       |apply Sys.eq_sym in H; apply H].
    eapply Sys.eq_sym. eapply Sys.eq_trans. eapply Sem.fetch_weak; auto.
    intro n; apply Hread.
    eapply SemDefns.option_hasRight_eq; try apply AccessRight.eq_refl; eauto. 
    eapply SemDefns.option_hasRight_eq;
      [eapply Ind.eq_sym; eauto | apply Ref.eq_sym; eauto | apply Sys.eq_sym; eauto | apply AccessRight.eq_refl | auto].

    eapply option_map1_Equiv with
      (EqA := RefEQ) 
      (EqB := SysEQ); try apply SemDefns.option_target_eq; try apply Ref.eq_sym; auto.
    (* probably a new theorem here *)
    unfold option_map1_compat_op.
    intros.
    unfold SC.copyCap.
    eapply option_map1_Equiv with
      (EqA := CapEQ)
      (EqB := SysEQ); try apply SC.getCap_eq; try apply Ref.eq_sym; auto.
    (* probably a new theorem here *)
    unfold option_map1_compat_op.
    intros.
    unfold SC.addCap.
    eapply option_map1_Equiv with
      (EqA := ObjEQ)
      (EqB := SysEQ); try apply SC.getObj_eq; try apply Ref.eq_sym; auto.
    (* probably a new theorem here *)
    unfold option_map1_compat_op.
    intros.
    unfold SC.updateObj.
    eapply option_map1_Equiv with
      (EqA := PEQ)
      (EqB := SysEQ); try apply SC.getObjTuple_eq; try apply Ref.eq_sym; auto.
    (* probably a new theroem here *)
    unfold option_map1_compat_op.
    intros.
    (* And here is the meat of the theorem *)
    unfold SC.addObjTuple.
    unfold SC.update_pair_object. 
    repeat progress destruct a3; destruct a'3.
    repeat progress destruct p0.
    repeat progress destruct p.
    repeat progress destruct H7.
    apply SC.addObjTuple_eq; try apply Ref.eq_sym; auto.
    unfold Sys.P.eq. 
    simpl in *.
    repeat progress split; auto.
    apply OC.addCap_eq; auto.
    (* need a weaken_eq theorem *)
    apply CC.weaken_equiv; auto.
    (* and the case where things are not equal *)
    eapply Sys.eq_trans. eapply Sem.fetch_invalid; auto.    
    eapply Sys.eq_sym. eapply Sys.eq_trans;[ eapply Sem.fetch_invalid; auto|auto].
    intro n'. apply n.
    eapply SemDefns.fetch_preReq_eq_iff in n'; eauto.
  Qed.

  Theorem do_allocate_eq : forall a a' n n' i i' cil cil' s s',
    Sys.eq s s' ->
    Ref.eq a a' ->
    Ref.eq n n' ->
    Ind.eq i i' ->
    CIL_Facts.cil_eq cil cil' ->
    Sys.eq (Sem.do_allocate a n i cil s) (Sem.do_allocate a' n' i' cil' s').
  Proof.
    intros.
    case (SemDefns.allocate_preReq_dec a n s); simpl; intros.

    (* case where preReq occurrs *)
    eapply Sys.eq_trans. eapply Sem.allocate_valid; auto.
    eapply SemDefns.allocate_preReq_eq_iff in a0;
      [|apply Ref.eq_sym in H0; apply H0
       |apply Ref.eq_sym in H1; apply H1
       |apply Sys.eq_sym in H; apply H].
    eapply Sys.eq_sym.  eapply Sys.eq_trans.  eapply Sem.allocate_valid; auto.
    unfold SC.set_alive.
    unfold SC.set_label.
    
    Hint Resolve SC.addCap_eq.
    Hint Resolve ARSet.eq_refl.
    Hint Resolve Cap.mkCap_eq.

    apply SC.addCap_eq; try apply Ref.eq_sym; auto.  eapply Cap.mkCap_eq; split. 
    eapply Ref.eq_trans. 
      eapply Ref.eq_trans. 
        eapply Ref.eq_sym; apply H1. 
        apply Ref.eq_sym; eapply CC.mkCap_target. 
      auto.
    eapply ARSet.eq_trans.
      eapply ARSet.eq_sym. eapply CC.mkCap_rights.
      auto.
    apply SC.copyCapList_eq; try apply Ref.eq_sym; auto. (* generalize CIL_Facts.cil_Equiv; intros [_ sym _].  apply sym. auto. *)

    (* apply SC.copyCapList_eq; auto.
       apply SC.addCap_eq; auto;  [eapply Cap.mkCap_eq; split; [rewrite CC.mkCap_target]| rewrite mkCap_rights]; eauto|]. *)

    apply option_map1_Equiv with
      (EqA:=PEQ)
      (EqB:=SysEQ); try solve [apply SC.updateObj_eq; try apply Obj.eq_refl; eauto].

    
    (* option_map1_compat_op case *)
    unfold option_map1_compat_op; intros.
    apply SC.addObjTuple_eq; try apply SC.copyCapList_eq; try apply Ref.eq_sym; eauto.
    unfold SC.update_pair_label.
    repeat progress destruct a1; destruct a'0. 
    repeat progress destruct H4.
    repeat progress destruct p0.
    repeat progress destruct p.
    unfold Sys.P.eq.
    simpl in *.
    repeat progress split; auto.
    Hint Immediate Sys.eq_sym.
    apply SC.updateObj_eq; try apply Obj.eq_refl; try apply SC.rmCapsByTarget_eq; try apply Ref.eq_sym; eauto.
    apply SC.updateObj_eq; try apply Obj.eq_refl; try apply SC.rmCapsByTarget_eq; try apply Ref.eq_sym; eauto.

(*    apply SC.updateObj_eq; try apply Obj.eq_refl; try apply SC.rmCapsByTarget_eq; eauto. *)
    (* option_map_eq case *)
    eapply Sys_MapEquiv.find_eq; eauto.
    eapply SC.updateObj_eq; try apply Obj.eq_refl; try apply SC.rmCapsByTarget_eq; try apply Ref.eq_sym; eauto.

    (* and the case where things are not equal *)
    eapply Sys.eq_trans. eapply Sem.allocate_invalid; auto.
    assert (~ SemDefns.allocate_preReq a' n' s'). intro. eapply n0.

    eapply SemDefns.allocate_preReq_eq_iff in H4; eauto.
    eapply Sys.eq_sym.  eapply Sys.eq_trans.  eapply Sem.allocate_invalid; auto. apply Sys.eq_sym; auto.
  Qed.


  Theorem do_op_eq : forall op s s',
    Sys.eq s s' -> Sys.eq (Sem.do_op op s) (Sem.do_op op s').
  Proof.
    intros.
    destruct op; auto;
     first [apply do_read_eq | apply do_write_eq | apply do_fetch_eq | apply do_store_eq | apply do_revoke_eq | apply do_send_eq | apply do_allocate_eq | apply do_destroy_eq]; auto; try apply Ref.eq_refl;
    try (destruct CIL_Facts.cil_Equiv as [refl _ _]; apply refl);
      try (destruct (option_map_eq_Equiv Ind.eq IndEQ) as [refl _ _]; apply refl).
  Qed.

  Import RefS.

  Theorem Proper_read_from_def: Proper (Sys.eq ==> eq ==> RefSet.eq ==> impl) Sem.read_from_def.
  Proof.
    unfold Proper; unfold respectful; unfold impl.
    intros s s' Hs op op' Hop r r' Hr Hrf.

    Require Import OptionSumbool.

    (* Heq = H0 , HpreReq = H Hempty = H0 *)
    (* The first two cases solve the branches of odd constructors, the last two for even *)
    Ltac solve_occurrance op_preReq_eq_iff Hr Heq a t s s' Hs HpreReq Hempty:= solve
      [ eapply op_preReq_eq_iff; eauto; try apply Ref.eq_refl
        | eapply RefSet.eq_trans; [| apply Hr];
          eapply RefSet.eq_trans; [| apply Heq];
            try apply RefSet.eq_refl;
              unfold Sem.add_option_target;
                let Hcap := fresh "Hcap" in
                  let Hcase := fresh "Hcase" in
                    let Hcase' := fresh "Hcase'" in
                      generalize (SC.getCap_eq _ _ _ _ _ _ Hs (Ind.eq_refl t) (Ref.eq_refl a)); intros Hcap;
                        case (option_sumbool (SC.getCap t a s));intros Hcase; 
                          [|destruct Hcase as [cap Hcase]];rewrite Hcase in *;
                            (case (option_sumbool (SC.getCap t a s'));intros Hcase'; 
                              [|destruct Hcase' as [cap' Hcase']];rewrite Hcase' in *); 
                            simpl in *; try solve 
                              [apply RefSet.eq_refl 
                                | contradiction
                                | apply Cap.target_eq in Hcap; rewrite Hcap; apply RefSet.eq_refl]
        | intros Hnot; apply HpreReq; eapply op_preReq_eq_iff; eauto; try apply Ref.eq_refl
        | eapply RefSetFacts.Empty_m; [apply RefSet.eq_sym; apply Hr| apply Hempty] 
      ].
    destruct Hrf; rewrite <- Hop in *;
      [ constructor 1; solve_occurrance SemDefns.read_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 2; solve_occurrance SemDefns.read_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 3; solve_occurrance SemDefns.write_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 4; solve_occurrance SemDefns.write_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 5; solve_occurrance SemDefns.fetch_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 6; solve_occurrance SemDefns.fetch_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 7; solve_occurrance SemDefns.store_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 8; solve_occurrance SemDefns.store_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 9; solve_occurrance SemDefns.revoke_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 10; solve_occurrance SemDefns.revoke_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 11; solve_occurrance SemDefns.send_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 12; solve_occurrance SemDefns.send_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 13; solve_occurrance SemDefns.allocate_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 14; solve_occurrance SemDefns.allocate_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 15; solve_occurrance SemDefns.destroy_preReq_eq_iff Hr H0 a t s s' Hs H H0
        | constructor 16; solve_occurrance SemDefns.destroy_preReq_eq_iff Hr H0 a t s s' Hs H H0
      ].
  Qed.

  Theorem Proper_wrote_to_def: Proper (Sys.eq ==> eq ==> RefSet.eq ==> impl) Sem.wrote_to_def.
  Proof.
    unfold Proper; unfold respectful; unfold impl.
    intros s s' Hs op op' Hop w w' Hw Hwt.
    destruct Hwt; rewrite <- Hop in *;
      [ constructor 1; solve_occurrance SemDefns.read_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 2; solve_occurrance SemDefns.read_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 3; solve_occurrance SemDefns.write_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 4; solve_occurrance SemDefns.write_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 5; solve_occurrance SemDefns.fetch_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 6; solve_occurrance SemDefns.fetch_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 7; solve_occurrance SemDefns.store_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 8; solve_occurrance SemDefns.store_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 9; solve_occurrance SemDefns.revoke_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 10; solve_occurrance SemDefns.revoke_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 11; solve_occurrance SemDefns.send_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 12; solve_occurrance SemDefns.send_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 13; solve_occurrance SemDefns.allocate_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 14; solve_occurrance SemDefns.allocate_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 15; solve_occurrance SemDefns.destroy_preReq_eq_iff Hw H0 a t s s' Hs H H0
        | constructor 16; solve_occurrance SemDefns.destroy_preReq_eq_iff Hw H0 a t s s' Hs H H0
      ].
  Qed.


End MakeSemanticsConv.
