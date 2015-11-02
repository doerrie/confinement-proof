Require Import OptionMap2.
Require Import Sumbool_dec.
Require Import SystemState_Conv.
Require Import SystemState_ConvImpl.
Require Import FMapFacts.
Require Import Iff_Equiv.
Require Import AccessRights.
Require Import AccessRightSets.
(* type_remove *)
Require Import SemanticsDefinitions.
Require Import References.
Require Import Capabilities.
Require Import Indices.
Require Import Objects.
Require Import SystemState.


Module MakeSemanticsDefns (Ref:ReferenceType) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) : SemanticsDefinitionsType Ref Cap Ind Obj Sys.

  Module SC := MakeSysStConv Ref Cap Ind Obj Sys.
  Module OC := SC.OC.
  Module CC := SC.CC.

  Definition CapEQ := CC.CapEQ.
  Definition ObjEQ := OC.ObjEQ.
  Definition RefEQ := CC.RefEQ.
  Definition IndEQ := OC.IndEQ.
  Definition PEQ := SC.PEQ.

  Definition option_target opt_cap :=
    option_map Cap.target opt_cap.

  Definition target_is_alive i o s :=
    option_map1 (fun tgt => SC.is_alive tgt s) False (option_target (SC.getCap i o s)).

  Definition preReqCommon a s :=
    SC.is_alive a s /\ SC.is_active a s.

  Definition preReq a t s :Prop := 
    preReqCommon a s /\ target_is_alive t a s.

  Definition option_hasRight opt_cap rgt:=
    option_map1 (fun cap => CC.hasRight cap rgt) False opt_cap.

  Definition read_preReq a t s := 
    preReq a t s /\ (option_hasRight (SC.getCap t a s) rd \/ option_hasRight (SC.getCap t a s) wk).
  Definition write_preReq a t s := preReq a t s /\ option_hasRight (SC.getCap t a s) wr.
  Definition fetch_preReq a t s := 
    preReq a t s /\ (option_hasRight (SC.getCap t a s) rd \/ option_hasRight (SC.getCap t a s) wk).
  Definition store_preReq a t s := preReq a t s /\ option_hasRight (SC.getCap t a s) wr.
  Definition revoke_preReq a t s := preReq a t s /\ option_hasRight (SC.getCap t a s) wr.
  Definition send_preReq a t s := preReq a t s /\ option_hasRight (SC.getCap t a s) tx.
  Definition allocate_preReq a n s := preReqCommon a s /\ SC.is_unborn n s.
  Definition destroy_preReq a t s := preReq a t s /\ option_hasRight (SC.getCap t a s) wr.

  Theorem target_is_alive_dec: forall i o s, {target_is_alive i o s} + {~ target_is_alive i o s}.
  Proof.
    intros.
    unfold target_is_alive.
    unfold option_target.
    destruct (SC.getCap i o s); simpl; auto.
  Qed.

  Hint Resolve target_is_alive_dec.

  Theorem preReqCommon_dec: forall a s, {preReqCommon a s} + {~ preReqCommon a s}.
  Proof.
    intros; unfold preReqCommon; Sumbool_decide; eauto.
  Qed.
  Hint Resolve preReqCommon_dec.

  Theorem preReq_dec: forall a t s, {preReq a t s} + {~ preReq a t s}.
  Proof.
    intros; unfold preReq; Sumbool_decide; eauto.
  Qed.

  Theorem option_hasRight_dec: forall opt_cap rgt,
    {option_hasRight opt_cap rgt} + {~ option_hasRight opt_cap rgt}.
  Proof.
    intros.
    destruct opt_cap; simpl; auto.
    unfold CC.hasRight; apply ARSetProps.In_dec.
  Qed.

  Hint Resolve preReq_dec option_hasRight_dec.

  Theorem read_preReq_dec : forall a t s, 
    {read_preReq a t s} + {~ read_preReq a t s}.
  Proof.
    intros; unfold read_preReq; Sumbool_decide; eauto.
  Qed.

  Theorem write_preReq_dec : forall a t s, 
    {write_preReq a t s} + {~ write_preReq a t s}.
  Proof.
    intros; unfold write_preReq; Sumbool_decide; eauto.
  Qed.

  Theorem fetch_preReq_dec : forall a t s, 
    {fetch_preReq a t s} + {~ fetch_preReq a t s}.
  Proof.
    intros; unfold fetch_preReq; Sumbool_decide; eauto.  
  Qed.
  
  Theorem store_preReq_dec : forall a t s, 
    {store_preReq a t s} + {~ store_preReq a t s}.
  Proof.
    intros; unfold store_preReq; Sumbool_decide; eauto.  
  Qed.

  Theorem revoke_preReq_dec : forall a t s, 
    {revoke_preReq a t s} + {~ revoke_preReq a t s}.
  Proof.
    intros; unfold revoke_preReq; Sumbool_decide; eauto.  
  Qed.

  Theorem send_preReq_dec : forall a t s, 
    {send_preReq a t s} + {~ send_preReq a t s}.
  Proof.
    intros; unfold send_preReq; Sumbool_decide; eauto.  
  Qed.

  Theorem allocate_preReq_dec : forall a n s, 
    {allocate_preReq a n s} + {~ allocate_preReq a n s}.
  Proof.
    intros; unfold allocate_preReq; Sumbool_decide; eauto.  
  Qed.

  Theorem destroy_preReq_dec : forall a t s, 
    {destroy_preReq a t s} + {~ destroy_preReq a t s}.
  Proof.
    intros; unfold destroy_preReq; Sumbool_decide; eauto.
  Qed.

  Theorem option_target_eq: forall i i' o o' s s',
    Sys.eq s s' -> Ref.eq o o' -> Ind.eq i i' ->
    option_map_eq Ref.eq (option_target (SC.getCap i o s))
    (option_target (SC.getCap i' o' s')).
  Proof.
    intros.
    unfold option_target.
    rewrite option_map_is_option_map1.
    rewrite option_map_is_option_map1.
    eapply option_map1_Equiv with
      (EqA := CapEQ)
      (EqB := (option_map_eq_Equiv _ RefEQ)).  
    unfold option_map1_compat_op; intros.
    (* case 1 *)
    unfold option_map_eq; unfold option_map2.
    eapply Cap.target_eq; auto.
    (* case 2 *)
    unfold option_map_eq; unfold option_map2; trivial.
    (* case 3 *)
    apply SC.getCap_eq; auto.
  Qed.
    

  Theorem target_is_alive_eq : forall o o' i i' s s',
      Ref.eq o o' ->
      Ind.eq i i' ->
      Sys.eq s s' ->
      (target_is_alive i o s <-> target_is_alive i' o' s').
  Proof.
    intros.
    unfold target_is_alive.
    eapply option_map1_Equiv with
      (eqA := Ref.eq)
      (eqB := iff).
    unfold option_map1_compat_op; intros.
    unfold SC.is_alive.
    split; apply SC.isLabel_eq; auto with *.
    apply Sys.eq_sym; auto.
    split; auto.
    apply option_target_eq; auto.
  Qed.

(*    option_map_eq iff (option_hasRight (SC.getCap t a s) r) (option_hasRight (SC.getCap t' a' s') r'). *)

  Theorem option_hasRight_eq: forall t t' a a' s s' r r',
    Ind.eq t t' -> Ref.eq a a' -> Sys.eq s s' -> AccessRight.eq r r' ->
    (option_hasRight (SC.getCap t a s) r <-> option_hasRight (SC.getCap t' a' s') r').
  Proof.
    intros.
    unfold AccessRight.eq in H2.
    rewrite <- H2.
    unfold option_hasRight in *.
    eapply option_map1_Equiv with
      (EqA := CapEQ)
      (EqB := iff_Equiv).
    (* case 1 *)
    unfold option_map1_compat_op; intros.
    unfold CC.hasRight; apply Cap.rights_eq; auto.
    (* case 2 *)
    tauto.
    (* case 3 *)
    apply SC.getCap_eq; auto.
  Qed.

  (* type_remove*)
  Theorem preReqCommon_eq : Proper (Ref.eq ==> Sys.eq ==> impl) preReqCommon.
  Proof.
    unfold Proper; unfold respectful; unfold impl; unfold preReqCommon;
      intros a a' Ha s s' Hs [H1 H2]; split; eauto.
    eapply SC.is_active_eq; eauto.
  Qed.

  (* type_remvoe *)
  Theorem preReqCommon_Proper : Proper (Ref.eq ==> Sys.eq ==> iff) preReqCommon.
  Proof.
    split; intros; eapply preReqCommon_eq; eauto; try apply Ref.eq_sym; try apply Sys.eq_sym; eauto.
  Qed.

  Theorem preReqCommon_eq_iff: forall a a' s s',
    Ref.eq a a' -> Sys.eq s s' ->
    (preReqCommon a s <-> preReqCommon a' s').
  Proof.
    generalize preReqCommon_Proper; unfold Proper; unfold respectful; auto.
  Qed.
    
(* type_remove *)
  Theorem preReq_eq : forall a a' t t' s s',
    Ref.eq a a' -> Ind.eq t t' -> Sys.eq s s' ->
    preReq a t s -> preReq a' t' s'.
  Proof.
    intros.
    unfold preReq in *.
    destruct H2 as [H2 H3].
    split.
    eapply preReqCommon_eq; eauto.
    generalize (target_is_alive_eq a a' t t' s s' H H0 H1); intros H5. destruct H5. auto.
  Qed.

  Theorem preReq_eq_iff: forall a a' t t' s s',
    Ref.eq a a' -> Ind.eq t t' -> Sys.eq s s' ->
    (preReq a t s <-> preReq a' t' s').
  Proof.
    intros.
    split; intros.
    eapply preReq_eq; eauto.
    eapply preReq_eq; apply Sys.eq_sym in H1; apply Ind.eq_sym in H0; apply Ref.eq_sym in H; eauto.
  Qed.

(* type_remove *)
  Theorem read_preReq_eq : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    (read_preReq a t s) -> (read_preReq a' t' s').
  Proof.
    intros.
    unfold read_preReq.
    destruct H2 as [Hi Hi'].
    split.  eapply preReq_eq; eauto.
    destruct Hi' as [Hi'|Hi']; [left|right];
    (eapply option_hasRight_eq;
      [eapply Ind.eq_sym; eauto
      |apply Ref.eq_sym; eauto 
      |apply Sys.eq_sym; eauto 
      |apply AccessRight.eq_refl
      |auto]).
  Qed.


  Theorem read_preReq_eq_iff : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    ((read_preReq a t s) <-> (read_preReq a' t' s')).
  Proof.
    intros; split; intros.
    eapply read_preReq_eq; eauto.
    eapply read_preReq_eq; apply Ref.eq_sym in H; apply Ind.eq_sym in H0; apply Sys.eq_sym in H1; eauto.
  Qed.


(* type_remove *)
  Theorem write_preReq_eq : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    (write_preReq a t s) -> (write_preReq a' t' s').
  Proof.
    intros.
    unfold write_preReq.
    destruct H2 as [Hi Hi'].
    split.  eapply preReq_eq; eauto.
    apply (option_hasRight_eq _ _ _ _ _ _ _ _ H0 H H1 (refl_equal AccessRights.wr)); auto.
  Qed.


  Theorem write_preReq_eq_iff : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    ((write_preReq a t s) <-> (write_preReq a' t' s')).
  Proof.
    intros; split; intros.
    eapply write_preReq_eq; eauto.
    eapply write_preReq_eq; apply Ref.eq_sym in H; apply Ind.eq_sym in H0; apply Sys.eq_sym in H1; eauto.
  Qed.

(* type_remove *)
  Theorem revoke_preReq_eq : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    (revoke_preReq a t s) -> (revoke_preReq a' t' s').
  Proof.
    intros.
    unfold revoke_preReq.
    destruct H2 as [Hi Hi'].
    split.  eapply preReq_eq; eauto.
    apply (option_hasRight_eq _ _ _ _ _ _ _ _ H0 H H1 (refl_equal AccessRights.wr)); auto.
  Qed.


  Theorem revoke_preReq_eq_iff : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    ((revoke_preReq a t s) <-> (revoke_preReq a' t' s')).
  Proof.
    intros; split; intros.
    eapply revoke_preReq_eq; eauto.
    eapply revoke_preReq_eq; apply Ref.eq_sym in H; apply Ind.eq_sym in H0; apply Sys.eq_sym in H1; eauto.
  Qed.

(* type_remove *)
  Theorem destroy_preReq_eq : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    (destroy_preReq a t s) -> (destroy_preReq a' t' s').
  Proof.
    intros.
    unfold destroy_preReq.
    destruct H2 as [Hi Hi'].
    split.  eapply preReq_eq; eauto.
    apply (option_hasRight_eq _ _ _ _ _ _ _ _ H0 H H1 (refl_equal AccessRights.wr)); auto.
  Qed.

  Theorem destroy_preReq_eq_iff : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    ((destroy_preReq a t s) <-> (destroy_preReq a' t' s')).
  Proof.
    intros; split; intros.
    eapply destroy_preReq_eq; eauto.
    eapply destroy_preReq_eq; apply Ref.eq_sym in H; apply Ind.eq_sym in H0; apply Sys.eq_sym in H1; eauto.
  Qed.


(* type_remove *)
  Theorem send_preReq_eq : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    (send_preReq a t s) -> (send_preReq a' t' s').
  Proof.
    intros.
    unfold send_preReq.
    destruct H2 as [Hi Hi'].
    split.  eapply preReq_eq; eauto.
    apply (option_hasRight_eq _ _ _ _ _ _ _ _ H0 H H1 (refl_equal AccessRights.tx)); auto.
  Qed.

  Theorem send_preReq_eq_iff : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    ((send_preReq a t s) <-> (send_preReq a' t' s')).
  Proof.
    intros; split; intros.
    eapply send_preReq_eq; eauto.
    eapply send_preReq_eq; apply Ref.eq_sym in H; apply Ind.eq_sym in H0;
      apply Sys.eq_sym in H1; eauto. 
  Qed.


(* type_remove *)
  Theorem allocate_preReq_eq : forall a a' n n' s s',
    Ref.eq a a' ->
    Ref.eq n n' ->
    Sys.eq s s' ->
    (allocate_preReq a n s) -> (allocate_preReq a' n' s').
  Proof.
    intros a a' n n' s s' H H0 H1 H2.
    unfold allocate_preReq.
    destruct H2 as [Hi Hi'].
    split.
    eapply preReqCommon_eq; eauto.
    eapply SC.isUnborn_eq; eauto.    
  Qed.

  Theorem allocate_preReq_eq_iff : forall a a' n n' s s',
    Ref.eq a a' ->
    Ref.eq n n' ->
    Sys.eq s s' ->
    ((allocate_preReq a n s) <-> (allocate_preReq a' n' s')).
  Proof.
    intros; split; intros.
    eapply allocate_preReq_eq; eauto.
    eapply allocate_preReq_eq; apply Ref.eq_sym in H; apply Ref.eq_sym in H0;
      apply Sys.eq_sym in H1; eauto. 
  Qed.

(* type_remove *)
Theorem store_preReq_eq : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    (store_preReq a t s) -> (store_preReq a' t' s').
  Proof.
    intros.
    unfold store_preReq.
    destruct H2 as [Hi Hi'].
    split.  eapply preReq_eq; eauto.
    apply (option_hasRight_eq _ _ _ _ _ _ _ _ H0 H H1 (refl_equal AccessRights.wr)); auto.
  Qed.

  Theorem store_preReq_eq_iff : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    ((store_preReq a t s) <-> (store_preReq a' t' s')).
  Proof.
    intros; split; intros.
    eapply store_preReq_eq; eauto.
    eapply store_preReq_eq; apply Ref.eq_sym in H; apply Ind.eq_sym in H0; apply Sys.eq_sym in H1; eauto.
  Qed.

(* type_remove *)
Theorem fetch_preReq_eq : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    (fetch_preReq a t s) -> (fetch_preReq a' t' s').
  Proof.
    intros.
    unfold fetch_preReq.
    destruct H2 as [Hi Hi'].
    split.  eapply preReq_eq; eauto.
    destruct Hi'.
    left; apply (option_hasRight_eq _ _ _ _ _ _ _ _ H0 H H1 (refl_equal AccessRights.rd)); auto.
    right; apply (option_hasRight_eq _ _ _ _ _ _ _ _ H0 H H1 (refl_equal AccessRights.wk)); auto.
  Qed.

  Theorem fetch_preReq_eq_iff : forall a a' t t' s s',
    Ref.eq a a' ->
    Ind.eq t t' ->
    Sys.eq s s' ->
    ((fetch_preReq a t s) <-> (fetch_preReq a' t' s')).
  Proof.
    intros; split; intros.
    eapply fetch_preReq_eq; eauto.
    eapply fetch_preReq_eq; apply Ref.eq_sym in H; apply Ind.eq_sym in H0; apply Sys.eq_sym in H1; eauto.
  Qed.

  Definition preReq_bool a t s : bool := true_bool_of_sumbool (preReq_dec t a s).
  Definition option_hasRight_bool opt_cap rgt : bool := true_bool_of_sumbool (option_hasRight_dec opt_cap rgt).

End MakeSemanticsDefns.
