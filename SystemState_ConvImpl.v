(* type_remove *)
Require Import SystemState_Conv.
Require Import SystemState.
Require Import OptionMap2.
Require CapIndexListFacts.
Require Objects_Conv.
Require Capabilities_Conv.
Require Import FMapExists.
Require Import OrdFMapEquiv.
Require Import FMapFacts2.
Require Import ObjectLabels.
Require Import ObjectTypes.
Require Import ObjectSchedules.
Require Import OptionSumbool.
Require Import OrderedTypeEquiv.
Require FMapFoldEqual.
Require Import References.
Require Import Indices.
Require Import Capabilities.
Require Import Objects.
Require Import Objects_Conv.
Require Import Objects_ConvImpl.
Require Import Capabilities_Conv.
Require Import Capabilities_ConvImpl.
Require Import OrdFMapEquiv.
Require Import FMapAdd.
(* must be last *)
Require Import FMapInterface2.

Module MakeSysStConv (Ref:ReferenceType) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) : SystemStateConv Ref Cap Ind Obj Sys.
  
  Module OC := MakeObjConv Ref Cap Ind Obj.
  Module CC := MakeCapConv Ref Cap.
  Module ObjFacts := OC.Obj_Facts.

  Definition getObjTuple (r:Ref.t) (s:Sys.t) : option Sys.P.t := Sys.MapS.find r s.
  Definition addObjTuple (r:Ref.t) (p:Sys.P.t) (s:Sys.t) : Sys.t := Sys.MapS.add r p s.
  Definition rmObjTuple (r:Ref.t) (s:Sys.t) : Sys.t := Sys.MapS.remove r s.

  Module Sys_OrdProps := OrdProperties_fun Ref Sys.MapS.
  Module Sys_Props := Sys_OrdProps.P.
  Module Sys_Facts := Sys_Props.F.
  Module Sys_MapEquiv := OrdFMapEquiv.MakeEquiv_fun Ref Sys.MapS Sys.P Sys.
  Module Sys_FoldEqual := FMapFoldEqual.Make_fun Ref Sys.MapS Sys.P Sys.
  Module Sys_Exists := MakeExists_fun Ref Sys.MapS Sys.P Sys.
  Module Sys_Equiv := OT_Equiv Sys.
  Module Sys_OrdAdd := MakeAdd Ref Sys.MapS Sys.P Sys.

  Module P_Equiv := OT_Equiv Sys.P.

  Module Obj_Exists := OC.Obj_Exists.
  Module Obj_MapEquiv := OC.Obj_MapEquiv.

  Module CIL_Facts := CapIndexListFacts.mkFacts Ind.
  Import CIL_Facts.

  Definition SysEQ := Sys_Equiv.Equiv.
  Definition PEQ := P_Equiv.Equiv.
  Definition CapEQ := CC.CapEQ.
  Definition RefEQ := CC.RefEQ.
  Definition IndEQ := OC.IndEQ.
  Definition ObjEQ := OC.ObjEQ.


  (* Just a specialization of Sys_MapEquiv.find_eq *)
  Theorem getObjTuple_eq: forall r r' s s',
    Ref.eq r r' ->
    Sys.eq s s' ->
    option_map_eq Sys.P.eq (getObjTuple r s) (getObjTuple r' s').
  Proof.
    intros; apply Sys_MapEquiv.find_eq; auto.
  Qed.
    

  Definition update_pair_label (p:Sys.P.t) (l:ObjectLabel.t) :=
    match p with
      (o, _, t, d) => (o, l, t, d)
    end.

  Definition update_pair_type (p:Sys.P.t) (t:ObjectType.t) :=
    match p with
      (o, l, _, d) => (o, l, t, d)
    end.

  Definition update_pair_schedule (p:Sys.P.t) (d:ObjectSchedule.t) :=
    match p with
      (o, l, t, _) => (o, l, t, d)
    end.

  Definition update_pair_object (p:Sys.P.t) (o:Obj.t) :=
    match p with
      (_, l, t, d) => (o, l, t, d)
    end.

  Definition tupleGetObj (p:Sys.P.t) := 
    match p with
      (o, _, _, _) => o
    end.

  Definition tupleGetLabel (p:Sys.P.t) := 
    match p with
      (_, l, _, _) => l
    end.

  Definition tupleGetType (p:Sys.P.t) := 
    match p with
      (_, _, t, _) => t
    end.

  Definition tupleGetSchedule (p:Sys.P.t) := 
    match p with
      (_, _, _, d) => d
    end.

  Definition getObj (r:Ref.t) (s:Sys.t) : (option Obj.t) := option_map tupleGetObj (getObjTuple r s).
  Definition getLabel (r:Ref.t) (s:Sys.t) : (option ObjectLabel.t) := option_map tupleGetLabel (getObjTuple r s).
  Definition getType (r:Ref.t) (s:Sys.t) : (option ObjectType.t) := option_map tupleGetType (getObjTuple r s).
  Definition getSched (r:Ref.t) (s:Sys.t) : (option ObjectSchedule.t) := option_map tupleGetSchedule (getObjTuple r s).


  Theorem addObjTuple_eq : forall r r' p p' s s',
    Ref.eq r r' ->
    Sys.P.eq p p' ->
    Sys.eq s s' ->
    Sys.eq (addObjTuple r p s) (addObjTuple r' p' s').
  Proof.
    (* tactic is nearly identical to addCap_eq, please generalize *)
    intros.
    unfold addObjTuple.
    apply Sys.eq_1.
    unfold Sys.MapS.Equivb.
    unfold Sys.MapS.Equiv.
    unfold Cmp.
    apply Sys.eq_2 in H1.
    unfold Sys.MapS.Equivb in H1.
    unfold Sys.MapS.Equiv in H1.
    unfold Cmp in H1.
    destruct H1.
    split; intros. 
    split; intros.
    (*case 1 *)
    eapply Sys_Facts.add_in_iff.
    apply Sys_Facts.add_in_iff in H3.
    destruct H3.
    (* case 1.1 *)
    left.
    apply Ref.eq_trans with r; auto.
    (* case 1.2 *)
    right.
    eapply H1; assumption.
    (* case 2, identical to case 1 *)
    eapply Sys_Facts.add_in_iff.
    apply Sys_Facts.add_in_iff in H3.
    destruct H3.
    (* case 2.1 *)
    left.
    apply Ref.eq_trans with r'; auto.
    (* case 2.2 *)
    right.
    eapply H1; assumption.
    (* case 3 *)
    (* need to show C.eq e e' *)
    apply Sys_Facts.add_mapsto_iff in H3.
    apply Sys_Facts.add_mapsto_iff in H4.
    destruct H3; destruct H4; destruct H3; destruct H4.
    (* case 3.1 *)
    unfold Sys.cmp in *.
    generalize (Sys.P.compare e e'); intros CMP.
    destruct CMP as [CMP|CMP|CMP]; rewrite H5 in H0; rewrite H6 in H0.
       apply Sys.P.lt_not_eq in CMP; contradiction.
       trivial. 
       apply Sys.P.lt_not_eq in CMP; apply Sys.P.eq_sym in H0; contradiction.
    (* case 3.2 *)
    unfold Sys.cmp in *.
    generalize (Sys.P.compare e e'); intros CMP.
    apply Ref.eq_sym in H.
    apply Ref.eq_trans with (x:= r') (y:= r) (z:= k) in H; auto.
    (* case 3.3 *)
    unfold Sys.cmp in *.
    generalize (Sys.P.compare e e'); intros CMP.
    apply Ref.eq_trans with (x:= r) (y:= r') (z:= k) in H; auto.
    (* case 3.4 *)
    apply H2 with k; auto.
  Qed.

  Theorem removeObjTuple_eq : forall r r' s s',
    Ref.eq r r' ->
    Sys.eq s s' ->
    Sys.eq (rmObjTuple r s) (rmObjTuple r' s').
  Proof.
    (* again, tactic is nearly identical to removeCap_eq, please generalize to Fmaps*)
    intros.
    unfold rmObjTuple.
    apply Sys.eq_1.
    unfold Sys.MapS.Equivb.
    unfold Sys.MapS.Equiv.
    unfold Cmp.
    split; intros. 
    split; intros.
    (*case 1 *)
    eapply Sys_Facts.remove_in_iff.
    eapply Sys_Facts.remove_in_iff in H1.
    destruct H1.
    split.
    (* case 1.1 *)
    intro.
    apply Ref.eq_trans with (x:=r) (y:=r') (z:=k) in H3; try contradiction; auto.
    (* case 1.2 *)
    eapply Sys.eq_2; [apply Sys.eq_sym; apply H0 | auto].
    (* case 2, similar to case 1 *)
    eapply Sys_Facts.remove_in_iff.
    eapply Sys_Facts.remove_in_iff in H1.
    destruct H1.
    split.
    (* case 2.1 *)
    intro.
    apply Ref.eq_sym in H; apply Ref.eq_trans with (x:=r') (y:=r) (z:=k) in H3; try contradiction; auto.
    (* case 2.2 *)
    eapply Sys.eq_2; [apply H0 |auto].
    (* case 3 *)
    apply Sys.eq_2 in H0.
    unfold Sys.MapS.Equivb in H0.
    unfold Sys.MapS.Equiv in H0.
    unfold Cmp in H0.
    destruct H0.
    (* need to show C.eq e e' *)
    apply Sys_Facts.remove_mapsto_iff in H1.
    apply Sys_Facts.remove_mapsto_iff in H2.
    destruct H1; destruct H2.
    apply H3 with k; auto.
  Qed.
  


  (* this should be a special case of OptionMap Equivelences *)

  Theorem getObj_eq: forall r r' s s',
    Sys.eq s s' -> 
    Ref.eq r r' ->
    option_map_eq Obj.eq (getObj r s) (getObj r' s').
  Proof.
    intros.
    unfold getObj.
    progress (repeat rewrite option_map_is_option_map1).
    eapply option_map1_Equiv with
    (EqA := PEQ)
    (EqB := (option_map_eq_Equiv _ ObjEQ)).
    (* case 1 *)
    unfold option_map1_compat_op; intros.
    progress (repeat let x := fresh x in destruct a as [a x]).
    progress (repeat let x := fresh x in destruct a' as [a' x]).
    simpl in H1.
    progress (repeat let H := fresh H in destruct H1 as [H1 H]; try rewrite H).
    simpl; auto.
    (* case 2 *)
    simpl; auto.
    (* case 3 *)
    eapply getObjTuple_eq; auto.
  Qed.

  Definition addUnbornObj (r:Ref.t) (o:Obj.t) (t:ObjectType.t) (d:ObjectSchedule.t) (s:Sys.t) : Sys.t := 
    addObjTuple r (o,unborn,t,d) s.
  Definition updateObj (r:Ref.t) (o:Obj.t) (s:Sys.t) : Sys.t := 
        option_map1 (fun p:Sys.P.t => addObjTuple r (update_pair_object p o) s) s (getObjTuple r s).
  Definition rmObj (r:Ref.t) (s:Sys.t) : Sys.t := rmObjTuple r s.
  
  Definition is_label (r:Ref.t) (s:Sys.t) (l:ObjectLabel.t) :=
    (* option_map1 (fun p:Sys.P.t => ObjectLabel.eq (tupleGetLabel p) l) False (getObjTuple r s).  *)
    option_map1 (fun l' => ObjectLabel.eq l' l) False (getLabel r s).
  Definition is_unborn r s := is_label r s unborn.
  Definition is_alive r s := is_label r s alive.
  Definition is_dead r s := is_label r s dead.

      Ltac destruct_tuple tuple obj lbl obj_type sched :=
        destruct tuple as [tuple sched]; destruct tuple as [tuple obj_type];
          destruct tuple as [obj lbl].


    (* should go in SC *)
    Theorem getLabel_eq: forall r r' s s',
      Ref.eq r r' -> 
      Sys.eq s s' ->
      option_map_eq ObjectLabel.eq (getLabel r s) (getLabel r' s').
    Proof.
      intros.
      unfold getLabel.
      generalize (getObjTuple_eq _ _ _ _ H H0); intros H3.
      case (option_sumbool (getObjTuple r s)); intros Hopt1;
        [|destruct Hopt1 as [tuple Hopt1]; destruct_tuple tuple obj lbl type sched];
        rewrite Hopt1 in *; simpl in *;
          (case (option_sumbool (getObjTuple r' s')); intros Hopt2;
            [|destruct Hopt2 as [tuple' Hopt2]; destruct_tuple tuple' obj' lbl' type' sched'];
            rewrite Hopt2 in *; simpl in *); auto.
      destruct_tuple H3 H3_1 H3_2 H3_3 H3_4; simpl in *; auto.
    Qed.


  Theorem isLabel_eq: forall r r' s s' l l',
    Ref.eq r r' -> 
    ObjectLabels.ObjectLabel.eq l l' -> 
    Sys.eq s s' ->
    is_label r s l -> is_label r' s' l'.
  Proof.
    intros.
    generalize (getLabel_eq _ _ _ _ H H1); intros H3.
    unfold is_label in *; 
    unfold option_map1 in *; unfold option_map2 in *.
    case (option_sumbool (getLabel r s)); intros Hopt; [rewrite Hopt in *; tauto|].
    destruct Hopt as [p Hopt]; rewrite Hopt in *.
    unfold ObjectLabel.eq in *.
    case (option_sumbool (getLabel r' s')); intros Hopt2; [rewrite Hopt2 in *; tauto|].
    destruct Hopt2 as [p' Hopt2].
    rewrite Hopt2 in *.
    repeat progress destruct H3.
    rewrite H2; auto.
  Qed.

  Theorem is_label_eq_iff: 
    forall o o', Ref.eq o o' -> 
      forall s s', Sys.eq s s' ->
        forall l l', ObjectLabel.eq l l' -> 
          (is_label o s l <-> is_label o' s' l').
  Proof.
    intros.
    split; eapply isLabel_eq; eauto; solve [apply Ref.eq_sym; auto | apply ObjectLabel.eq_sym; auto | apply Sys.eq_sym; auto].
  Qed.
      
  Theorem is_label_dec : forall a s l, {is_label a s l} + {~ is_label a s l}.
  Proof.
    intros.
    unfold is_label.
    destruct (getLabel a s); simpl; auto.
    apply ObjectLabels.ObjectLabel.eq_dec.
  Qed.

  Hint Resolve is_label_dec.

  Theorem is_alive_dec: forall a s, {is_alive a s} + {~ is_alive a s}.
  Proof.
    intros.
    unfold is_alive.
    auto.
  Qed.

  Hint Resolve is_alive_dec.

  Theorem is_unborn_dec : forall a s , {is_unborn a s} + {~ is_unborn a s}.
  Proof.
    intros.
    unfold is_unborn.
    auto.
  Qed.

  Hint Resolve is_unborn_dec.

  Theorem is_dead_dec : forall a s , {is_dead a s} + {~ is_dead a s}.
  Proof.
    intros.
    unfold is_dead.
    auto.
  Qed.
  
  Hint Resolve is_dead_dec.

  Hint Resolve isLabel_eq.

  Theorem isAlive_eq:  forall r r' s s',
    Ref.eq r r' -> Sys.eq s s' -> is_alive r s -> is_alive r' s'.
  Proof.
    intros; unfold is_alive; eapply isLabel_eq; eauto;  apply ObjectLabel.eq_refl.
  Qed.
  
  Hint Resolve isAlive_eq.

  Theorem isUnborn_eq:  forall r r' s s',
    Ref.eq r r' -> Sys.eq s s' -> is_unborn r s -> is_unborn r' s'.
  Proof.
    intros; unfold is_unborn; eapply isLabel_eq; eauto;  apply ObjectLabel.eq_refl.
  Qed.
  
  Hint Resolve isUnborn_eq.

  Theorem isDead_eq:  forall r r' s s',
    Ref.eq r r' -> Sys.eq s s' -> is_dead r s -> is_dead r' s'.
  Proof.
    intros; unfold is_dead; eapply isLabel_eq; eauto;  apply ObjectLabel.eq_refl.
  Qed.
  
  Hint Resolve isDead_eq.

  Definition set_label (r:Ref.t) (s:Sys.t) (l:ObjectLabel.t) :=
    option_map1 (fun p:Sys.P.t => addObjTuple r (update_pair_label p l) s) s (getObjTuple r s).
  Definition set_unborn r s := set_label r s unborn.
  Definition set_alive r s := set_label r s alive.
  Definition set_dead r s := set_label r s dead.

  Definition getCap i o s := option_map1 (fun o => OC.getCap i o) None (getObj o s).

  Theorem getCap_eq: forall i i' o o' s s',
    Sys.eq s s' ->
    Ind.eq i i' -> 
    Ref.eq o o' ->
    option_map_eq Cap.eq (getCap i o s) (getCap i' o' s').
  Proof.
    intros.
    unfold getCap.
    generalize (getObj_eq _ _ _ _ H H1); intros.
    case (option_sumbool (getObj o s)); intros Hopt; 
      first [rewrite Hopt in * | destruct Hopt as [ob Hopt]; rewrite Hopt in *];
        case (option_sumbool (getObj o' s')); intros Hopt';
          first [ rewrite Hopt' in *; auto; simpl in *; tauto
            | destruct Hopt' as [ob' Hopt']; rewrite Hopt' in *; simpl in *; auto; try tauto 
            | auto]; apply OC.getCap_eq; auto.
  Qed.

    (* FIXME: go back and use this where you are destructing cases for legibility *)
    Theorem getCap_split : forall s o i cap, getCap i o s = Some cap <->
      exists tuple, getObjTuple o s = Some tuple /\ OC.getCap i (tupleGetObj tuple) = Some cap.
    Proof.
      unfold getCap; unfold getObj; intros; split; intros.
      case (option_sumbool (getObjTuple o s)); intros Hcase; [|destruct Hcase as [tuple Hcase]];
        rewrite Hcase in *; simpl in *; solve [discriminate
          | eapply ex_intro; split; eauto].
      destruct H as [tuple [Htuple HgetCap]].
      rewrite Htuple; auto.
    Qed.


  Definition is_type (r:Ref.t) (s:Sys.t) (t:ObjectType.t) :=
     option_map1 (fun p:Sys.P.t => ObjectType.eq (tupleGetType p) t) False (getObjTuple r s).
  Definition is_active r s := is_type r s active.
  Definition is_passive r s := is_type r s passive.

  Theorem is_type_dec : forall a s d, {is_type a s d} + {~ is_type a s d}.
  Proof.
    intros.
    unfold is_type.
    destruct (getObjTuple a s); simpl; auto.
    apply ObjectTypes.ObjectType.eq_dec.
  Qed.
  
  Hint Resolve is_type_dec.

  Theorem is_active_dec : forall a s, {is_active a s} + {~ is_active a s}.
  Proof.
    intros; unfold is_active; auto.
  Qed.

  Theorem is_passive_dec : forall a s, {is_passive a s} + {~ is_passive a s}.
  Proof.
    intros; unfold is_passive; auto.
  Qed.
  
  Hint Resolve is_active_dec is_passive_dec.


  Theorem isType_eq: forall r r' s s' l l',
    Ref.eq r r' -> 
    ObjectTypes.ObjectType.eq l l' -> 
    Sys.eq s s' ->
    is_type r s l -> is_type r' s' l'.
  Proof.
    intros.
    generalize (getObjTuple_eq _ _ _ _ H H1); intros H3.
    unfold is_type in *.
    unfold option_map1 in *; unfold option_map2 in *.
    case (option_sumbool (getObjTuple r s)); intros Hopt; [rewrite Hopt in *; tauto|].
    destruct Hopt as [p Hopt]; rewrite Hopt in *.
    unfold ObjectType.eq in *.
    case (option_sumbool (getObjTuple r' s')); intros Hopt2; [rewrite Hopt2 in *; tauto|].
    destruct Hopt2 as [p' Hopt2].
    rewrite Hopt2 in *.
    repeat progress destruct H3.
    repeat progress destruct p' as [p'].
    repeat progress destruct p as [p].
    simpl in *.
    rewrite <- H5.
    rewrite <- H0.
    auto.
  Qed.

Hint Resolve isType_eq.

Theorem is_active_eq : Proper (Ref.eq ==> Sys.eq ==> impl) is_active.
Proof.
  unfold Proper; unfold respectful; unfold impl; unfold is_active; intros r r' Hr s s' Hs H1.
  eapply isType_eq; eauto; eapply ObjectType.eq_refl.
Qed.

Hint Resolve is_active_eq.


Theorem is_passive_eq : Proper (Ref.eq ==> Sys.eq ==> impl) is_passive.
Proof.
  unfold Proper; unfold respectful; unfold impl; unfold is_passive; intros r r' Hr s s' Hs H1.
  eapply isType_eq; eauto; eapply ObjectType.eq_refl.
Qed.

Hint Resolve is_passive_eq.


  Definition is_schedule (r:Ref.t) (s:Sys.t) (d:ObjectSchedule.t) :=
     option_map1 (fun p:Sys.P.t => ObjectSchedule.eq (tupleGetSchedule p) d) False (getObjTuple r s).
  Definition is_running r s := is_schedule r s running.
  Definition is_blocked r s := is_schedule r s blocked.

  Definition addCap i cap o s :=  
    option_map1 (fun ob => (updateObj o (OC.addCap i cap ob) s)) s (getObj o s).
  Definition copyCap i o i' o' s :=
    option_map1 (fun cap => addCap i' cap o' s) s (getCap i o s).
  Definition copyCapList o o' (ixi_list: list (Ind.t * Ind.t)) s :=
    fold_right (fun ixi s => copyCap (fst ixi) o (snd ixi) o' s) s ixi_list.
  Definition weakCopyCap i o i' o' s :=
    option_map1 (fun cap => addCap i' (Cap.weaken cap) o' s) s (getCap i o s).
  Definition rmCap i o s :=
    option_map1 (fun ob => (updateObj o (OC.rmCap i ob) s)) s (getObj o s).

  Definition rmCapsByTarget (t:Ref.t) (s:Sys.t) :=
    Sys.MapS.fold (fun ref p s' => 
      addObjTuple ref (update_pair_object p (OC.rmCapsByTarget t (tupleGetObj p))) s')
    s (Sys.MapS.empty _).

  Theorem addCap_eq : forall i i' cap cap' o o' s s',
    Ind.eq i i' -> Cap.eq cap cap' -> Ref.eq o o' -> Sys.eq s s' ->
    Sys.eq (addCap i cap o s) (addCap i' cap' o' s').
  Proof.
    intros.
    unfold addCap.
    unfold updateObj.
    generalize (getObj_eq _ _ _ _ H2 H1); intros.
    case (option_sumbool (getObj o s)); intros Hopt; [|destruct Hopt as [obj Hopt]]; rewrite Hopt in *; simpl in *;
      (case (option_sumbool (getObj o' s')); intros Hopt'; [|destruct Hopt' as [obj' Hopt']]; rewrite Hopt' in *; simpl in *;
        try contradiction; auto).
    generalize (getObjTuple_eq _ _ _ _ H1 H2); intros.
    case (option_sumbool (getObjTuple o s)); intros Hopt2; 
      [|destruct Hopt2 as [tuple Hopt2]]; rewrite Hopt2 in *; simpl in *;
        (case (option_sumbool (getObjTuple o' s')); intros Hopt2'; 
          [|destruct Hopt2' as [tuple' Hopt2']]; rewrite Hopt2' in *; simpl in *;
            try contradiction; auto).
    apply addObjTuple_eq; auto.
    destruct tuple as [tuple t]; destruct tuple as [tuple d]; destruct tuple as [l t_obj];
    destruct tuple' as [tuple' t']; destruct tuple' as [tuple' d']; destruct tuple' as [l' t_obj'].
    unfold Sys.P.eq in *; simpl in *; intuition.
    eapply OC.addCap_eq; auto.
  Qed.

    Theorem update_pair_object_eq: forall p p' o o',
      Sys.P.eq p p' ->
      Obj.eq o o' ->
      Sys.P.eq (update_pair_object p o) (update_pair_object p' o').
    Proof.
      intros.
      destruct_tuple p o_ l t s. destruct_tuple p' o_' l' t' s'. 
      unfold update_pair_object.
      unfold Sys.P.eq in *.
      intuition.
    Qed.

    Theorem addObjTuple_transpose_neqkey: forall k k' e e' a,
      ~ Ref.eq k k' ->
      Sys.eq (addObjTuple k e (addObjTuple k' e' a)) 
      (addObjTuple k' e' (addObjTuple k e a)).
    Proof.
      intros.
      unfold addObjTuple.
      apply Sys.eq_1.
      unfold Sys.MapS.Equivb.
      unfold Sys.MapS.Equiv.
      split; intros.
      (* case In <-> In *)
      split; intros;
      (eapply Sys_Facts.add_in_iff;
       destruct H0; eapply Sys_Facts.add_mapsto_iff in H0; destruct H0; destruct H0;
       [ right; rewrite H0; eapply Sys_Facts.add_in_iff; intuition eauto
       | eapply Sys_Facts.add_mapsto_iff in H1; destruct H1; destruct H1;
         [ auto
         | right; eapply Sys_Facts.add_in_iff; right; eapply ex_intro; eapply H2]]).
      
      (* case Cmp Obj.cmp *)
      unfold Cmp; unfold Sys.cmp.
      apply Sys_Facts.add_mapsto_iff in H0; destruct H0 as [[HeqK HeqE]|[HneqK Hmap]];
        apply Sys_Facts.add_mapsto_iff in H1; destruct H1 as [[HeqK' HeqE']|[HneqK' Hmap']];
          try (apply Sys_Facts.add_mapsto_iff in Hmap'; destruct Hmap' as [[HeqK'' HeqE'']|[HneqK'' Hmap'']]);
            try (apply Sys_Facts.add_mapsto_iff in Hmap; destruct Hmap as [[HeqK''' HeqE''']|[HneqK''' Hmap''']]);
              try rewrite HeqK in *; try rewrite HeqK' in *; try contradiction (H (Ref.eq_refl _));
                destruct (Sys.P.compare e0 e'0); eauto;
                  apply Sys.P.lt_not_eq in l; 
                    try rewrite <- HeqE in l; try rewrite HeqE'' in l; 
                      try rewrite <- HeqE''' in l; try rewrite HeqE' in l; 
                        try rewrite (Sys_Facts.MapsTo_fun Hmap'' Hmap''') in l; 
                          eauto; try contradiction (l (Sys.P.eq_refl _)).
    Qed.

  Theorem rmCapsByTarget_eq: forall r r' s s',
    Ref.eq r r' ->
    Sys.eq s s' ->
    Sys.eq (rmCapsByTarget r s) (rmCapsByTarget r' s').
  Proof.
    unfold rmCapsByTarget.
    intros.
  

    apply Sys_FoldEqual.fold_foldEqual with (m := s) (m' := s'); auto.
  
    (* Equiv *)
    split; unfold Reflexive; unfold Symmetric; unfold Transitive; intros;
      try apply Sys.eq_refl; auto; try apply Sys.eq_sym; auto; try eapply Sys.eq_trans; apply Sys.eq_sym; eauto.
    (* eq empty *)
    apply Sys.eq_refl.
    (* Sys_FoldEqual *)
    unfold Sys_FoldEqual.foldEqual.
    intros.
    eapply addObjTuple_eq; auto.

    
    apply update_pair_object_eq; eauto.
    apply OC.rmCapsByTarget_eq; eauto.
    destruct_tuple v o l t d; destruct_tuple v' o' l' t' d'.
    intuition.

  (* transpose_neqkey *)
    unfold Sys_FoldEqual.Props.transpose_neqkey.
    intros.
    eapply addObjTuple_transpose_neqkey;eauto.
Qed.

Hint Resolve rmCapsByTarget_eq.

(* we need a little more than this, the tuples must be related in all but object. *)
  Theorem rmCapsByTarget_2_a: forall n tuple r s i c,
    Sys.MapS.MapsTo n tuple (rmCapsByTarget r s) /\ Obj.MapS.MapsTo i c (tupleGetObj tuple) -> 
    exists tuple', (tupleGetLabel tuple) = (tupleGetLabel tuple') /\
      (tupleGetType tuple) = (tupleGetType tuple') /\
      (tupleGetSchedule tuple) = (tupleGetSchedule tuple') /\
      Sys.MapS.MapsTo n tuple' s /\ Obj.MapS.MapsTo i c (tupleGetObj tuple').
  Proof.
    intros n tuple r s i c.
    unfold rmCapsByTarget.
    eapply Sys_Props.fold_rec_bis with 
      (P:= fun m A => Sys.MapS.MapsTo n tuple A /\ Obj.MapS.MapsTo i c (tupleGetObj tuple) ->
        exists tuple', (tupleGetLabel tuple) = (tupleGetLabel tuple') /\
          (tupleGetType tuple) = (tupleGetType tuple') /\
          (tupleGetSchedule tuple) = (tupleGetSchedule tuple') /\
          Sys.MapS.MapsTo n tuple' m /\ Obj.MapS.MapsTo i c (tupleGetObj tuple')).
    (* equiv *)
    intros.
    destruct H0 as [tuple' H0]. apply H1.
    eapply ex_intro with tuple'; intros. 
    intuition auto.
    eapply Sys.MapS.find_1 in H5; eapply Sys.MapS.find_2; rewrite H in H5; apply H5; auto.
    (* base *)
    intros; eapply ex_intro with tuple; intuition eauto;
      try apply ObjectLabel.eq_refl; try apply ObjectType.eq_refl; try apply ObjectSchedule.eq_refl.
    (* step *)
    intros k tuple2 a s'.
    intros.
    destruct H2.
    (* cases on n[=|<>] k *)
    unfold addObjTuple in H2.
    apply Sys_Facts.add_mapsto_iff in H2. destruct H2 as [[Heq Hieq]|[Hneq Hmap]].
    (* case k [=] n *)
    eapply ex_intro with tuple2; auto.
    destruct_tuple tuple2 o2 l2 t2 d2; simpl in *.
    destruct_tuple tuple o l t d; simpl in *.
    inversion Hieq.
    intuition (try apply ObjectLabel.eq_refl; try apply ObjectType.eq_refl; try apply ObjectSchedule.eq_refl; auto);
      solve [eapply Sys_Facts.add_mapsto_iff; intuition auto 
        | rewrite <- H4 in *; eapply OC.rmCapsByTarget_2; eauto].
    (* case k [<>] n *)
    destruct H1 as [tuple' H1]; auto.
    apply ex_intro with tuple'; intuition auto.
    eapply Sys_Facts.add_mapsto_iff; intuition.
  Qed.

  Theorem rmCapsByTarget_2: forall n o l t d r s i c,
    Sys.MapS.MapsTo n (o,l,t,d) (rmCapsByTarget r s) /\ Obj.MapS.MapsTo i c o -> 
    exists o', Sys.MapS.MapsTo n (o',l,t,d) s /\ Obj.MapS.MapsTo i c o'.
  Proof.
    intros.
    generalize (rmCapsByTarget_2_a n (o,l,t,d) r s i c); intros H2a.
    simpl in H2a.
    destruct H2a as [tuple H2a]; auto.
    destruct H2a as [H2a_1 [H2a_2 [H2a_3 [H2a_4 H2a_5]]]].
    destruct_tuple tuple o' l' t' d'. simpl in *.
    apply ex_intro with o'.
    intuition.
    rewrite H2a_1; rewrite H2a_2; rewrite H2a_3; auto.
  Qed.
  (* the reason the induction didn't work is because o should really be a forall 
     inducted over in fold_rec_bis.  Encapsulating in tuple captures this relationship
     in cases where it can not succeed. *)

  Hint Resolve rmCapsByTarget_2.

  Theorem rmCapsByTarget_1: forall r n l t d s i c ,
    ~ Ref.eq (Cap.target c) r -> 
    forall o, Sys.MapS.MapsTo n (o,l,t,d) s /\ Obj.MapS.MapsTo i c o ->
      exists o', Sys.MapS.MapsTo n (o',l,t,d) (rmCapsByTarget r s) /\ Obj.MapS.MapsTo i c o'.
  Proof.
    intros r n l t d s i c Hneq.
    unfold rmCapsByTarget; unfold addCap.
    eapply Sys_Props.fold_rec_bis with
      (P:= fun m A => 
        forall o, Sys.MapS.MapsTo n (o,l,t,d) m /\ Obj.MapS.MapsTo i c o ->
          exists o', Sys.MapS.MapsTo n (o',l,t,d) A /\ Obj.MapS.MapsTo i c o');
      intros; eauto.
    (* Equiv *)
    destruct H1 as [H1 H2];
      eapply Sys_Facts.find_mapsto_iff in H1; rewrite <- H in H1;
        eapply Sys_Facts.find_mapsto_iff in H1; eapply (H0 o); intuition auto.
    (* step *)
    destruct H2 as [H2 H3].
    destruct_tuple e o' l' t' d'; simpl in *.
    apply Sys_Facts.add_mapsto_iff in H2; destruct H2 as [[Heq Heq']|[Heq Hmap]].
    (* k [=] n *)
    inversion Heq'.
    apply ex_intro with (OC.rmCapsByTarget r o').
    rewrite H4.
    split;
       [eapply Sys_Facts.add_mapsto_iff; intuition auto |
       eapply OC.rmCapsByTarget_1; auto].
    (* k [<>] n *)
    destruct (H1 o) as [o2 IH]; intuition auto.
    apply ex_intro with o2; intuition auto.
    eapply Sys_Facts.add_mapsto_iff; intuition auto.
  Qed.

  Hint Resolve rmCapsByTarget_1.

  Theorem rmCapsByTarget_3: forall r s n l t d i c,
    Ref.eq (Cap.target c) r -> 
    forall o, Sys.MapS.MapsTo n (o,l,t,d) s /\ Obj.MapS.MapsTo i c o ->
    ~ exists o', exists c',
      Cap.eq c c' /\ Sys.MapS.MapsTo n (o',l,t,d) (rmCapsByTarget r s) /\ Obj.MapS.MapsTo i c' o'.
  Proof.
    intros r s n l t d i c Heq.
    unfold rmCapsByTarget.
    eapply Sys_Props.fold_rec_bis with 
      (P:= fun m A => 
        forall o, Sys.MapS.MapsTo n (o, l, t, d) m /\ Obj.MapS.MapsTo i c o ->
        ~ exists o', exists c',
            Cap.eq c c' /\ Sys.MapS.MapsTo n (o', l, t, d) A /\ Obj.MapS.MapsTo i c' o');
      intros; eauto.
    (* equiv *)
    eapply H0; destruct H1; apply Sys.MapS.find_1 in H1;
      rewrite <- H in H1;  apply Sys.MapS.find_2 in H1; eauto.
    (* empty *)
    unfold not; intro H0; destruct H0 as [o' [ c' [H0 [H1 H2]]]].
    eapply Sys_Facts.empty_mapsto_iff in H1; auto.
    (* step *)
    destruct H2 as [H2 H3].
    destruct_tuple e o' l' t' d'; simpl in *.
    apply Sys_Facts.add_mapsto_iff in H2; destruct H2 as [[HMeq Heq']|[HMeq Hmap]];
      (* common tactics *)
    intro Hnot;
      destruct Hnot as [not_o' [not_c' [Hnot3 [Hnot1 Hnot2]]]];
        apply Sys_Facts.add_mapsto_iff in Hnot1; destruct Hnot1 as [[Hn1eq Hn1eq']|[Hn1eq Hn1map]];
          try solve [contradiction | eapply H1; intuition eauto].
    (* k [<>] n handled above *)
    (* k [=] n *)
    inversion Hn1eq'.
    eapply OC.rmCapsByTarget_3; rewrite <- H4 in *;
      generalize (Cap.target_eq _ _ Hnot3); intros HeqR';
        [eapply Ref.eq_trans in HeqR'; [|apply Ref.eq_sym; apply Heq]; apply Ref.eq_sym in HeqR'; apply HeqR'
          | eapply OC.rmCapsByTarget_2; apply Hnot2
          | apply ex_intro with not_c'; split; [intuition| eapply Hnot2]].
  Qed.

  Hint Resolve rmCapsByTarget_3.

  Definition rmCapsByTarget_spec_in (s s':Sys.t) := forall n,
    Sys.MapS.In n s' <-> Sys.MapS.In n s.

  Definition rmCapsByTarget_spec_mapsto (s s': Sys.t) := forall (n:Ref.t) (l:ObjectLabel.t) (t:ObjectType.t) (d:ObjectSchedule.t),
    (exists o', exists l', exists t', exists d', 
      ObjectLabel.eq l l' /\ ObjectType.eq t t' /\ ObjectSchedule.eq d d' /\ Sys.MapS.MapsTo n (o',l',t',d') s') <->
    (exists o', exists l', exists t', exists d',
      ObjectLabel.eq l l' /\ ObjectType.eq t t' /\ ObjectSchedule.eq d d' /\ Sys.MapS.MapsTo n (o',l',t',d') s).

  Definition rmCapsByTarget_spec_not_in (s s': Sys.t) := forall (n:Ref.t) i (l:ObjectLabel.t) (t:ObjectType.t) (d:ObjectSchedule.t) o,
    Sys.MapS.MapsTo n (o,l,t,d) s /\ ~ Obj.MapS.In i o ->
    (exists o', exists l', exists t', exists d',
      ObjectLabel.eq l l' /\ ObjectType.eq t t' /\ ObjectSchedule.eq d d' /\ 
      Sys.MapS.MapsTo n (o',l',t',d') s' /\ ~ Obj.MapS.In i o').
  
  Definition rmCapsByTarget_spec_not_target r s s' := forall n i c (l:ObjectLabel.t) (t:ObjectType.t) (d:ObjectSchedule.t),
    ((exists o', exists l', exists t', exists d', exists c',
      ObjectLabel.eq l l' /\ ObjectType.eq t t' /\ ObjectSchedule.eq d d' /\ Cap.eq c c' /\
      Sys.MapS.MapsTo n (o',l',t',d') s' /\ Obj.MapS.MapsTo i c' o') <->
     (exists o', exists l', exists t', exists d', exists c',
      ObjectLabel.eq l l' /\ ObjectType.eq t t' /\ ObjectSchedule.eq d d' /\ Cap.eq c c' /\
      Sys.MapS.MapsTo n (o',l',t',d') s /\ Obj.MapS.MapsTo i c' o' /\ ~ Ref.eq (Cap.target c) r)).

  Definition rmCapsByTarget_spec r s s' :=  
    rmCapsByTarget_spec_in s s' /\ rmCapsByTarget_spec_mapsto s s' /\ 
    rmCapsByTarget_spec_not_in s s' /\ rmCapsByTarget_spec_not_target r s s'.
  (* why so many exists?  because of equiv *)

  Theorem rmCapsByTarget_spec_not_target_rmCapsByTarget: forall r s , 
    rmCapsByTarget_spec_not_target r s (rmCapsByTarget r s).
  Proof.
    unfold rmCapsByTarget_spec; intros; split; intros. 
    destruct H as [o' [l' [t' [d' [c' [H [H1 [H2 [H3 H4]]]]]]]]].
    (* direct *)
    case (Ref.eq_dec (Cap.target c) r); intros Hcase;
      destruct (rmCapsByTarget_2 _ _ _ _ _ _ _ _ _ H4) as [o2 Hrm2];
        apply ex_intro with o2;
          apply ex_intro with l'; apply ex_intro with t'; 
            apply ex_intro with d'; apply ex_intro with c';
              try solve [intuition].
    (* (target c) [<>] r solved by above.
       (target c) [=] r, has a contradiction by rmCapsByTarget_3 *)
    (* keep Hrm2 intact for later.  Destruct only if auto solves on a branch *)
    repeat progress (split ; try solve [destruct Hrm2; auto]). 
    (* contradiction *)
    generalize (Cap.target_eq _ _ H3); intros HeqC.
    eapply Ref.eq_trans in HeqC; [|apply Ref.eq_sym; apply Hcase]; apply Ref.eq_sym in HeqC.
    intro Hnot; eapply (rmCapsByTarget_3 _ _ _ _ _ _ _ _ HeqC _ Hrm2).
      apply ex_intro with o'; apply ex_intro with c'; intuition.
    (* converse *)
    destruct H as [o' [l' [t' [d' [c' [H [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]]]].
    assert (~ Ref.eq (Cap.target c') r) as Hnoteq;
      [intros Hnot; apply H6; eapply Ref.eq_trans; [apply (Cap.target_eq _ _ H3) | apply Hnot] |].
    destruct (rmCapsByTarget_1 r n l' t' d' s i c' Hnoteq o') as [o2 Hgoal]; [split; auto|].
    apply ex_intro with o2;
      apply ex_intro with l'; apply ex_intro with t'; 
        apply ex_intro with d'; apply ex_intro with c';
          solve [intuition auto].
  Qed.
  Hint Resolve rmCapsByTarget_spec_not_target_rmCapsByTarget.

  Theorem rmCapsByTarget_mapsto_1: forall r s n l t d o,
    Sys.MapS.MapsTo n (o,l,t,d) s ->
    exists o', exists l', exists t', exists d', 
      ObjectLabel.eq l l' /\ ObjectType.eq t t' /\ ObjectSchedule.eq d d' /\
      Sys.MapS.MapsTo n (o',l',t',d') (rmCapsByTarget r s).
  Proof.
    intros r s n l t d.
    unfold rmCapsByTarget.
    (* induction *)
    eapply Sys_Props.fold_rec_bis with 
      (P:= (fun m A => forall o,
        Sys.MapS.MapsTo n (o, l, t, d) m ->
        exists o' : Obj.MapS.t Cap.t,
          exists l' : ProjectedObjectLabel.t,
            exists t' : ProjectedObjectType.t,
              exists d' : ProjectedObjectSchedule.t,
                 ObjectLabel.eq l l' /\
                 ObjectType.eq t t' /\
                 ObjectSchedule.eq d d' /\
                Sys.MapS.MapsTo n (o', l', t', d') A)); intros; eauto.
    (* compat *)
    eapply H0; eapply Sys_Facts.find_mapsto_iff; eapply Sys_Facts.find_mapsto_iff in H1. 
    unfold Sys.MapS.Equal in H; rewrite H in *; apply H1.
    (* base *)
    eapply Sys_Facts.empty_mapsto_iff in H; contradiction.
    (* step *)
    eapply Sys_Facts.add_mapsto_iff in H2; destruct H2 as [[Hkeq Hpeq]|[H2 H2']].
    (* k [=] n *)
    rewrite Hkeq in *; rewrite Hpeq in *.
    unfold addObjTuple; unfold update_pair_object; unfold tupleGetObj; simpl.
    apply ex_intro with (OC.rmCapsByTarget r o); apply ex_intro with l;
      apply ex_intro with t; apply ex_intro with d.
    intuition (solve [eapply Sys_Facts.add_mapsto_iff; auto 
      | apply ObjectLabel.eq_refl | apply ObjectType.eq_refl | apply ObjectSchedule.eq_refl]).
    (* k [<>] n *)
    generalize (H1 _ H2'); intros [o' [l' [t' [d' [Heql [Heqt [Heqd Hmap']]]]]]].
    apply ex_intro with o'; apply ex_intro with l';
      apply ex_intro with t'; apply ex_intro with d'.
    repeat progress (split; auto);
      eapply Sys_Facts.add_mapsto_iff; auto.
  Qed.

Theorem rmCapsByTarget_mapsto_2: forall r s n l t d o,
  Sys.MapS.MapsTo n (o,l,t,d) (rmCapsByTarget r s) ->
  exists o', exists l', exists t', exists d', 
    ObjectLabel.eq l l' /\
    ObjectType.eq t t' /\
    ObjectSchedule.eq d d' /\
    Sys.MapS.MapsTo n (o',l',t',d') s.
Proof.
  intros r s n l t d.
    unfold rmCapsByTarget.
    eapply Sys_Props.fold_rec_nodep; intros; eauto.
    (* base *)
    eapply Sys_Facts.empty_mapsto_iff in H.
    contradiction.
    (* step *)
    destruct e as [[[o' l'] t'] d'].
    unfold update_pair_object in *; unfold tupleGetObj in *.
    eapply Sys_Facts.add_mapsto_iff in H1; destruct H1 as [[H1 H1']|[H1 H1']]; eauto.
    (* k [<>] n solved by eauto *)
    (* k [=] n *)
    rewrite H1 in *; injection H1'; intros H2 H3 H4 H5; clear H1'.
      rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
        do 4 (eapply ex_intro).
        do 3 (split ; 
          first [apply ObjectLabel.eq_refl
                |apply ObjectType.eq_refl
                |apply ObjectSchedule.eq_refl 
                |apply H
                |auto]).
  Qed.

Theorem rmCapsByTarget_spec_mapsto_rmCapsByTarget: forall r s , 
    rmCapsByTarget_spec_mapsto s (rmCapsByTarget r s).
Proof.
unfold rmCapsByTarget_spec_mapsto.
intros; split; intros; destruct H as [o' [l' [t' [d' [H1 [H2 [H3 H4]]]]]]];
[generalize (rmCapsByTarget_mapsto_2 _ _ _ _ _ _ _ H4) 
  | generalize (rmCapsByTarget_mapsto_1 r _ _ _ _ _ _ H4)];
intros [o2 [l2 [t2 [d2 [HeqL [HeqT [HeqD Hexists]]]]]]];
eapply ex_intro with o2; eapply ex_intro with l2;
  eapply ex_intro with t2; eapply ex_intro with d2;
(split; [eapply ObjectLabel.eq_trans; [apply H1 | auto] 
  | split; [eapply ObjectType.eq_trans; [apply H2 | auto] 
    | split; [eapply ObjectSchedule.eq_trans; [apply H3 | auto] | auto]]]).
Qed.

Hint Resolve rmCapsByTarget_spec_mapsto_rmCapsByTarget.

Theorem rmCapsByTarget_spec_in_rmCapsByTarget: forall r s,
    rmCapsByTarget_spec_in s (rmCapsByTarget r s).
Proof.
  unfold rmCapsByTarget_spec_in;   intros.
unfold rmCapsByTarget.
eapply Sys_Props.fold_rec_bis with (P:= fun m a => Sys.MapS.In n a <-> Sys.MapS.In n m).
(* compat *)
intros.
unfold Sys.MapS.Equal in *.
unfold Sys.MapS.In in *.
(* eq case *)
split; intros HExMap; [eapply H0 in HExMap | eapply H0]; 
  destruct HExMap as [e HMap]; eapply Sys_Facts.find_mapsto_iff in HMap;
    [rewrite H in HMap| rewrite <- H in HMap];
      eapply Sys_Facts.find_mapsto_iff in HMap;
        eapply ex_intro; apply HMap.
(* empty case *)
intuition eauto.
(* induction *)
intros.
destruct e as [[[o l] t] d]; simpl in *.
unfold addObjTuple.
split; intros Hmap;
apply Sys_Facts.add_in_iff in Hmap;
destruct Hmap as [Hkn | Hin]; eapply Sys_Facts.add_in_iff; intuition.
Qed.

Hint Resolve rmCapsByTarget_spec_in_rmCapsByTarget.

Theorem rmCapsByTarget_spec_none: forall r o o' k, OC.rmCapsByTarget_spec r o o' ->
  ~ Obj.MapS.In k o -> ~ Obj.MapS.In k o'.
Proof.
intros.
unfold Obj.MapS.In in *.
intros Hnot.
apply H0; clear H0.
destruct Hnot as [e Hnot].
eapply H in Hnot.
destruct Hnot as [Hnot Hnot'].
eapply ex_intro.
eauto.
Qed.


Theorem rmCapsByTarget_spec_not_in_rmCapsByTarget: forall r s,
    rmCapsByTarget_spec_not_in s (rmCapsByTarget r s).
Proof.
  unfold rmCapsByTarget_spec_not_in.
intros r s n i l t d.
unfold rmCapsByTarget.
eapply Sys_Props.fold_rec_bis with (P:= fun m a =>
   forall o : Obj.MapS.t Cap.t,
   Sys.MapS.MapsTo n (o, l, t, d) m /\ ~ Obj.MapS.In i o ->
   exists o' : Obj.MapS.t Cap.t,
     exists l' : ObjectLabel.t,
       exists t' : ObjectType.t,
         exists d' : ObjectSchedule.t,
           ObjectLabel.eq l l' /\
           ObjectType.eq t t' /\
           ObjectSchedule.eq d d' /\
           Sys.MapS.MapsTo n (o', l', t', d')a /\
           ~ Obj.MapS.In i o');
 intros; eauto.
(* compat case *)
eapply H0; clear H0.
destruct H1 as [H1 H1'].
apply Sys_Facts.find_mapsto_iff in H1.
rewrite <- H in H1.
apply Sys_Facts.find_mapsto_iff in H1.
split. apply H1. apply H1'.
(* empty case*)
destruct H as [H H'].
eapply Sys_Facts.empty_mapsto_iff in H. contradiction.
(* induction *)
    destruct e as [[[o' l'] t'] d']; simpl in *.
    destruct H2 as [H2 H2'].
    (* apply H1 in H2. *)
    eapply Sys_Facts.add_mapsto_iff in H2. destruct H2 as [[H2_2 H2_2']|[H2_2 H2_2']]; eauto.
    (* k [=] n *)
    rewrite H2_2 in *; injection H2_2'; intros H3 H4 H5 H6. clear H2_2';
      rewrite H3 in *; rewrite H4 in *; rewrite H5 in *.
        do 4 (eapply ex_intro);
          repeat progress (split). 
   unfold addObjTuple.
   eapply Sys_Facts.find_mapsto_iff.
   eapply Sys_Facts.add_eq_o; auto.
   
idtac.
eapply rmCapsByTarget_spec_none.
eapply OC.rmCapsByTarget_spec_rmCapsByTarget.
rewrite H6. auto.
    (* k [<>] n *) 
   generalize (H1 _ (conj H2_2' H2')); clear H1; intros H1.
   destruct H1 as [o2 [l2 [t2 [d2 [Hl [Ht [Hd [Hm Hi]]]]]]]].
   do 4 (eapply ex_intro);
   repeat progress (split; try apply Hl; try apply Ht; try apply Hd; try apply Hi).
   unfold addObjTuple.
   eapply Sys_Facts.find_mapsto_iff.
   rewrite Sys_Facts.add_neq_o; auto.
   eapply Sys_Facts.find_mapsto_iff; auto.
Qed.


Hint Resolve  rmCapsByTarget_spec_not_in_rmCapsByTarget.



Theorem rmCapsByTarget_spec_rmCapsByTarget: forall r s , 
    rmCapsByTarget_spec r s (rmCapsByTarget r s).
Proof.
  intros; repeat progress (split; auto).
Qed.

Hint Resolve rmCapsByTarget_spec_rmCapsByTarget.

 (* An object is safe to make alive when there are no dangling caps to it *)
 (* three properties are necessary lemmas, first rmCapsByTarget_spec n s s' -> safe_to_make_alive n s'
    second {safe_to_make_alive n s} + {~ safe_to_make_alive n s}.
    third, and I want to see the interaction of these theorems to determine how to best write it if necessary,
    is a lemma that adding an existing cap to a safe graph makes a safe graph.
    The usefulness of these predicates will become apparent later. *)


Definition safe_to_make_alive n s :=  ~ (exists r, exists p, Sys.MapS.MapsTo r p s /\ 
  exists i, exists c,Obj.MapS.MapsTo i c (tupleGetObj p) /\ Ref.eq (Cap.target c) n).

Theorem safe_to_make_alive_dec : forall n s, {safe_to_make_alive n s} + {~ safe_to_make_alive n s}.
Proof.
  intros.
  unfold safe_to_make_alive.

   (* Assert decidability of existence for all objects *)
   assert (forall o, 
     { exists k : Obj.MapS.key,
       exists e : Cap.t,
         Obj.MapS.MapsTo k e o /\ Ref.eq (Cap.target e) n} + 
     {~ (exists k : Obj.MapS.key,
       exists e : Cap.t,
         Obj.MapS.MapsTo k e o /\ Ref.eq (Cap.target e) n)}) as HdecOb.
   (* generate decidability of existence for an object. *)
   generalize (Obj_Exists.exists_ (fun i c => Ref.eq (Cap.target c) n)); intros HicEx; 
     unfold Obj_Exists.Exists in *.
   assert ((Obj.MapS.key -> forall e : Cap.t,
     {Ref.eq (Cap.target e) n} + {~ Ref.eq (Cap.target e) n})) as Hdec;
   [intros i e; apply Ref.eq_dec |].
   assert (Obj_Exists.compat_P2 (fun (_ : Obj.MapS.key) (c : Cap.t) => Ref.eq (Cap.target c) n)) as Hcomp;
   [unfold Obj_Exists.compat_P2; intros;
     generalize (Cap.target_eq _ _ H0); intros Heq;
       eapply Ref.eq_trans; [apply Ref.eq_sym; apply Heq | auto]|].
   intros o; eapply HicEx with o in Hdec; clear HicEx.
   destruct Hdec as [Hdec|Hdec]; apply Hdec in Hcomp; [left|right];  apply Hcomp.
   (* decidability for objects done. *)
   (* generate decidability of existence for the system state. *)
   generalize (Sys_Exists.exists_ (fun r p =>  
     exists i : Obj.MapS.key,
       exists c : Cap.t,
         Obj.MapS.MapsTo i c (tupleGetObj p) /\
         Ref.eq (Cap.target c) n)); intros HrpEx;
   unfold Sys_Exists.Exists in *.
   assert (Sys.MapS.key -> forall e : Sys.P.t,
     {(exists i : Obj.MapS.key,
               exists c : Cap.t,
                 Obj.MapS.MapsTo i c (tupleGetObj e) /\
                 Ref.eq (Cap.target c) n)} +
           {~
            (exists i : Obj.MapS.key,
               exists c : Cap.t,
                 Obj.MapS.MapsTo i c (tupleGetObj e) /\
                 Ref.eq (Cap.target c) n)}) as HdecSt;
   [intros i [[[o l] t] d]; simpl in *; eapply HdecOb|].
   apply HrpEx with s in HdecSt; clear HrpEx.

   assert (Sys_Exists.compat_P2 
     (fun (_ : Sys.MapS.key) (p : Sys.P.t) =>
       exists i : Obj.MapS.key,
         exists c : Cap.t,
           Obj.MapS.MapsTo i c (tupleGetObj p) /\
           Ref.eq (Cap.target c) n)) as Hcomp.
   unfold Sys_Exists.compat_P2; 
     intros r r' [[[o l] t] d] [[[o' l'] t'] d'] H [[[H3 H4] H5] H6] [i [c [H1 H2]]]; simpl in *.
   destruct (Obj_MapEquiv.exists_mapsTo_eq _ _ H3 _ _ H1 _ (Ind.eq_refl _)) as [c' [HeqC HmapC]].
   apply ex_intro with i; apply ex_intro with c'; intuition eauto;
     (   eapply Ref.eq_trans; [ | apply H2]; apply Cap.target_eq; auto).
   destruct HdecSt as [HdecSt|HdecSt]; apply HdecSt in Hcomp; clear HdecSt; [right | left]; intuition eauto.    
Qed.

  Theorem safe_to_make_alive_eq : forall n n' s s',
    Ref.eq n n' -> Sys.eq s s' -> safe_to_make_alive n s -> safe_to_make_alive n' s'.
  Proof.
    intros.
    unfold safe_to_make_alive in *.
    intros Hnot; apply H1; clear H1.
    destruct Hnot as [r [p [ HrpMap [i [c [Hmap Heq]]]]]].
    apply ex_intro with r.
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ (Sys.eq_sym H0)
      _ _ HrpMap
      _ (Ref.eq_refl r)) as [p' [HeqP' HmapP']].
    apply ex_intro with p'; intuition auto.
    destruct p as [[[o l] t] d]; destruct p' as [[[o' l'] t'] d']; simpl in *.
    apply ex_intro with i.
    destruct (Obj_MapEquiv.exists_mapsTo_eq
      _ _ H1
      _ _ Hmap
      _ (Ind.eq_refl i)) as [c' [HeqC' HmapC']].
    apply ex_intro with c'.
    intuition eauto.
    generalize (Cap.target_eq _ _ HeqC'); intros HeqT.
    eapply Ref.eq_trans; [apply Ref.eq_sym; apply HeqT |
    eapply Ref.eq_trans; [apply Heq | auto]].
  Qed.

  Theorem safe_to_make_alive_rmCapsByTarget_spec: forall n s s',
    rmCapsByTarget_spec n s s' -> safe_to_make_alive n s'.
  Proof.
    intros.
    destruct H as [_ [_ [_ HrT]]].
    unfold safe_to_make_alive; unfold rmCapsByTarget_spec_mapsto in *;
      unfold rmCapsByTarget_spec_not_target in *.
  (* by contradiction *)
    intro H; destruct H as [r [[[[o l] t] d] [HmapS' [i [c [HmapO HeqT]]]]]]; simpl in *.
    generalize (HrT r i c l t d); clear HrT; intros [HrT _].
    destruct HrT as [o' HrT];[do 5 eapply ex_intro; intuition eauto; try apply ObjectLabel.eq_refl; try apply ObjectSchedule.eq_refl; try apply ObjectType.eq_refl|].
    do 4 (let x := fresh "x" in destruct HrT as [x HrT]).
    intuition eauto.
  Qed.

      Theorem copyCap_eq: 
        forall si si' a a' di di' t t' s s',
          Ind.eq si si' ->
          Ref.eq a a' ->
          Ind.eq di di' ->
          Ref.eq t t' ->
          Sys.eq s s' ->
          Sys.eq (copyCap si a di t s)
          (copyCap si' a' di' t' s').
      Proof.
        intros.
        unfold copyCap.
        eapply option_map1_Equiv with
          (EqA := CapEQ)
          (EqB := SysEQ); try apply getCap_eq; auto.
        unfold option_map1_compat_op.
        intros.
        (* probably a new theorem here *)
        unfold addCap.
        eapply option_map1_Equiv with
          (EqA := ObjEQ)
          (EqB := SysEQ); try apply getObj_eq; auto.
        unfold option_map1_compat_op.
        intros.
        (* probably a new theorem here *)
        unfold updateObj.
        eapply option_map1_Equiv with
          (EqA := PEQ)
          (EqB := SysEQ); simpl;  try apply getObjTuple_eq; auto.
        unfold option_map1_compat_op.
        intros.
        destruct H6.
        apply addObjTuple_eq; auto.
        unfold update_pair_object.
        repeat progress destruct a2; destruct a'2.
        repeat progress destruct H6.
        repeat progress destruct p0.
        repeat progress destruct p.
        simpl in *.
        unfold Sys.P.eq. simpl.
        repeat progress split; auto.
        apply OC.addCap_eq; auto.
      Qed.

    Theorem updateObj_eq: forall a a' o o' s s',
      Ref.eq a a' -> 
      Obj.eq o o' ->
      Sys.eq s s' ->
      Sys.eq (updateObj a o s)
      (updateObj a' o' s').
    Proof.
      intros.
      unfold updateObj.
      eapply option_map1_Equiv with
        (EqA := PEQ)
        (EqB := SysEQ); simpl in *;  try apply getObjTuple_eq; auto.
      unfold option_map1_compat_op; intros.
      destruct H2.
      apply addObjTuple_eq; auto.
      repeat progress destruct a0; destruct a'0.
      repeat progress destruct p0.
      repeat progress destruct p.
      repeat progress destruct H2.
      unfold Sys.P.eq; 
        simpl in *.
      repeat progress split; auto.
    Qed.



  Theorem copyCapList_eq: forall a a' t t' cil cil' s s',
    Ref.eq a a' ->
    Ref.eq t t' ->
    cil_eq cil cil' ->
    Sys.eq s s' ->
    Sys.eq (copyCapList a t cil s) (copyCapList a' t' cil' s').
  Proof.
    unfold copyCapList.
    unfold cil_eq.
    intros.
    induction H1; simpl; auto.
    apply copyCap_eq; red in H1; intuition.
  Qed.

  Theorem getCap_copyCapList_equal: forall s o o' t ixi_list i_src i_cap i_cap',
    getCap i_src o s = Some i_cap ->
    Ref.eq o o' ->
    ~ Ref.eq o t ->
    getCap i_src o (copyCapList o' t ixi_list s) = Some i_cap' ->
    Cap.eq i_cap i_cap'.
  Proof.
    intros s o o' t ixi_list i_src i_cap i_cap' Hi_cap HeqO HneqObj.
    
    (* induction *)
    
    induction ixi_list; intros Hi_cap'.
    (* base case *)
    simpl in *.
    rewrite Hi_cap in Hi_cap'.
    inversion Hi_cap'; auto.
    
    (* step case *)
    simpl in *.
    
    unfold copyCap in Hi_cap'.
    unfold getCap in Hi_cap'; unfold getCap in Hi_cap; unfold getCap in IHixi_list.
    unfold getObj in Hi_cap'; unfold getObj in Hi_cap; unfold getObj in IHixi_list.
    
    case (option_sumbool (getObjTuple o' (copyCapList o' t ixi_list s))); intros Hopt1;
      [| destruct Hopt1 as [o'_tuple Hopt1]]; rewrite Hopt1 in *; simpl in *; auto.
    
    destruct_tuple o'_tuple o'_obj o'_lbl o'_type o'_sched; simpl in *.
    
    case (option_sumbool (OC.getCap (fst a) o'_obj)); intros Hopt2;
      [| destruct Hopt2 as [copied_cap Hopt2]]; rewrite Hopt2 in *; simpl in *; auto.
    
    (* eliminate absurd case in Hi_cap' *)
    case (option_sumbool (getObjTuple o (addCap (snd a) copied_cap t (copyCapList o' t ixi_list s))));
      intros Hopt3; [| destruct Hopt3 as [o_tuple Hopt3]]; rewrite Hopt3 in *; simpl in *; auto; try discriminate.
    
    destruct_tuple o_tuple o_obj o_lbl o_type o_sched; simpl in *.
    
    (* eliminate absurd case in Hi_cap *)
    case (option_sumbool (getObjTuple o s));
      intros Hopt4; [| destruct Hopt4 as [o2_tuple Hopt4]]; rewrite Hopt4 in *; simpl in *; auto; try discriminate.
    destruct_tuple o2_tuple o2_obj o2_lbl o2_type o2_sched; simpl in *.
    
    (* reduce IHixi_list *)
    eapply Sys.MapS.find_2 in Hopt1.
    apply Sys.MapS.MapsTo_1 with (y:=o) in Hopt1; try (apply Ref.eq_sym; auto).
    apply Sys.MapS.find_1 in Hopt1.  
    unfold getObjTuple in IHixi_list.
    unfold Sys.P.t in Hopt1.
    rewrite Hopt1 in IHixi_list; simpl in *.
    
    (* prepare Hopt3 and IHixi_list for add_mapsto_iff *)
    unfold OC.getCap in IHixi_list.
    unfold addCap in Hopt3.
    unfold updateObj in Hopt3.
    unfold getObj in Hopt3.
    unfold getObjTuple in Hopt3.
    unfold addObjTuple in Hopt3.
    unfold OC.addCap in Hopt3.


    case (option_sumbool (Sys.MapS.find t (copyCapList o' t ixi_list s))); intros Hopt5;
      [|destruct Hopt5 as [t_tuple Hopt5]]; rewrite Hopt5 in *; simpl in *; auto; try discriminate.
      (* none *)
      (* o_obj = o'obj *)
    rewrite Hopt3 in Hopt1.
    inversion Hopt1.
    rewrite <- H0 in IHixi_list; auto.
      (* some *)
    destruct_tuple t_tuple t_obj t_lbl t_type t_sched; simpl in *.
      (* apply add_mapsto_iff in Hopt3 *)
    apply Sys.MapS.find_2 in Hopt3.
    apply Sys_Facts.add_mapsto_iff in Hopt3;
      destruct Hopt3 as [Hopt3 | Hopt3]; destruct Hopt3 as [Hopt3_eq Hopt3_map]. 
      (* t [=] o *)
    apply Ref.eq_sym in Hopt3_eq; generalize (HneqObj (Hopt3_eq)); contradiction.
      (* t [<>] o *)
    apply Sys.MapS.find_1 in Hopt3_map.
      (* o_obj = o'obj *)
    unfold Sys.P.t in *.
    rewrite Hopt3_map in Hopt1.
    inversion Hopt1.
    rewrite <- H0 in IHixi_list; auto.
  Qed.    

  Hint Resolve getCap_copyCapList_equal.

  (* was named copyCapList_eq in DirectAccessApproxImpl.v *)

    Theorem copyCapList_tuple_eq: forall s o o' t ixi_list tuple,
      Ref.eq o o' -> ~ Ref.eq o' t ->
      (Sys.MapS.find o (copyCapList o' t ixi_list s) = Some tuple <->
        Sys.MapS.find o s = Some tuple).
    Proof.
      intros.
      induction ixi_list; simpl; [intuition auto|].
      (* step *)
      unfold copyCap.
      unfold addCap.
      unfold updateObj.
      unfold getCap.
      unfold getObj.
      unfold addObjTuple.
      unfold getObjTuple.
      unfold OC.addCap.
      unfold OC.getCap.
      
      case (option_sumbool (Sys.MapS.find o' (copyCapList o' t ixi_list s))); intros Hopt1;
        [|destruct Hopt1 as [o'_tuple Hopt1]; destruct_tuple o'_tuple o'_obj o'_lbl o'_type o'_sched]; 
        rewrite Hopt1 in *; simpl in *; [intuition auto|].

      case (option_sumbool (Obj.MapS.find (fst a) o'_obj)); intros Hopt2;
        [|destruct Hopt2 as [cap Hopt2]]; rewrite Hopt2 in *; simpl in *; [intuition auto|].

      case (option_sumbool (Sys.MapS.find t (copyCapList o' t ixi_list s))); intros Hopt3;
        [|destruct Hopt3 as [t_tuple Hopt3]; destruct_tuple t_tuple t_obj t_lbl t_type t_sched]; 
        rewrite Hopt3 in *; simpl in *; [intuition auto|].

      split; intros; destruct IHixi_list as [IH IH'].
      apply Sys.MapS.find_2 in H1; apply Sys_Facts.add_mapsto_iff in H1; destruct H1 as [H1 | H1]; destruct H1 as [H1eq H1];
        [apply Ref.eq_sym in H1eq; apply Ref.eq_trans with (x:= o') in H1eq; auto; generalize (H0 H1eq); contradiction |
            apply IH; apply Sys.MapS.find_1; auto].
      apply Sys.MapS.find_1;eapply Sys_Facts.add_mapsto_iff;right; split;
        [intro H1eq; apply Ref.eq_sym in H1eq; apply Ref.eq_trans with (x:= o') in H1eq; auto|
          apply Sys.MapS.find_2; apply IH'; auto].
    Qed.

  Theorem getCap_copyCapList_none: forall s o o' t ixi_list i_src,
    Ref.eq o o' ->
    ~ Ref.eq o t ->
    (getCap i_src o s = None <->
      getCap i_src o (copyCapList o' t ixi_list s) = None).
  Proof.
    intros s o o' t ixi_list i_src HeqO HneqObj.

    assert (~ Ref.eq o' t) as HneqO';[intro Heq; apply HneqObj; eapply Ref.eq_trans; [apply HeqO| auto]|].

    induction ixi_list.
    (* base case *)
    split; auto.
    (* step case *)
    simpl in *.
    
    unfold copyCap.
    unfold getCap; unfold getCap in IHixi_list.
    unfold getObj; unfold getObj in IHixi_list.


    (* branch *)


    case (option_sumbool (getObjTuple o' (copyCapList o' t ixi_list s))); intros Hopt1;
      [| destruct Hopt1 as [o'_tuple Hopt1]; destruct_tuple o'_tuple o'_obj o'_lbl o'_type o'_sched];
      rewrite Hopt1 in *; simpl in *; auto;
    (* reduce IHixi_list *)
    unfold getObjTuple in Hopt1;
    rewrite Sys_Facts.find_o with (y:= o) in Hopt1; auto;
    unfold getObjTuple in *;
    rewrite Hopt1 in *; simpl in *.

    case (option_sumbool (OC.getCap (fst a) o'_obj)); intros Hopt6;
      [|destruct Hopt6 as [cap Hopt6]]; rewrite Hopt6 in *; simpl in *; auto;
        [unfold getObjTuple; rewrite Hopt1 in *; simpl; intuition auto|].

    (* reduce Hi_cap *)

    generalize (copyCapList_tuple_eq s _ _ _ ixi_list (o'_obj, o'_lbl, o'_type, o'_sched) HeqO HneqO'); intros H1.
    destruct H1 as [H1 H1']. generalize (H1 Hopt1); intros Hopt1'.
    unfold getObjTuple; rewrite Hopt1' in *; simpl in *.

    unfold addCap in *.
    unfold updateObj in *.
    unfold addObjTuple in *.
    unfold getObj in * .
    unfold getObjTuple in *.
    unfold OC.addCap in *.

    (* case on finding an obj at t *)

    case (option_sumbool (Sys.MapS.find t (copyCapList o' t ixi_list s))); intros Hopt3;
      [| destruct Hopt3 as [t_tuple Hopt3]; destruct_tuple t_tuple t_obj t_lbl t_type t_sched]; 
      rewrite Hopt3 in *; simpl in *; auto.
    (* case with no t *)
    rewrite Hopt1 in *; simpl; auto.
    (* case with t *)
    case (option_sumbool (Sys.MapS.find o (Sys.MapS.add t (Obj.MapS.add (snd a) cap t_obj, t_lbl, t_type, t_sched)
      (copyCapList o' t ixi_list s)))); intros Hopt2;
    [| destruct Hopt2 as [l_tuple Hopt2]; destruct_tuple l_tuple l_obj l_lbl l_type l_sched];
    unfold Sys.P.t in *; unfold Obj.t in *; rewrite Hopt2 in * ; simpl in *; auto;
    
    rewrite Sys_Facts.add_neq_o  in *; auto; rewrite Hopt2 in *; simpl in *; auto; try discriminate.

    (* case with l_obj *)
    inversion Hopt1. auto.  
  Qed.

  Hint Resolve getCap_copyCapList_none.

  Theorem getCap_copyCapList_map_eq: forall s o o' t ixi_list i_src opt_i_cap opt_i_cap',
    Ref.eq o o' ->
    ~ Ref.eq o t ->
    getCap i_src o s = opt_i_cap ->
    getCap i_src o (copyCapList o' t ixi_list s) = opt_i_cap' ->
    option_map_eq Cap.eq opt_i_cap opt_i_cap'.
  Proof.
    intros.
    destruct opt_i_cap as [i_cap |]; destruct opt_i_cap' as [i_cap' |]; simpl in *; auto.
    (* auto should be eauto, internal anomaly broken with changes to systemstate *)
    eapply getCap_copyCapList_equal; [apply H1 | apply H | apply H0 | apply H2].
    eapply getCap_copyCapList_none in H2; auto; rewrite H2 in H1; discriminate H1.
    eapply getCap_copyCapList_none in H1; [ rewrite H1 in H2; discriminate H2 |apply H | apply H0].
  Qed.


    (* the following is a simplification of the proof of getLabel_copyCapList_map_eq,
       However, we intend to change copyCapList to have a different indution method,
       so we are duplicating the proof so as not to loose it in future versions *)

    Theorem getLabel_copyCap_map_eq: forall s i o i' o' i_src opt_i_lbl opt_i_lbl',
    getLabel i_src s = opt_i_lbl ->
    getLabel i_src (copyCap i o i' o' s) = opt_i_lbl' ->
    option_map_eq ObjectLabel.eq opt_i_lbl opt_i_lbl'.
    Proof.
    intros s i o i' o' i_src opt_i_lbl opt_i_lbl' Hi_lbl Hi_lbl'.
    unfold copyCap in *; unfold getCap in *; unfold getObj in *.

    case (option_sumbool (getObjTuple o s)); intros Hopt1;
      [| destruct Hopt1 as [o'_tuple Hopt1]]; rewrite Hopt1 in *; simpl in *; auto;
        try solve [rewrite <- Hi_lbl; rewrite <- Hi_lbl'; eapply option_map_eq_refl; eauto].
    destruct_tuple o'_tuple o'_obj o'_lbl o'_type o'_sched; simpl in *.

    case (option_sumbool (OC.getCap i o'_obj)); intros Hopt2;
      [| destruct Hopt2 as [copied_cap Hopt2]]; rewrite Hopt2 in *; simpl in *; auto;
        try solve [rewrite <- Hi_lbl; rewrite <- Hi_lbl'; eapply option_map_eq_refl; eauto].

    unfold addCap in *; unfold getLabel in *;
    unfold getObj in *; unfold updateObj in *.

    case (option_sumbool (getObjTuple o' s)); intros Hopt3;
      [|destruct Hopt3 as [t_tuple Hopt3]; destruct_tuple t_tuple t_obj t_lbl t_type t_sched];
      rewrite Hopt3 in *; simpl in *;
        try solve [rewrite <- Hi_lbl; rewrite <- Hi_lbl'; eapply option_map_eq_refl; eauto].        

    unfold addObjTuple in *; unfold getObjTuple in *; unfold OC.addCap in *.
    
    case (Ref.eq_dec o' i_src ); intros Heq1.
    (* i_src [=] o' *)
    rewrite Sys_Facts.add_eq_o in Hi_lbl'; simpl in *; auto.
    unfold tupleGetLabel in *.
    rewrite Heq1 in *; rewrite Hopt3 in *; simpl in *;
      try solve [rewrite <- Hi_lbl; rewrite <- Hi_lbl'; eapply option_map_eq_refl; eauto].

    (* i_src [<>] o' *)
    rewrite Sys_Facts.add_neq_o in Hi_lbl'; simpl in *; auto;
      try solve [rewrite <- Hi_lbl; rewrite <- Hi_lbl'; eapply option_map_eq_refl; eauto].
    Qed.

    Theorem getLabel_copyCap_map_eq_equiv: forall s i o i' o' i_src s' opt_i_lbl opt_i_lbl',
      Sys.eq (copyCap i o i' o' s) s' ->
    getLabel i_src s = opt_i_lbl ->
    getLabel i_src s' = opt_i_lbl' ->
    option_map_eq ObjectLabel.eq opt_i_lbl opt_i_lbl'.
    Proof.
      intros.
      eapply option_map_eq_transitive; 
        [eauto
          |
          |rewrite <- H1; eapply getLabel_eq; [eapply Ref.eq_refl| eapply H]].
      
      rewrite <- H0.
      eapply getLabel_copyCap_map_eq; eapply eq_refl.
    Qed.
  
  Theorem getLabel_copyCapList_map_eq: forall s o t ixi_list i_src opt_i_lbl opt_i_lbl',
    getLabel i_src s = opt_i_lbl ->
    getLabel i_src (copyCapList o t ixi_list s) = opt_i_lbl' ->
    option_map_eq ObjectLabel.eq opt_i_lbl opt_i_lbl'.
  Proof.
    intros s o t ixi_list i_src opt_i_lbl opt_i_lbl' Hi_lbl.
    induction ixi_list; intros Hi_lbl';    simpl in *.
    (*base *)
    rewrite Hi_lbl in Hi_lbl'.
    rewrite Hi_lbl'.
    destruct opt_i_lbl; destruct opt_i_lbl'; try discriminate Hi_lbl';
      simpl in *; auto; apply ObjectLabel.eq_refl.
    (* step *)
    unfold copyCap in Hi_lbl'.
    unfold getCap in Hi_lbl'; unfold getCap in Hi_lbl; unfold getLabel in IHixi_list.
    unfold getObj in Hi_lbl'; unfold getObj in Hi_lbl; unfold getObj in IHixi_list.
  
    case (option_sumbool (getObjTuple o (copyCapList o t ixi_list s))); intros Hopt1;
      [| destruct Hopt1 as [o'_tuple Hopt1]]; rewrite Hopt1 in *; simpl in *; auto.
    destruct_tuple o'_tuple o'_obj o'_lbl o'_type o'_sched; simpl in *.

    case (option_sumbool (OC.getCap (fst a) o'_obj)); intros Hopt2;
      [| destruct Hopt2 as [copied_cap Hopt2]]; rewrite Hopt2 in *; simpl in *; auto.

    unfold addCap in Hi_lbl'.
    unfold getLabel in Hi_lbl'.
    unfold getObj in Hi_lbl'.
    unfold updateObj in *.
  
    case (option_sumbool (getObjTuple t (copyCapList o t ixi_list s))); intros Hopt3;
      [|destruct Hopt3 as [t_tuple Hopt3]; destruct_tuple t_tuple t_obj t_lbl t_type t_sched];
      rewrite Hopt3 in *; simpl in *.
    (* none case. apply IH *)
    apply IHixi_list; auto.
    (* some case *)
    unfold addObjTuple in Hi_lbl'.
    unfold getObjTuple in Hi_lbl'.
    unfold OC.addCap in Hi_lbl'.
    (* cases on i_src [=] t *)
    case (Ref.eq_dec t i_src ); intros Heq1.
    (* i_src [=] t*)
    rewrite Sys_Facts.add_eq_o in Hi_lbl'; simpl in *; auto.
    unfold getObjTuple in Hopt3; unfold getObjTuple in IHixi_list.
    rewrite Sys_Facts.find_o with (y:=t) in IHixi_list; auto.
    rewrite Hopt3 in IHixi_list. simpl in *.
    apply IHixi_list. auto.
    (* i_src [<>] t*)
    rewrite Sys_Facts.add_neq_o in Hi_lbl'; simpl in *; auto.
  Qed.


    Theorem getLabel_copyCapList_map_eq_equiv: forall s' s o t ixi_list i_src opt_i_lbl opt_i_lbl',
      Sys.eq (copyCapList o t ixi_list s) s' ->
    getLabel i_src s = opt_i_lbl ->
    getLabel i_src s' = opt_i_lbl' ->
    option_map_eq ObjectLabel.eq opt_i_lbl opt_i_lbl'.
    Proof.
      intros.
      eapply option_map_eq_transitive; 
        [eauto
          |
          |rewrite <- H1; eapply getLabel_eq; [eapply Ref.eq_refl| eapply H]].
      
      rewrite <- H0.
      eapply getLabel_copyCapList_map_eq; eapply eq_refl.
    Qed.

 
  Theorem is_label_iff_getLabel: forall r s l,
    is_label r s l <-> getLabel r s = Some l.
  Proof.
    intros.
    unfold is_label; unfold getLabel.
    case (option_sumbool (getObjTuple r s)); intros Hopt;
      [|destruct Hopt as [tuple Hopt]; destruct_tuple tuple obj lbl type sched];
      rewrite Hopt; simpl; split; intros; auto; 
        try discriminate; try contradiction; try rewrite H; try injection H; auto.
  Qed.


  Theorem getLabel_copyCapList_map_1: forall s o t ixi_list i_src opt_i_lbl opt_i_lbl',
    option_map_eq ObjectLabel.eq opt_i_lbl opt_i_lbl' ->
    getLabel i_src (copyCapList o t ixi_list s) = opt_i_lbl' ->
    getLabel i_src s = opt_i_lbl.
  Proof.
    intros.
    assert (exists opt_lbl, getLabel i_src s = opt_lbl) as Hl2;
      [unfold getLabel in *; unfold is_label in *;
        case (option_sumbool (getObjTuple i_src s)); intros Hopt9;
          [|destruct Hopt9 as [tuple9 Hopt9]; destruct_tuple tuple9 obj9 lbl9 type9 sched9];
          rewrite Hopt9 in *; simpl in *;
            eapply ex_intro; auto
        |destruct Hl2 as [opt_lbl Hl2]].

    generalize (getLabel_copyCapList_map_eq _ _ _ _ _ _ _ Hl2 H0); intros Heq.
    destruct opt_i_lbl as [i_lbl|]; destruct opt_lbl as[lbl|]; destruct opt_i_lbl' as [i_lbl'|];
      simpl in *; try discriminate; try contradiction; try assumption; auto.
    rewrite H; rewrite <- Heq; auto.
  Qed.

Theorem getObjTuple_rmCapsByTarget_some: forall a s obj lbl typ sch n,
  getObjTuple a s = Some (obj, lbl, typ, sch) ->
  exists obj', Obj.eq obj obj' /\
    getObjTuple a (rmCapsByTarget n s) = Some ((OC.rmCapsByTarget n obj'), lbl, typ, sch).
Proof.
  intros a s obj lbl typ sch n.
  unfold rmCapsByTarget in *.
  eapply Sys_Props.fold_rec_bis with 
    (P:= fun STATE STATE' =>
      getObjTuple a STATE = Some (obj, lbl, typ, sch) -> 
      exists obj', Obj.eq obj obj' /\ getObjTuple a STATE' = Some (OC.rmCapsByTarget n obj', lbl, typ, sch)).
  (* compat *)
  intros m m' a0 H; intros; unfold Sys.MapS.Equal in *; unfold getObjTuple in *.
  generalize (H a); intros H'; rewrite H' in *; auto.
  (* base *)
  intros H.
  unfold getObjTuple in *.
  generalize (Sys_Facts.empty_o Sys.P.t a); intros H'.
  unfold Sys.P.t in *.
  rewrite H' in H.
  discriminate H.
  (* induction *)
  intros.
  unfold getObjTuple in *.
  eapply Sys_Facts.find_mapsto_iff in H.
  unfold addObjTuple.
  (* cases, a [=|<>] k *)
  case ( Ref.eq_dec k a ); intros Hcase.
  (* k = a *)
  rewrite (Sys_Facts.add_eq_o m' e Hcase) in H2.
  injection H2; intros H2'; rewrite H2' in *; simpl in *.
  apply ex_intro with obj; intuition; apply Obj.eq_refl.
  (* k <> a *)
  rewrite (Sys_Facts.add_neq_o _ _ Hcase) in H2.
  apply H1 in H2.
    destruct H2 as [obj' H2]; destruct H2 as [H2 H3].
  destruct_tuple e e_obj e_lbl e_typ e_schd; simpl in *.
  rewrite (Sys_Facts.add_neq_o _ _ Hcase).
  apply ex_intro with obj'; intuition; apply Obj.eq_refl.
Qed.

Theorem getObjTuple_rmCapsByTarget_none: forall a s n,
  getObjTuple a s = None ->
  getObjTuple a (rmCapsByTarget n s) = None.
Proof.
  intros a s n.
  unfold rmCapsByTarget in *.
  eapply Sys_Props.fold_rec_bis with 
    (P:= fun STATE STATE' =>
      getObjTuple a STATE = None -> 
      getObjTuple a STATE' = None).
  (* compat *)
  intros m m' a0 H; intros; unfold Sys.MapS.Equal in *; unfold getObjTuple in *.
  generalize (H a); intros H'; rewrite H' in *; auto.
  (* base *)
  auto.
  (* induction *)
  intros k e s' m'; intros.
  unfold getObjTuple in *.
  eapply Sys_Facts.find_mapsto_iff in H.
  unfold addObjTuple.
  destruct_tuple e e_obj e_lbl e_typ e_schd; simpl in *.
  (* cases, a [=|<>] k *)
  case ( Ref.eq_dec k a ); intros Hcase; 
    [  rewrite (Sys_Facts.add_eq_o _ _ Hcase) in H2
|   rewrite (Sys_Facts.add_neq_o _ _ Hcase) in H2].
  (* k = a *)
  discriminate H2.
   (* k <> a *)
  rewrite (Sys_Facts.add_neq_o _ _ Hcase); auto.
Qed.

Theorem getCap_rmCapsByTarget_getCap: forall i o s cap n cap',
getCap i o s = Some cap -> getCap i o (rmCapsByTarget n s) = Some cap' -> Cap.eq cap cap'.
Proof.
  intros.
  unfold getCap in *.
  unfold getObj in *.
  unfold getObjTuple in *.
  destruct (rmCapsByTarget_spec_rmCapsByTarget n s) as [_ [_ [_ Htarget]]].
  case (option_sumbool (Sys.MapS.find o (rmCapsByTarget n s))); intros HfindObj; 
    [ | destruct HfindObj as [e HfindObj]]; rewrite HfindObj in *; simpl in *; [discriminate H0|].
  eapply Sys_Facts.find_mapsto_iff in HfindObj.
  unfold rmCapsByTarget_spec_not_target in *.
  destruct e as [[[ob l] t] d].
  generalize (Htarget o i cap' l t d); clear Htarget; intros Htarget.
  destruct Htarget as [Htarget _].
  unfold OC.getCap in H0. simpl in H0.
  eapply ObjFacts.find_mapsto_iff in H0.
  assert (exists o' : Obj.MapS.t Cap.t,
               exists l' : ObjectLabel.t,
                 exists t' : ObjectType.t,
                   exists d' : ObjectSchedule.t,
                     exists c' : Cap.t,
                       ObjectLabel.eq l l' /\
                       ObjectType.eq t t' /\
                       ObjectSchedule.eq d d' /\
                       Cap.eq cap' c' /\
                       Sys.MapS.MapsTo o (o', l', t', d')
                         (rmCapsByTarget n s) /\
                       Obj.MapS.MapsTo i c' o')as Hassert.
  do 5 (eapply ex_intro);
  repeat progress (split; simpl); try apply ObjectLabel.eq_refl; try apply ObjectType.eq_refl; try apply ObjectSchedule.eq_refl; 
    try apply Cap.eq_refl; try apply HfindObj; try  apply H0.
  apply Htarget in Hassert. clear Htarget.
  destruct Hassert as [o' [l' [t' [d' [c' [Hl [Ht [Hd [Hc [Hm [Hm2 Hnt]]]]]]]]]]].
  eapply ObjFacts.find_mapsto_iff in Hm2.
  eapply Sys_Facts.find_mapsto_iff in Hm.
  rewrite Hm in *; simpl in *.
  unfold OC.getCap in *.
  rewrite H in *.
  inversion Hm2 as [Hm2'].
  eapply Cap.eq_sym; auto.
Qed.
 
Theorem getCap_set_label_neq_o: forall i a l n s,
~ Ref.eq a n -> getCap i a (set_label n s l) = getCap i a s.
Proof.
intros.
unfold set_label.
unfold getCap.
unfold getObj.
unfold getObjTuple.
unfold addObjTuple.
case (option_sumbool (Sys.MapS.find n s)); intros Hcase; [|destruct Hcase as [[[[o' l'] t'] d'] Hcase]]; 
rewrite Hcase in *; simpl in *; auto.
rewrite Sys_Facts.add_neq_o; auto.
Qed.

Theorem getCap_updateObj_neq_o: forall i a n o s,
~ Ref.eq a n -> getCap i a (updateObj n o s) = getCap i a s.
Proof.
intros.
unfold updateObj.
unfold getCap.
unfold getObj.
unfold addObjTuple.
unfold getObjTuple.
case (option_sumbool (Sys.MapS.find n s)); intros Hcase; [|destruct Hcase as [[[[o' l'] t'] d'] Hcase]]; 
rewrite Hcase in *; simpl in *; auto.
rewrite Sys_Facts.add_neq_o; auto.
Qed.

(* this is a more reduced form of getLabel_copyCapList_map_eq and should probably be used w/in it *)
  Theorem getLabel_addCap_map_eq: forall r i c o s opt_i_lbl opt_i_lbl',
  getLabel r s = opt_i_lbl ->
  getLabel r (addCap i c o s) = opt_i_lbl' ->
  option_map_eq ObjectLabel.eq opt_i_lbl opt_i_lbl'.
Proof.
intros.
unfold getLabel in *.
unfold addCap in *.
unfold getObj in *.

case (option_sumbool (getObjTuple o s)); intros Hopt1;
[| destruct Hopt1 as [o'_tuple Hopt1]]; rewrite Hopt1 in *; simpl in *; auto.
(* None *)
rewrite H in H0.
rewrite H0.
destruct opt_i_lbl; destruct opt_i_lbl'; simpl; intuition (auto; try apply ObjectLabel.eq_refl).
(* Some *)
unfold updateObj in *; unfold getObjTuple in *; unfold addObjTuple in *. 
case (Ref.eq_dec r o ); intros Heq1.
(* eq *)
rewrite Hopt1 in *. simpl in *.
rewrite Sys_Facts.add_eq_o in H0; auto.
destruct o'_tuple as [[[ob' l'] t'] d']; simpl in *.
rewrite <- H0 in *.
rewrite Sys_Facts.find_o with (y:=r) in Hopt1; auto.
rewrite Hopt1 in*. simpl in *.
rewrite <- H.
 simpl. apply ObjectLabel.eq_refl.
(* <> *)
rewrite Hopt1 in *. simpl in *.
rewrite Sys_Facts.add_neq_o in H0; auto.
destruct o'_tuple as [[[ob' l'] t'] d']; simpl in *.
unfold Sys.P.t in *.
rewrite H in H0; rewrite H0; destruct opt_i_lbl; destruct opt_i_lbl'; simpl; intuition (auto; try apply ObjectLabel.eq_refl).
Qed.


  Theorem getLabel_addCap_map_1: forall r i c o s opt_i_lbl opt_i_lbl',
  option_map_eq ObjectLabel.eq opt_i_lbl opt_i_lbl' ->
  getLabel r (addCap i c o s) = opt_i_lbl' ->
  getLabel r s = opt_i_lbl.
Proof.
  intros.
  generalize (getLabel_addCap_map_eq _ _ _ _ _ _ _ (refl_equal (getLabel r s )) H0);
    intros Hlbl;
  case (option_sumbool (getLabel r s)); intros Hcase;
    [|destruct Hcase as [l Hcase]]; rewrite Hcase in *; simpl in *;
   destruct opt_i_lbl as [i_lbl|]; destruct opt_i_lbl' as [i_lbl'|];
      simpl in *; try discriminate; try contradiction; try assumption; auto.
   rewrite H. rewrite <- Hlbl. auto.
Qed.

Theorem getLabel_set_label_neq_o: forall a l n s,
~ Ref.eq a n -> getLabel a (set_label n s l) = getLabel a s.
Proof.
intros.
unfold set_label.
unfold getLabel.
unfold getObj.
unfold getObjTuple.
unfold addObjTuple.
case (option_sumbool (Sys.MapS.find n s)); intros Hcase; [|destruct Hcase as [[[[o' l'] t'] d'] Hcase]]; 
rewrite Hcase in *; simpl in *; auto.
rewrite Sys_Facts.add_neq_o; auto.
Qed.

Theorem getLabel_updateObj_o: forall a n o s,
getLabel a (updateObj n o s) = getLabel a s.
Proof.
intros.
unfold updateObj.
unfold getLabel.
unfold getObj.
unfold addObjTuple.
unfold getObjTuple.
case (option_sumbool (Sys.MapS.find n s)); intros Hcase; [|destruct Hcase as [[[[o' l'] t'] d'] Hcase]]; 
rewrite Hcase in *; simpl in *; auto.
case (Ref.eq_dec a n); intros Heq.
rewrite Sys_Facts.add_eq_o; auto.
rewrite Sys_Facts.find_o with (y:=a)in Hcase; auto.
rewrite Hcase. simpl; auto.

rewrite Sys_Facts.add_neq_o; auto.
Qed.

Theorem getLabel_rmCapsByTarget_o: forall a n s,
  getLabel a (rmCapsByTarget n s) = getLabel a s.
Proof.
  intros.
  generalize (rmCapsByTarget_spec_rmCapsByTarget n s); intros [Hin [Hmapsto _]].
  unfold rmCapsByTarget_spec_in in *.
unfold getLabel in *.
unfold getObjTuple in *.
  generalize (Hin a); clear Hin; intros Hin.
  case (option_sumbool (Sys.MapS.find a s)); intros Hcase;
 [|destruct Hcase as [[[[o l] t] d] Hcase]]; rewrite Hcase; simpl.

  eapply Sys_Facts.not_find_in_iff in Hcase.
  destruct Hin as [Hin _].
  assert (~ Sys.MapS.In a (rmCapsByTarget n s));[ intuition; eauto|].
  eapply Sys_Facts.not_find_in_iff in H.
  rewrite H; simpl; eauto.

  clear Hin.
  unfold rmCapsByTarget_spec_mapsto in *.
  generalize (Hmapsto a l t d); clear Hmapsto;  intros Hmapsto.
  eapply Sys_Facts.find_mapsto_iff in Hcase.

  assert (exists o' : Obj.MapS.t Cap.t,
               exists l' : ObjectLabels.ObjectLabel.t,
                 exists t' : ObjectTypes.ObjectType.t,
                   exists d' : ObjectSchedules.ObjectSchedule.t,
                     ObjectLabels.ObjectLabel.eq l l' /\
                     ObjectTypes.ObjectType.eq t t' /\
                     ObjectSchedules.ObjectSchedule.eq d d' /\
                     Sys.MapS.MapsTo a (o', l', t', d') s) as Hassert.
  do 4 (eapply ex_intro);
  repeat progress (split; try apply ObjectLabel.eq_refl; try apply ObjectType.eq_refl; try apply ObjectSchedule.eq_refl; try apply Hcase).

  eapply Hmapsto in Hassert; clear Hmapsto.
  destruct Hassert as [o' [l' [t' [d' [Hl [Ht [Hd Hm]]]]]]].
  eapply Sys_Facts.find_mapsto_iff in Hm.
  rewrite Hm; simpl.
  rewrite Hl; auto.
Qed.

        Theorem getLabel_set_label_eq_o_1: forall a l n s,
          Ref.eq a n -> 
          getLabel a (set_label n s l) = if (getObjTuple n s) then Some l else None.
        Proof.
          intros.
          rewrite H; clear H.
          unfold set_label.
          unfold getLabel.
          case (option_sumbool (getObjTuple n s)) as [Hcase| [[[[obj lbl] typ] sch] Hcase]];
            repeat progress (rewrite Hcase; simpl); eauto.
          unfold addObjTuple.
          unfold getObjTuple.
          rewrite Sys_Facts.add_eq_o; auto.
        Qed.
        Theorem getLabel_set_label_eq_o: forall a l n s,
          Ref.eq a n -> 
          getLabel a (set_label n s l) = if (getLabel n s) then Some l else None.
        Proof.
          intros.
          generalize (getLabel_set_label_eq_o_1 _ l _ s H).
          unfold getLabel.
          case (option_sumbool (getObjTuple n s)) as [Hcase | [[[[obj lbl] typ] sch] Hcase]];
            rewrite Hcase; simpl; intros; auto.
        Qed.

        Theorem is_label_set_label_neq_o: forall o o', ~ Ref.eq o o' ->
          forall s l l',
            is_label o (set_label o' s l) l' = is_label o s l'.
        Proof.
          intros.
          unfold is_label.
          unfold set_label.
          unfold getLabel.
          case (option_sumbool (getObjTuple o' s)) as [Hcase' | [[[[obj' lbl'] sch'] typ'] Hcase']]; 
            repeat progress (rewrite Hcase' in *; simpl in *); eauto;
              (case (option_sumbool (getObjTuple o s)) as [Hcase | [[[[obj lbl] sch] typ] Hcase]]; 
                repeat progress (rewrite Hcase in *; simpl in *); eauto);

              unfold getObjTuple in *;
                unfold addObjTuple in *;
                  try rewrite Sys_Facts.add_neq_o; simpl; auto; 
                    unfold Sys.P.t in *;rewrite Hcase; simpl; auto.
        Qed.

        Theorem is_label_set_label_eq_o: forall o o', Ref.eq o o' ->
          forall s l l',
            is_label o (set_label o' s l) l' = if (getLabel o' s) then ObjectLabel.eq l l' else False.
        Proof.
          intros.
          unfold is_label.
          unfold set_label.
          unfold getLabel.
          rewrite H.
          case (option_sumbool (getObjTuple o' s)) as [Hcase | [[[[obj lbl] sch] typ] Hcase]]; 
            repeat progress (rewrite Hcase in *; simpl in *); eauto.
          unfold getObjTuple.
          unfold addObjTuple.
          rewrite Sys_Facts.add_eq_o. simpl; auto. eapply eq_refl.
        Qed.

    Theorem rmObjTuple_eq: forall o o', Ref.eq o o' ->
      forall s s', Sys.eq s s' ->
      Sys.eq (rmObjTuple o s) (rmObjTuple o' s').
    Proof.
      intros; unfold rmObjTuple.
      eapply Sys_MapEquiv.remove_m; auto.
    Qed.

        (* From Attenuation.v: *)
        (* FIXME: go back and use this support theorm where you generalize SC.getCap_eq everywhere for legibility*)
        Theorem getCap_eq_Some: forall {i i' o o' s s' cap},
          Ind.eq i i' ->
          Ref.eq o o' ->
          Sys.eq s s' ->
          getCap i o s = Some cap ->
          exists cap', getCap i' o' s' = Some cap' /\ Cap.eq cap cap'.
        Proof.
          intros.
          generalize (getCap_eq _ _ _ _ _ _ H1 H H0); intros HEq.
          rewrite H2 in HEq.
          case (option_sumbool (getCap i' o' s')); intros Hcase; [|destruct Hcase as [cap' Hcase]];
          rewrite Hcase in HEq; simpl in *; try contradiction.
          eapply ex_intro.
          split; eauto.          
        Qed.

  Theorem exists_getCap_dec : forall s P,
    (forall o i cap, {P o i cap} + {~ P o i cap}) ->
    Proper (Ref.eq ==> Ind.eq ==> Cap.eq ==> impl) P ->
    {exists o, exists i, exists cap, getCap i o s = Some cap /\ P o i cap} + 
    {~ exists o,  exists i, exists cap, getCap i o s = Some cap /\ P o i cap}.
  Proof.
    (* This should be FMapExists.exists_ applied for OC and SC. *)
    intros s P Pdec HcompatP.
    edestruct (Sys_Exists.exists_ (fun o tuple => OC.Obj_Exists.Exists (P o) (tupleGetObj tuple)))
      with (m:=s)
        as [HsysEx|HsysEx].
    (* Sys decidability *)
    intros o tuple.
    destruct_tuple tuple obj lbl sch typ; simpl.
    edestruct (OC.Obj_Exists.exists_ (P o)) as [HobjEx|HobjEx];
      [eauto | left | right]; 
      solve [apply HobjEx; unfold OC.Obj_Exists.compat_P2; intros; eapply HcompatP; eauto; try apply Ref.eq_refl].
    (* Sys exists *)
    left.
    destruct HsysEx as [o HsysEx].
    (* compat *)
    unfold Sys_Exists.compat_P2. intros o o' t t' HrefEq HtupleEq Hex.
    destruct_tuple t obj src typ sch.
    destruct_tuple t' obj' src' typ' sch'.
    destruct_tuple HtupleEq HobjEq HsrcEq HtypEq HschEq.
    simpl in *.
    eapply Obj_MapEquiv.Proper_Exists;
      [eapply HcompatP; apply HrefEq
        | eapply HobjEq
        | auto].
    (* ex *)
    destruct HsysEx as [tuple [Hmap Hex]].
    destruct_tuple tuple obj lbl sch typ; simpl in *.
    eapply ex_intro with o.
    unfold getCap.
    unfold getObj.
    unfold getObjTuple.
    eapply Sys.MapS.find_1 in Hmap.
    rewrite Hmap; simpl.
    destruct Hex as [i [cap [Hmap' Hp']]].
    eapply Obj.MapS.find_1 in Hmap'.
    eauto.
    (* Sys ~ exists *)
    right.
    intro Hnot.
    destruct HsysEx.
    (* compat *)
    unfold Sys_Exists.compat_P2. intros o o' t t' HrefEq HtupleEq Hex.
    destruct_tuple t obj src typ sch.
    destruct_tuple t' obj' src' typ' sch'.
    destruct_tuple HtupleEq HobjEq HsrcEq HtypEq HschEq.
    simpl in *.
    eapply Obj_MapEquiv.Proper_Exists;
      [eapply HcompatP; apply HrefEq
        | eapply HobjEq
        | auto].
    (* ex *)
    destruct Hnot as [o [i [cap [Hcap Hp]]]].
    unfold Sys_Exists.Exists.

    idtac.
    generalize Hcap; intros Hcap'.
    eapply getCap_split in Hcap'.
    destruct Hcap' as [tuple [Htuple Hcap']].
    do 2 eapply ex_intro.
    split.
    eapply Sys.MapS.find_2; apply Htuple.
    do 2 eapply ex_intro.
    split.
    eapply Obj.MapS.find_2; apply Hcap'.
    auto.
  Qed.


End MakeSysStConv.


