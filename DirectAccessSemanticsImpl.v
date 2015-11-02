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
Require Import DirectAccessImpl.
(* type_remove *)
(*Require Import DirectAccessSemantics.*)
Require Import References.
Require Import Capabilities.
Require Import Indices.
Require Import Objects.
Require Import SystemState.
Require Import SemanticsDefinitions.
Require Import Semantics.
Require Import Semantics_ConvImpl.
Require Import AccessRightSets.
Require Import AccessGraphs.
Require Import AccessEdge.
Require Import RefSets.


Module MakeDirectAccessSemantics (Ref:ReferenceType) (RefS: RefSetType Ref) (Edges: AccessEdgeType Ref) (AccessGraph:AccessGraphType Ref Edges) (Seq:SeqAccType Ref RefS Edges AccessGraph) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) (SemDefns: SemanticsDefinitionsType Ref Cap Ind Obj Sys) (Sem: SemanticsType Ref RefS Cap Ind Obj Sys SemDefns).

  Module DA := MakeDirectAccess Ref RefS Edges AccessGraph Seq Cap Ind Obj Sys SemDefns Sem.

  Import DA.  
  Export DA.
  
    Ltac eapply_ag_add_cap_spec_rewrite := fun edge =>
      rewrite <- (Edges.edge_rewrite edge);
        eapply ag_add_cap_spec; [ eapply AG.eq_refl |];
          rewrite Edges.source_rewrite;
            rewrite Edges.target_rewrite;
              rewrite Edges.right_rewrite;
                rewrite (Edges.edge_rewrite edge).



    Ltac obj_label_alive := fun HexMap2 Hex2 HeqLbl => rewrite HexMap2; rewrite <- Hex2; rewrite HeqLbl; auto.


Theorem dirAcc_addCap_subset : forall ref index cap obj obj_lbl obj_type obj_sched s ag ag' ag2,
    Sys.MapS.MapsTo ref (obj, obj_lbl, obj_type, obj_sched) s ->
    dirAcc_spec s ag ->
    dirAcc_spec 
    (Sys.MapS.add ref
      (Obj.MapS.add index cap obj, obj_lbl, obj_type, obj_sched)
      s) ag2 ->
    AG.Subset ag ag' ->
    AG.Subset ag2 (ag_add_cap ref cap ag').
  Proof.
    intros.
    unfold AG.Subset; intros edge; intros.
    (* the cases here should be straightforward *)

    eapply_ag_add_cap_spec_rewrite edge.
    
    (* note the 3 decidable clauses in the conclusion *)
    (* if any of these are not true, then the only way edge is in ag' is if it is in ag. *)
    (* in the case where all 3 occur, the proof is concluded. *)
    
(*    case (A.ARSetProps.In_dec (Edges.right edge) (C.rights cap)); intros HinRight;
      [case (R.eq_dec (C.target cap) (Edges.target edge)); intros HeqTarget;
        [ case (R.eq_dec ref (Edges.source edge)); intros HeqSource; 
          [intuition (* case where all 3 occur *)|] |] |]; right. *)
    (* these should all come up during the existential instantiation *)
    (* case where ref [<>] (source edge) *)

    (* instantiate variables for solving by destructing dirAcc_spec ... ag' *)
    destruct (H1 edge) as [_ Hda]; apply Hda in H3; clear Hda.
    destruct_dirAcc H3 s'' HeqS src_ref src lbl type sched HmapS src' lbl' type' sched' 
    HeqP HeqL ind cap1 Hmap0 cap1_obj cap1_lbl cap1_type cap1_sched HmapScap
    cap1_obj' cap1_lbl' cap1_type' cap1_sched' HeqPcap HaliveCap rgt HinR HeqEdge.

    (* break apart HeqP and HeqPcap *)
    destruct_tuple HeqP HeqSrc HeqLbl HeqType HeqSched; simpl in HeqSrc; simpl in HeqLbl; simpl in HeqType; simpl in HeqSched.
    destruct_tuple HeqPcap HCap1 HCap2 HCap3 HCap4; simpl in HCap1; simpl in HCap2; simpl in HCap3; simpl in HCap4.

    destructEdgeEq HeqEdge edge HeqEdgeS HeqEdgeT HeqEdgeR.

    (* find an ex_obj ... that exists in the state from add. *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ (Sys.eq_sym HeqS)
      _ _ HmapS
      _ (Ref.eq_refl src_ref)) as [exP Hex];
    destruct_tuple exP ex_src ex_lbl ex_type ex_sched; simpl in Hex; destruct Hex as [Hex HexMap];
    destruct_tuple Hex Hex1 Hex2 Hex3 Hex4.

    (* find an ex_cap that exists in ex_obj *)
    destruct (Obj_MapEquiv.exists_mapsTo_eq
      _ _ (Obj.eq_trans (Obj.eq_sym HeqSrc) Hex1)
      _ _ Hmap0
      _ (Ind.eq_refl ind)) as [ex_cap1 HexCapMap];
    destruct HexCapMap as [HexCapEq HexCapMap].

    (* find an ex_cap_obj ... that exists in the state from add *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ (Sys.eq_sym HeqS)
      _ _ HmapScap
      _ (Ref.eq_refl (Cap.target cap1))) as [exPcap HCex];
    destruct_tuple exPcap ex_cap1_obj ex_cap1_lbl ex_cap1_type ex_cap1_sched; simpl in HCex; destruct HCex as [HCex HCexMap];
    destruct_tuple HCex HCex1 HCex2 HCex3 HCex4.

    (* at this point, all witness terms have a corresponding ex_ term existing in the add *)

    (* apply add_mapsto_iff in HexMap to find the cases for add *)
    (* generates 2 subgoals: (Ref.eq_dec rgt src_ref) *)
    apply Sys_Facts.add_mapsto_iff in HexMap;
      destruct HexMap as [HexMap | HexMap];
        destruct HexMap as [HexRef HexMap];
    (* Case 1: ref [=] src_ref case *)
    (* this line is case specific *)
    [ inversion HexMap as [[HexMap1 HexMap2 HexMap3 HexMap4]]; rewrite <- HexMap1 in HexCapMap |].


    (* apply add_mapsto_iff in HexCapMap to find the cases for add. *)
    (* generates 2 subgoals : (Ind.eq ind index) *)
    apply Obj_Facts.add_mapsto_iff in HexCapMap;
      destruct HexCapMap as [HexCapMap|HexCapMap];
        destruct HexCapMap as [HexCapRef HexCapMap]; [left|right].
 
    (* Case 1.1: index [=] ind *)
    (* at this point, the capability being added is the capability that produced the edge, so we have enough
       information to decide.  All other cases will be instantiating via the other dirAcc. *)

    (* We know that cap = ex_cap1 [=] cap1 -> In rgt (rights cap1) -> In rgt (rights cap), go left*)
    rewrite HexCapMap; split;
      [eauto 
        | split; 
          [apply Ref.eq_trans with (Cap.target cap1); auto ; apply Cap.target_eq; auto 
            | ]].

    (* Since coq 8.3, everywhere, hints for Ref.eq don't work *)
    
    eapply Ref.eq_trans;[| apply HeqEdgeS]; auto.

    (* In (right edge) (rights ex_cap1) *)

    eapply (ARSetFacts.In_eq_iff _ HeqEdgeR); apply Cap.rights_eq in HexCapEq;
      unfold ARSet.eq in HexCapEq; unfold ARSet.Equal in HexCapEq;eapply HexCapEq; auto.
    

    (* case 1.2: index [<>] ind *)
    (* ind is the index of the witness cap1.  index is the index we are inserting cap into *)
    (* this means that ex_cap1 [=] cap1 *)
    eapply H2.
    eapply H0.
    (* this will generate 2 subgoals: (Ref.eq_dec rgt (Cap.target cap1)) *)
    (* many of the subgoals will be identical and may want to be generalized here. *)
    apply Sys_Facts.add_mapsto_iff in HCexMap;
      destruct HCexMap as [HCexMap|HCexMap];
        destruct HCexMap as [HCexRef HCexMap];
          [ inversion HCexMap as [[HCexMap1 HCexMap2 HCexMap3 HCexMap4]] |].
    (* case 1.2.1: ref [=] target cap1 *)
    apply_ex_intro_dirAcc s s src_ref obj obj_lbl obj_type obj_sched obj obj_lbl obj_type obj_sched ind ex_cap1
    obj obj_lbl obj_type obj_sched obj obj_lbl obj_type obj_sched rgt;
    try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
      try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
        try apply ObjectLabels.ObjectLabel.eq_sym; auto.
    (* MapsTo src_ref (obj ...) s *)
    apply Sys.MapS.MapsTo_1 with ref; auto.
    (* obj_label = alive *)
    obj_label_alive HexMap2 Hex2 HeqLbl.
    (* MapsTo (Cap.target ex_cap1) (obj ... ) s *)
    apply Sys.MapS.MapsTo_1 with ref; auto; apply Ref.eq_trans with (Cap.target cap1); auto; apply Cap.target_eq; auto.
    (* obj_label = alive *)
    obj_label_alive HexMap2 Hex2 HeqLbl.
    (* In rgt (rights ex_cap1) *)
    apply Cap.rights_eq in HexCapEq; unfold ARSet.eq in HexCapEq; 
      unfold ARSet.Equal in HexCapEq;eapply HexCapEq; auto.
    (* (mkEdge src_ref (Cap.target ex_cap1) rgt) [=] edge *)
     rewrite <- (Edges.edge_rewrite edge);
       apply Edges.edge_equal; auto;
         apply Ref.eq_trans with (Cap.target cap1); auto; apply Cap.target_eq; auto.

     (* case 1.2.2: ref [<>] target cap1 *)
     (* here the object holding the edge producing cap is obj, but the witness object to the target is ex_cap1_obj *)
     apply_ex_intro_dirAcc s s src_ref obj obj_lbl obj_type obj_sched obj obj_lbl obj_type obj_sched ind ex_cap1
     ex_cap1_obj ex_cap1_lbl ex_cap1_type ex_cap1_sched ex_cap1_obj ex_cap1_lbl ex_cap1_type ex_cap1_sched rgt;
     try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
       try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
         try apply ObjectLabels.ObjectLabel.eq_sym; auto.
     (* MapsTo src_ref (obj ...) s *)
     apply Sys.MapS.MapsTo_1 with ref; auto.
     (* obj_label = alive *)
     obj_label_alive HexMap2 Hex2 HeqLbl.
     (* MapsTo (Cap.target ex_cap1) (ex_cap1_obj ... ) s *)
     apply Sys.MapS.MapsTo_1 with (Cap.target cap1); auto; apply Cap.target_eq; auto.
     (* ex_cap1_label = alive *)
     rewrite <- HCex2; rewrite HCap2; auto.
     (* In rgt (rights ex_cap1) *)
    apply Cap.rights_eq in HexCapEq; unfold ARSet.eq in HexCapEq; 
      unfold ARSet.Equal in HexCapEq;eapply HexCapEq; auto.
     (* (mkEdge src_ref (Cap.target ex_cap1) rgt) [=] edge *)
     rewrite <- (Edges.edge_rewrite edge);
       apply Edges.edge_equal; auto;
         apply Ref.eq_trans with (Cap.target cap1); auto; apply Cap.target_eq; auto.

     (* case 2: ref [<>] src_ref *)
     (* we have missed the object producing this edge entirely *)
     right. eapply H2. eapply H0.
     (* this will generate 2 subgoals: (Ref.eq_dec rgt (Cap.target cap1)) *)
     (* many of the subgoals will be identical and may want to be generalized here. *)
     apply Sys_Facts.add_mapsto_iff in HCexMap;
       destruct HCexMap as [HCexMap|HCexMap];
         destruct HCexMap as [HCexRef HCexMap];
           [ inversion HCexMap as [[HCexMap1 HCexMap2 HCexMap3 HCexMap4]] |].

     (* case 2.1: ref [=] target cap1 *)
     apply_ex_intro_dirAcc s s src_ref ex_src ex_lbl ex_type ex_sched ex_src ex_lbl ex_type ex_sched ind ex_cap1
     obj obj_lbl obj_type obj_sched obj obj_lbl obj_type obj_sched rgt;
     try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
       try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
         try apply ObjectLabels.ObjectLabel.eq_sym; auto.
     (* ex_label = alive *)
     intuition eauto.
     (* MapsTo ind (target ex_cap) (cap1_obj ...) s *)
     apply Sys.MapS.MapsTo_1 with ref; auto; rewrite HCexRef; apply Cap.target_eq; auto.
     (* obj_lbl is alive *)
     (* I would like to do away with the inversion command below *)
     inversion HCexMap; rewrite <- HCex2; rewrite HCap2; auto.
     (* in rgt (rights ex_cap1) *)
     apply Cap.rights_eq in HexCapEq; unfold ARSet.eq in HexCapEq; 
      unfold ARSet.Equal in HexCapEq;eapply HexCapEq; auto.
     (* (mkEdge src_ref (Cap.target ex_cap1) rgt) [=] edge *)
     rewrite <- (Edges.edge_rewrite edge);
       apply Edges.edge_equal; auto;
         apply Ref.eq_trans with (Cap.target cap1); auto; apply Cap.target_eq; auto.

     (* case 2.2: ref [<>] target cap1 *)
     apply_ex_intro_dirAcc s s src_ref ex_src ex_lbl ex_type ex_sched ex_src ex_lbl ex_type ex_sched ind ex_cap1
     ex_cap1_obj ex_cap1_lbl ex_cap1_type ex_cap1_sched ex_cap1_obj ex_cap1_lbl ex_cap1_type ex_cap1_sched rgt;
     try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
       try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
         try apply ObjectLabels.ObjectLabel.eq_sym; auto.
     (* ex_label = alive *)
     intuition eauto.
     (* MapsTo ind (target ex_cap) (cap1_obj ...) s *)
     apply Sys.MapS.MapsTo_1 with (Cap.target cap1); auto; apply Cap.target_eq; auto.
     (* ex_cap1_lbl is alive *)
     rewrite <- HCex2; rewrite HCap2; auto.
     (* in rgt (rights ex_cap1) *)
     apply Cap.rights_eq in HexCapEq; unfold ARSet.eq in HexCapEq; 
      unfold ARSet.Equal in HexCapEq;eapply HexCapEq; auto.
     (* (mkEdge src_ref (Cap.target ex_cap1) rgt) [=] edge *)
     rewrite <- (Edges.edge_rewrite edge);
       apply Edges.edge_equal; auto;
         apply Ref.eq_trans with (Cap.target cap1); auto; apply Cap.target_eq; auto.
   Qed.

Theorem dirAcc_addCap_notAlive_1 : forall ref index cap obj obj_lbl obj_type obj_sched s ag ag',
    Sys.MapS.MapsTo ref (obj, obj_lbl, obj_type, obj_sched) s ->
    dirAcc_spec s ag ->
    ~ SC.is_alive ref s ->
    dirAcc_spec 
    (Sys.MapS.add ref
      (Obj.MapS.add index cap obj, obj_lbl, obj_type, obj_sched)
      s) ag' ->
    AG.Subset ag' ag.
  Proof.
    (* technically this is equal, not subset, but I only need subset to finish the proofs *)
    intros.
    (* lay out is_alive in terms of ref *)
    unfold SC.is_alive in H1;
    unfold SC.is_label in H1;
      unfold SC.getLabel in H1;
    unfold SC.getObjTuple in H1;
    unfold option_map1 in H1;
    unfold Sys.P.t in H1;
    rewrite (Sys.MapS.find_1 H) in H1;
    unfold SC.tupleGetLabel in H1.
    (* this is true because if obj is not alive, any caps within it contribute no edges *)
    unfold AG.Subset; intros edge Hda.
    (* relate In edges *)
    eapply H0.
    eapply H2 in Hda.
    destruct_dirAcc Hda s'' HeqS src_ref src lbl type sched HmapS src' lbl' type' sched' 
    HeqP HeqL ind cap1 Hmap0 cap1_obj cap1_lbl cap1_type cap1_sched HmapScap
    cap1_obj' cap1_lbl' cap1_type' cap1_sched' HeqPcap HaliveCap rgt HinR HeqEdge;
    (* break apart HeqP and HeqPcap *)
    destruct_tuple HeqP HeqSrc HeqLbl HeqType HeqSched; simpl in HeqSrc; simpl in HeqLbl; simpl in HeqType; simpl in HeqSched;
    destruct_tuple HeqPcap HCap1 HCap2 HCap3 HCap4; simpl in HCap1; simpl in HCap2; simpl in HCap3; simpl in HCap4;
    (* break down the newly introduced edge *)
    destructEdgeEq HeqEdge edge HeqEdgeS HeqEdgeT HeqEdgeRef.
    
    (* these 3 copied from previous theorem , amy wish to Ltac *)

    (* find an ex_obj ... that exists in the state from add. *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ (Sys.eq_sym HeqS)
      _ _ HmapS
      _ (Ref.eq_refl src_ref)) as [exP Hex];
    destruct_tuple exP ex_src ex_lbl ex_type ex_sched; simpl in Hex; destruct Hex as [Hex HexMap];
      destruct_tuple Hex Hex1 Hex2 Hex3 Hex4;

    (* find an ex_cap that exists in ex_obj *)
    destruct (Obj_MapEquiv.exists_mapsTo_eq
      _ _ (Obj.eq_trans (Obj.eq_sym HeqSrc) Hex1)
      _ _ Hmap0
      _ (Ind.eq_refl ind)) as [ex_cap1 HexCapMap];
    destruct HexCapMap as [HexCapEq HexCapMap];

    (* find an ex_cap_obj ... that exists in the state from add *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ (Sys.eq_sym HeqS)
      _ _ HmapScap
      _ (Ref.eq_refl (Cap.target cap1))) as [exPcap HCex];
    destruct_tuple exPcap ex_cap1_obj ex_cap1_lbl ex_cap1_type ex_cap1_sched; simpl in HCex; destruct HCex as [HCex HCexMap];
    destruct_tuple HCex HCex1 HCex2 HCex3 HCex4.

    


    (* apply add_mapsto_iff in HexMap to find the cases for add *)
    (* generates 2 subgoals: (Ref.eq_dec rgt src_ref) *)
    apply Sys_Facts.add_mapsto_iff in HexMap;
      destruct HexMap as [HexMap | HexMap];
        destruct HexMap as [HexRef HexMap];
    (* Case 1: ref [=] src_ref case *)
    (* this line is case specific *)
          [ inversion HexMap as [[HexMap1 HexMap2 HexMap3 HexMap4]] |].
    (* contradiction on obj_lbl being alive and not alive *)
    rewrite HexMap2 in H1.
    rewrite <- Hex2 in H1.
    rewrite HeqLbl in H1.
    Require Import ObjectLabels.
    apply ObjectLabel.eq_sym in HeqL.
    contradiction.
    (* Case 2: ref [<>] src_ref *)
    (* start : copied from prev theorem *)
     (* we have missed the object producing this edge entirely *)
     (* this will generate 2 subgoals: (Ref.eq_dec rgt (Cap.target cap1)) *)
     (* many of the subgoals will be identical and may want to be generalized here. *)
     apply Sys_Facts.add_mapsto_iff in HCexMap;
       destruct HCexMap as [HCexMap|HCexMap];
         destruct HCexMap as [HCexRef HCexMap];
           [ inversion HCexMap as [[HCexMap1 HCexMap2 HCexMap3 HCexMap4]] |].

     (* case 2.1: ref [=] target cap1 *)
     apply_ex_intro_dirAcc s s src_ref ex_src ex_lbl ex_type ex_sched ex_src ex_lbl ex_type ex_sched ind ex_cap1
     obj obj_lbl obj_type obj_sched obj obj_lbl obj_type obj_sched rgt;
     try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
       try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
         try apply ObjectLabels.ObjectLabel.eq_sym; auto.
     (* ex_label = alive *)
     intuition eauto.
     (* MapsTo ind (target ex_cap) (cap1_obj ...) s *)
     apply Sys.MapS.MapsTo_1 with ref; auto; rewrite HCexRef; apply Cap.target_eq; auto.
     (* obj_lbl is alive *)
     (* I would like to do away with the inversion command below *)
     inversion HCexMap; rewrite <- HCex2; rewrite HCap2; auto.
     (* in rgt (rights ex_cap1) *)
     apply Cap.rights_eq in HexCapEq; unfold ARSet.eq in HexCapEq; 
      unfold ARSet.Equal in HexCapEq;eapply HexCapEq; auto.
     (* (mkEdge src_ref (Cap.target ex_cap1) rgt) [=] edge *)
     rewrite <- (Edges.edge_rewrite edge);
       apply Edges.edge_equal; auto;
         apply Ref.eq_trans with (Cap.target cap1); auto; apply Cap.target_eq; auto.

     (* case 2.2: ref [<>] target cap1 *)
     apply_ex_intro_dirAcc s s src_ref ex_src ex_lbl ex_type ex_sched ex_src ex_lbl ex_type ex_sched ind ex_cap1
     ex_cap1_obj ex_cap1_lbl ex_cap1_type ex_cap1_sched ex_cap1_obj ex_cap1_lbl ex_cap1_type ex_cap1_sched rgt;
     try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
       try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
         try apply ObjectLabels.ObjectLabel.eq_sym; auto.
     (* ex_label = alive *)
     intuition eauto.
     (* MapsTo ind (target ex_cap) (cap1_obj ...) s *)
     apply Sys.MapS.MapsTo_1 with (Cap.target cap1); auto; apply Cap.target_eq; auto.
     (* ex_cap1_lbl is alive *)
     rewrite <- HCex2; rewrite HCap2; auto.
     (* in rgt (rights ex_cap1) *)
     apply Cap.rights_eq in HexCapEq; unfold ARSet.eq in HexCapEq; 
      unfold ARSet.Equal in HexCapEq;eapply HexCapEq; auto.
     (* (mkEdge src_ref (Cap.target ex_cap1) rgt) [=] edge *)
     rewrite <- (Edges.edge_rewrite edge);
       apply Edges.edge_equal; auto;
         apply Ref.eq_trans with (Cap.target cap1); auto; apply Cap.target_eq; auto.
     (* end copied from prev theorem *)  (*worked like a charm, probably should ltac. *)

  
  Qed.



  Theorem dirAcc_addCap_notAlive_2 : forall ref index cap obj obj_lbl obj_type obj_sched s ag ag',
    Sys.MapS.MapsTo ref (obj, obj_lbl, obj_type, obj_sched) s ->
    dirAcc_spec s ag ->
    ~ SC.is_alive (Cap.target cap) s ->
    dirAcc_spec 
    (Sys.MapS.add ref
      (Obj.MapS.add index cap obj, obj_lbl, obj_type, obj_sched)
      s) ag' ->
    AG.Subset ag' ag.
  Proof.
    intros.
    (* this is true because cap can not introduce any edge *)
    unfold AG.Subset; intros edge Hda.
    (* relate In edges *)
    eapply H0.
    eapply H2 in Hda.
    destruct_dirAcc Hda s'' HeqS src_ref src lbl type sched HmapS src' lbl' type' sched' 
    HeqP HeqL ind cap1 Hmap0 cap1_obj cap1_lbl cap1_type cap1_sched HmapScap
    cap1_obj' cap1_lbl' cap1_type' cap1_sched' HeqPcap HaliveCap rgt HinR HeqEdge;
    (* break apart HeqP and HeqPcap *)
    destruct_tuple HeqP HeqSrc HeqLbl HeqType HeqSched; simpl in HeqSrc; simpl in HeqLbl; simpl in HeqType; simpl in HeqSched;
    destruct_tuple HeqPcap HCap1 HCap2 HCap3 HCap4; simpl in HCap1; simpl in HCap2; simpl in HCap3; simpl in HCap4;
    (* break down the newly introduced edge *)
    destructEdgeEq HeqEdge edge HeqEdgeS HeqEdgeT HeqEdgeRef.
    
    (* these 3 copied from previous theorem , amy wish to Ltac *)

    (* find an ex_obj ... that exists in the state from add. *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ (Sys.eq_sym HeqS)
      _ _ HmapS
      _ (Ref.eq_refl src_ref)) as [exP Hex];
    destruct_tuple exP ex_src ex_lbl ex_type ex_sched; simpl in Hex; destruct Hex as [Hex HexMap];
      destruct_tuple Hex Hex1 Hex2 Hex3 Hex4;

    (* find an ex_cap that exists in ex_obj *)
    destruct (Obj_MapEquiv.exists_mapsTo_eq
      _ _ (Obj.eq_trans (Obj.eq_sym HeqSrc) Hex1)
      _ _ Hmap0
      _ (Ind.eq_refl ind)) as [ex_cap1 HexCapMap];
    destruct HexCapMap as [HexCapEq HexCapMap];

    (* find an ex_cap_obj ... that exists in the state from add *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ (Sys.eq_sym HeqS)
      _ _ HmapScap
      _ (Ref.eq_refl (Cap.target cap1))) as [exPcap HCex];
    destruct_tuple exPcap ex_cap1_obj ex_cap1_lbl ex_cap1_type ex_cap1_sched; simpl in HCex; destruct HCex as [HCex HCexMap];
    destruct_tuple HCex HCex1 HCex2 HCex3 HCex4.

    (* apply add_mapsto_iff in HexMap to find the cases for add *)
    (* generates 2 subgoals: (Ref.eq_dec rgt src_ref) *)
    apply Sys_Facts.add_mapsto_iff in HexMap;
      destruct HexMap as [HexMap | HexMap];
        destruct HexMap as [HexRef HexMap];
    (* Case 1: ref [=] src_ref case *)
    (* this line is case specific *)
          [ inversion HexMap as [[HexMap1 HexMap2 HexMap3 HexMap4]] |].
    (* apply add_mapsto_iff in HexCapMap to find the cases for add. *)
    (* generates 2 subgoals : (Ind.eq ind index) *)
    rewrite <- HexMap1 in HexCapMap.
    apply Obj_Facts.add_mapsto_iff in HexCapMap;
      destruct HexCapMap as [HexCapMap|HexCapMap];
        destruct HexCapMap as [HexCapRef HexCapMap].
    (* Case 1.1: index [=] ind *)
    (* at this point, the capability being added is the capability that produced the edge.
       There is a contradiction here, since ex_cap must target a live object, but also must not. *)
    (* unfortunately, we need to know if the target was updated to perform the analysis. *)
    (* lay out is_alive in terms of (target cap) *)
     unfold SC.is_alive in H1;
       unfold SC.is_label in H1;
         unfold SC.getLabel in H1;
         unfold SC.getObjTuple in H1;
           unfold option_map1 in H1;
             unfold Sys.P.t in H1;
               unfold SC.tupleGetLabel in H1.

     (* this will generate 2 subgoals: (Ref.eq_dec rgt (Cap.target cap1)) *)
     apply Sys_Facts.add_mapsto_iff in HCexMap;
       destruct HCexMap as [HCexMap|HCexMap];
         destruct HCexMap as [HCexRef HCexMap];
           [ inversion HCexMap as [[HCexMap1 HCexMap2 HCexMap3 HCexMap4]] |].
     (* case 1.1.1: ref [=] target cap1 *)
     rewrite HexCapMap in H1.
     generalize (Cap.target_eq _ _ HexCapEq); intros HexCapEqTarget.
     eapply Ref.eq_trans in HexCapEqTarget; [ |apply HCexRef].
     rewrite (Sys.MapS.find_1 (Sys.MapS.MapsTo_1 HexCapEqTarget H)) in H1.
     (* show obj_lbl contradicts in H1*)
     rewrite HexMap2 in H1.
     rewrite <- Hex2 in H1.
     rewrite HeqLbl in H1.
     apply ObjectLabel.eq_sym in HeqL.
     contradiction.

     (* case 1.1.2 ref [<>] target cap1 *)
     (* here we should then show that it falls through. *)
     rewrite HexCapMap in H1.
     generalize (Cap.target_eq _ _ HexCapEq); intros HexCapEqTarget.
     rewrite (Sys.MapS.find_1 (Sys.MapS.MapsTo_1 HexCapEqTarget HCexMap)) in H1.
     (* show obj_lbl contradicts in H1 *)
     rewrite <- HCex2 in H1.
     rewrite HCap2 in H1.
     apply ObjectLabel.eq_sym in HaliveCap.
     contradiction.

     (* case 1.2: index [<>] ind *)
     (* case 1.2 is copied from previous theorem *)
     (* ind is the index of the witness cap1.  index is the index we are inserting cap into *)
     (* this means that ex_cap1 [=] cap1 *)
     (* this will generate 2 subgoals: (Ref.eq_dec rgt (Cap.target cap1)) *)
     (* many of the subgoals will be identical and may want to be generalized here. *)
     apply Sys_Facts.add_mapsto_iff in HCexMap;
       destruct HCexMap as [HCexMap|HCexMap];
        destruct HCexMap as [HCexRef HCexMap];
          [ inversion HCexMap as [[HCexMap1 HCexMap2 HCexMap3 HCexMap4]] |].
    (* case 1.2.1: ref [=] target cap1 *)
    apply_ex_intro_dirAcc s s src_ref obj obj_lbl obj_type obj_sched obj obj_lbl obj_type obj_sched ind ex_cap1
    obj obj_lbl obj_type obj_sched obj obj_lbl obj_type obj_sched rgt;
    try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
      try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
        try apply ObjectLabels.ObjectLabel.eq_sym; auto.
    (* MapsTo src_ref (obj ...) s *)
    apply Sys.MapS.MapsTo_1 with ref; auto.
    (* obj_label = alive *)
    obj_label_alive HexMap2 Hex2 HeqLbl.
    (* MapsTo (Cap.target ex_cap1) (obj ... ) s *)
    apply Sys.MapS.MapsTo_1 with ref; auto; apply Ref.eq_trans with (Cap.target cap1); auto; apply Cap.target_eq; auto.
    (* obj_label = alive *)
    obj_label_alive HexMap2 Hex2 HeqLbl.
    (* In rgt (rights ex_cap1) *)
    apply Cap.rights_eq in HexCapEq; unfold ARSet.eq in HexCapEq; 
      unfold ARSet.Equal in HexCapEq;eapply HexCapEq; auto.
    (* (mkEdge src_ref (Cap.target ex_cap1) rgt) [=] edge *)
     rewrite <- (Edges.edge_rewrite edge);
       apply Edges.edge_equal; auto;
         apply Ref.eq_trans with (Cap.target cap1); auto; apply Cap.target_eq; auto.

     (* case 1.2.2: ref [<>] target cap1 *)
     (* here the object holding the edge producing cap is obj, but the witness object to the target is ex_cap1_obj *)
     apply_ex_intro_dirAcc s s src_ref obj obj_lbl obj_type obj_sched obj obj_lbl obj_type obj_sched ind ex_cap1
     ex_cap1_obj ex_cap1_lbl ex_cap1_type ex_cap1_sched ex_cap1_obj ex_cap1_lbl ex_cap1_type ex_cap1_sched rgt;
     try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
       try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
         try apply ObjectLabels.ObjectLabel.eq_sym; auto.
     (* MapsTo src_ref (obj ...) s *)
     apply Sys.MapS.MapsTo_1 with ref; auto.
     (* obj_label = alive *)
     obj_label_alive HexMap2 Hex2 HeqLbl.
     (* MapsTo (Cap.target ex_cap1) (ex_cap1_obj ... ) s *)
     apply Sys.MapS.MapsTo_1 with (Cap.target cap1); auto; apply Cap.target_eq; auto.
     (* ex_cap1_label = alive *)
     rewrite <- HCex2; rewrite HCap2; auto.
     (* In rgt (rights ex_cap1) *)
    apply Cap.rights_eq in HexCapEq; unfold ARSet.eq in HexCapEq; 
      unfold ARSet.Equal in HexCapEq;eapply HexCapEq; auto.
     (* (mkEdge src_ref (Cap.target ex_cap1) rgt) [=] edge *)
     rewrite <- (Edges.edge_rewrite edge);
       apply Edges.edge_equal; auto;
         apply Ref.eq_trans with (Cap.target cap1); auto; apply Cap.target_eq; auto.

   (* Case 2: ref [<>] src_ref *)
    (* start : copied from prev theorem *)
     (* we have missed the object producing this edge entirely *)
     (* this will generate 2 subgoals: (Ref.eq_dec rgt (Cap.target cap1)) *)
     (* many of the subgoals will be identical and may want to be generalized here. *)
     apply Sys_Facts.add_mapsto_iff in HCexMap;
       destruct HCexMap as [HCexMap|HCexMap];
         destruct HCexMap as [HCexRef HCexMap];
           [ inversion HCexMap as [[HCexMap1 HCexMap2 HCexMap3 HCexMap4]] |].

     (* case 2.1: ref [=] target cap1 *)
     apply_ex_intro_dirAcc s s src_ref ex_src ex_lbl ex_type ex_sched ex_src ex_lbl ex_type ex_sched ind ex_cap1
     obj obj_lbl obj_type obj_sched obj obj_lbl obj_type obj_sched rgt;
     try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
       try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
         try apply ObjectLabels.ObjectLabel.eq_sym; auto.
     (* ex_label = alive *)
     intuition eauto.
     (* MapsTo ind (target ex_cap) (cap1_obj ...) s *)
     apply Sys.MapS.MapsTo_1 with ref; auto; rewrite HCexRef; apply Cap.target_eq; auto.
     (* obj_lbl is alive *)
     (* I would like to do away with the inversion command below *)
     inversion HCexMap; rewrite <- HCex2; rewrite HCap2; auto.
     (* in rgt (rights ex_cap1) *)
     apply Cap.rights_eq in HexCapEq; unfold ARSet.eq in HexCapEq; 
      unfold ARSet.Equal in HexCapEq;eapply HexCapEq; auto.
     (* (mkEdge src_ref (Cap.target ex_cap1) rgt) [=] edge *)
     rewrite <- (Edges.edge_rewrite edge);
       apply Edges.edge_equal; auto;
         apply Ref.eq_trans with (Cap.target cap1); auto; apply Cap.target_eq; auto.

     (* case 2.2: ref [<>] target cap1 *)
     apply_ex_intro_dirAcc s s src_ref ex_src ex_lbl ex_type ex_sched ex_src ex_lbl ex_type ex_sched ind ex_cap1
     ex_cap1_obj ex_cap1_lbl ex_cap1_type ex_cap1_sched ex_cap1_obj ex_cap1_lbl ex_cap1_type ex_cap1_sched rgt;
     try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
       try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
         try apply ObjectLabels.ObjectLabel.eq_sym; auto.
     (* ex_label = alive *)
     intuition eauto.
     (* MapsTo ind (target ex_cap) (cap1_obj ...) s *)
     apply Sys.MapS.MapsTo_1 with (Cap.target cap1); auto; apply Cap.target_eq; auto.
     (* ex_cap1_lbl is alive *)
     rewrite <- HCex2; rewrite HCap2; auto.
     (* in rgt (rights ex_cap1) *)
     apply Cap.rights_eq in HexCapEq; unfold ARSet.eq in HexCapEq; 
      unfold ARSet.Equal in HexCapEq;eapply HexCapEq; auto.
     (* (mkEdge src_ref (Cap.target ex_cap1) rgt) [=] edge *)
     rewrite <- (Edges.edge_rewrite edge);
       apply Edges.edge_equal; auto;
         apply Ref.eq_trans with (Cap.target cap1); auto; apply Cap.target_eq; auto.
     (* end copied from prev theorem *)  (*worked like a charm, probably should ltac. *)
  Qed.












  Theorem dirAcc_read: forall s ag,
    dirAcc_spec s ag ->
    forall a c, dirAcc_spec (Sem.do_read a c s) ag.
  Proof.
  (* try to figure out how to automate this *)
    intros; unfold dirAcc_spec in *; intros.
    generalize (Sem.read_spec a c s); intros Heq.
    destruct H with edge as [H_1 H_2]; clear H.
    split; intros.
   (* case 1 *)
    apply H_1; intros.
    destruct_dirAcc H s' HeqS src_ref src lbl srcType srcSched HmapS 
    src' lbl' srcType' srcSched' HeqP Halive ind cap HmapSrc'
    cap_obj cap_lbl cap_type cap_sched HmapScap cap_obj' cap_lbl' cap_type' cap_sched'
    HeqPcap HaliveCap rgt HinR HeqEdge.
    apply_ex_intro_dirAcc s' (Sem.do_read a c s) src_ref src lbl srcType srcSched src' lbl' srcType' srcSched'
    ind cap cap_obj cap_lbl cap_type cap_sched cap_obj' cap_lbl' cap_type' cap_sched' rgt.
   (* case 2 *)
    eapply H_2 in H.
    destruct_dirAcc H s' HeqS src_ref src lbl srcType srcSched HmapS 
    src' lbl' srcType' srcSched' HeqP Halive ind cap HmapSrc'
    cap_obj cap_lbl cap_type cap_sched HmapScap cap_obj' cap_lbl' cap_type' cap_sched'
    HeqPcap HaliveCap rgt HinR HeqEdge.
    apply_ex_intro_dirAcc s' s src_ref src lbl srcType srcSched src' lbl' srcType' srcSched'
    ind cap cap_obj cap_lbl cap_type cap_sched cap_obj' cap_lbl' cap_type' cap_sched' rgt.
  Qed.

  Theorem dirAcc_write: forall s ag,
    dirAcc_spec s ag ->
    forall a c, dirAcc_spec (Sem.do_write a c s) ag.
  Proof.
    intros; unfold dirAcc_spec in *; intros.
    generalize (Sem.write_spec a c s); intros Heq.
    destruct H with edge as [H_1 H_2]; clear H.
    split; intros.
   (* case 1 *)
    apply H_1; intros.
    destruct_dirAcc H s' HeqS src_ref src lbl srcType srcSched HmapS 
    src' lbl' srcType' srcSched' HeqP Halive ind cap HmapSrc'
    cap_obj cap_lbl cap_type cap_sched HmapScap cap_obj' cap_lbl' cap_type' cap_sched'
    HeqPcap HaliveCap rgt HinR HeqEdge.
    apply_ex_intro_dirAcc s' (Sem.do_write a c s) src_ref src lbl srcType srcSched src' lbl' srcType' srcSched'
    ind cap cap_obj cap_lbl cap_type cap_sched cap_obj' cap_lbl' cap_type' cap_sched' rgt.
   (* case 2 *)
    eapply H_2 in H.
    destruct_dirAcc H s' HeqS src_ref src lbl srcType srcSched HmapS 
    src' lbl' srcType' srcSched' HeqP Halive ind cap HmapSrc'
    cap_obj cap_lbl cap_type cap_sched HmapScap cap_obj' cap_lbl' cap_type' cap_sched'
    HeqPcap HaliveCap rgt HinR HeqEdge.
    apply_ex_intro_dirAcc s' s src_ref src lbl srcType srcSched src' lbl' srcType' srcSched'
    ind cap cap_obj cap_lbl cap_type cap_sched cap_obj' cap_lbl' cap_type' cap_sched' rgt.
  Qed.

  (* there is probably a better way to prove this, or at least some
     additional ltac we could define to remove some of the 
     duplicated proof script *)
  Theorem dirAcc_revoke: forall s ag,
    dirAcc_spec s ag ->
    forall a t c ag', dirAcc_spec (Sem.do_revoke a t c s) ag' ->
      AG.Subset ag' ag.
  Proof.
    intros.
    unfold dirAcc_spec in *; unfold AG.Subset in *; intros x Hsub.
    case (SemDefns.revoke_preReq_dec a t s); intros Hpre; 
      [generalize (Sem.revoke_valid _ _ c _ Hpre)
        | generalize (Sem.revoke_invalid _ _ c _ Hpre)]; intros Heq;
      [|apply dirAcc_spec_eq_1 with (s:=Sem.do_revoke a t c s) (s':=s) (ag:=ag'); auto].
    (* case where revoke happens *)
    unfold SemDefns.revoke_preReq in Hpre; destruct Hpre as [Hpre HhasWrite];
      unfold_preReq Hpre Halive HtargetAlive HisActive.
    (* unfold Sem.preReq in Hpre; destruct Hpre as [Halive HtargetAlive];
      destruct HtargetAlive as [HtargetActive HtargetAlive];
        unfold Sem.target_is_alive in Halive; unfold Sem.SC.is_alive in Halive;
        unfold Sem.SC.is_label in Halive; red in Halive. *)
    unfold SC.getLabel in *.
    case (option_sumbool (SC.getObjTuple a s)); intros Hopt2;[|destruct Hopt2 as [tuple Hopt2]];
      rewrite Hopt2 in Halive; [contradiction| destruct_tuple tuple actor actor_lbl actor_type actor_sched; simpl in Halive].
    case (option_sumbool (SC.getCap t a s)); intros Hopt; 
      [|destruct Hopt as [cap Hopt]]; rewrite Hopt in Heq; simpl in Heq.
    (* case where revoke doesn't happen because cap is gone *) 
    (* reduced to do_revoke [=] s *)
    apply dirAcc_spec_eq_1 with (s:=Sem.do_revoke a t c s) (s':=s) (ag:=ag'); auto.
    (* case where cap exists and revoke occurrs *)
    unfold SemDefns.target_is_alive in HtargetAlive.
    rewrite Hopt in HtargetAlive. simpl in HtargetAlive.
    unfold SC.is_alive in HtargetAlive.
    unfold SC.is_label in HtargetAlive.
    unfold SC.getLabel in HtargetAlive.
    unfold option_map1 in HtargetAlive.
    unfold SC.rmCap in Heq.
    unfold SC.getObj in Heq.
    case (option_sumbool (SC.getObjTuple (Cap.target cap) s)); intros Hopt1;
      [|destruct Hopt1 as [obj_tuple Hopt1]]; rewrite Hopt1 in Heq; simpl in Heq.
    (* case where no object exists *)
    (* reduced to do_revoke [=] s *)
    apply dirAcc_spec_eq_1 with (s:=Sem.do_revoke a t c s) (s':=s) (ag:=ag'); auto.
    (* case where an object exists *)
    destruct_tuple obj_tuple src lbl src_type src_sched.
    rewrite Hopt1 in HtargetAlive; simpl in HtargetAlive.
    unfold SC.updateObj in Heq; unfold SC.addObjTuple in Heq; 
      unfold OC.rmCap in Heq; rewrite Hopt1 in Heq.
    simpl in Heq.
    generalize (H x); clear H; intros H.
    generalize (H0 x); clear H0; intros H0.
    destruct H0 as [_ H0].
    generalize (H0 Hsub); clear H0; intros H0.
    destruct_dirAcc H0 s1' HeqS src_ref1 src1 lbl1 type1 sched1 HmapS src1' 
    lbl1' type1' sched1' HeqP HeqL ind1 cap1 Hmap0 cap_obj cap_lbl cap_type cap_sched HmapScap
    cap_obj' cap_lbl' cap_type' cap_sched' HeqPcap HaliveCap rgt1 HinR HeqEdge.    
    (* we should now know enough to apply H. *)
    (* the case analysis is as follows *)
    (* when (target cap) [<>] src_refl1, we can determine (MapsTo src_ref1 (src1, lbl1, type1, sched1) s),
       since do_revoke did not modify src1 under src_refl1, and use H to show (In x ag) *)
    (* when (target cap) [=] src_refl1 /\  c [<>] ind1,  we can determine 
       (MapsTo ind1 cap1 src1'), and use H to show (In x ag) *)
    (* when (target cap) [=] src_refl1 /\ c [=] ind1, there is one remaining case:
       Either there is some other cap that could contribute edge from s, for which we use it; 
       or this is not, and we have a contradiction with H *)
    case (Ref.eq_dec (Cap.target cap) src_ref1); intros HeqA.
    (* case where Cap.target cap [=] src_ref1 *)
    generalize Hopt1; intros Hopt1'.
    unfold SC.getObjTuple in Hopt1';
      apply Sys.MapS.find_2 in Hopt1';
        apply Sys.MapS.MapsTo_1 with (y:=src_ref1) in Hopt1'; auto.
    case (Ind.eq_dec c ind1); intros HeqCap.
    (* case where c [=] ind1 *)
    (* we will want to know this in both cases below, assert it now *)
    assert (Obj_Exists.compat_P2 
      (fun _ cap' => 
        Ref.eq (Cap.target cap') (Cap.target cap1) /\
        ARSet.In rgt1 (Cap.rights cap') )) as Hcompat.
    unfold Obj_Exists.compat_P2; intros; destruct H2; split; 
      [ apply Ref.eq_trans with (Cap.target b); auto; 
        apply Cap.target_eq; apply Cap.eq_sym; assumption
        | eapply (Cap.rights_eq _ _  H1); auto]. 
    (* this will generate 3 subgoals.
       First, that the function is decidable.
       The remaining two cases are exists and ~exists. *)
    case (Obj_Exists.exists_ 
      (fun _ cap' => 
        Ref.eq (Cap.target cap') (Cap.target cap1) /\
        ARSet.In rgt1 (Cap.rights cap') ))
      with (m:=Obj.MapS.remove c src); intros Hexists.
    (* decidability *)
    intros; apply Sumbool_dec_and;[ apply Ref.eq_dec | apply ARSetProps.In_dec].
    (* exists case *)
    apply Hexists in Hcompat; clear Hexists; rename Hcompat into Hexists.
    unfold Obj_Exists.Exists in Hexists.
    destruct Hexists as [k Hexists]; destruct Hexists as [e Hexists]; 
      destruct Hexists as [Hmap1 Hexists]; destruct Hexists as [HeqTargetE HinRightsE].
    (* show that MapsTo k e src *)
    apply Obj.MapS.remove_3 in Hmap1.
    apply H.
    (* the case analysis is 
       rgt := rgt1
       cap := e
       ind := k
       lbl' := lbl
       src1 := src
       lbl := lbl
       src := src
       s := s *)

    case (Ref.eq_dec (Cap.target cap) (Cap.target e)); intros Htargets.
    (* case where (target e) [=] (target cap) *)
    apply_ex_intro_dirAcc s s src_ref1 src lbl src_type src_sched src lbl src_type src_sched k e 
    src lbl src_type src_sched src lbl src_type src_sched rgt1.
    apply Sys.eq_refl.
    apply Sys.eq_refl.
    apply Sys.P.eq_refl.
    apply ObjectLabel.eq_sym; assumption.

    apply Sys.MapS.find_2 in Hopt1.
    apply (Sys.MapS.MapsTo_1 Htargets Hopt1).

    apply Sys.P.eq_refl.
    apply ObjectLabel.eq_sym; assumption.
    Require Import AccessRights.
    apply Edge.eq_sym;
      apply Edge.eq_sym in HeqEdge;
        eapply Edge.eq_trans; 
          [ apply HeqEdge 
            | eapply Edges.edge_equal; eauto]; 
          try solve [apply Ref.eq_refl|
            eapply Ref.eq_trans; [apply Ref.eq_sym; apply HeqTargetE | apply Ref.eq_refl]|
              apply AccessRights.AccessRight.eq_refl].



    (* case where (target e) [!=] (target cap) *)

    generalize (Sys.eq_trans (Sys.eq_sym HeqS) Heq); intros HeqSrev.

    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ HeqSrev
      _ _ HmapScap
      _ (Ref.eq_refl (Cap.target cap1))) as [exP Hex].
    destruct_tuple exP cap_obj1 cap_lbl1 cap_type1 cap_sched1.
    destruct_tuple Hex Hex1 Hex3 Hex4 Hex5.
    destruct Hex1 as [Hex1 Hex2].
    simpl in Hex1; simpl in Hex2; simpl in Hex3; simpl in Hex4; simpl in Hex5.
    destruct_tuple HeqPcap HeqCapSrc1 HeqCapLbl1 HeqCapType1 HeqCapSched1.
    simpl in HeqCapSrc1; simpl in HeqCapLbl1; simpl in HeqCapType1; simpl in HeqCapSched1.
    apply Sys_Facts.add_mapsto_iff in Hex5.
    destruct Hex5 as [Hex5 | Hex5];
      destruct Hex5 as [Hex5 Hex5']; 
        try (rewrite <- Hex5 in HeqTargetE; apply sym_eq in HeqTargetE; contradiction).
    fold Ref.eq in Hex5. (* fixing some unfolding *)

    (* I believe we have enough to apply_ex_intro_diracc *)


    apply_ex_intro_dirAcc s s src_ref1 src lbl src_type src_sched src lbl src_type src_sched k e 
    cap_obj1 cap_lbl1 cap_type1 cap_sched1 cap_obj1 cap_lbl1 cap_type1 cap_sched1 rgt1.

    apply Sys.eq_refl.
    apply Sys.eq_refl.
    apply Sys.P.eq_refl.
    apply ObjectLabel.eq_sym; assumption.
    apply Sys.MapS.MapsTo_1 with (Cap.target cap1); auto.
    apply Sys.P.eq_refl.
    rewrite <- Hex2; rewrite HeqCapLbl1; auto.
    apply Edge.eq_trans with (x := (Edges.mkEdge src_ref1 (Cap.target e) rgt1)) in HeqEdge;
      [auto | eapply Edges.edge_equal; auto].
    apply Ref.eq_refl.
    apply AccessRight.eq_refl.

  (* does not exist case *)
    apply Hexists in Hcompat; clear Hexists; rename Hcompat into Hexists.
    unfold Obj_Exists.Exists in Hexists.
    contradict Hexists.
    (* presumably k = ind1 and e = cap1 *)
    apply ex_intro with ind1.
    (* we know that s1' [=] do_revoke and
       MapsTo ind1 cap1 src1' *)
    (* should know 
       (MapsTo src_ref1 (src1, lbl1) 
         (Sys.MapS.add (Sem.Sys.Obj.Cap.target cap)
           (Obj.MapS.remove c src, lbl) s)) *)
    (* This should give us
       src1 [=] Obj.MapS.remove c src *)
    (* Transitively, src1' [=] Obj.MapS.remove c src *)
    (* by Sys.eq, this should give us MapsTo ind1 cap1 (Obj.MapS.remove c src) *)
    generalize (Sys.eq_trans (Sys.eq_sym HeqS) Heq); intros HeqSrev.
(*     Require Import OrdFMapEquiv.
    Module ObjEquiv := MakeEquiv Obj.
    Module Sys_Equiv := MakeEquiv Sys. *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ HeqSrev
      _ _ HmapS
      _ (Ref.eq_refl src_ref1)) as [exP Hex]; 
    destruct_tuple exP src1'' lbl1'' type1'' sched1''; simpl in Hex;
      destruct Hex as [Hex1 Hex5]; destruct_tuple Hex1 Hex1 Hex2 Hex3 Hex4;
        destruct_tuple HeqP HeqSrc1 HeqLbl1 HeqType1 HeqSched1; 
        simpl in HeqSrc1; simpl in HeqLbl1; simpl in HeqType1; simpl in HeqSched1.
(*    Require FMapFacts.
   Module Sys_Facts := FMapFacts.Facts Sys.MapS. *)
    apply Sys_Facts.add_mapsto_iff in Hex5.
    destruct Hex5 as [Hex5 | Hex5];
      destruct Hex5 as [Hex5 Hex5']; try contradiction.
    fold Ref.eq in Hex5. (* fixing some unfolding *)
    inversion Hex5'.
    rewrite H1 in *.
    generalize (Obj_MapEquiv.exists_mapsTo_eq 
      _ _ (Obj.eq_trans (Obj.eq_sym HeqSrc1) Hex1)
      _ _ Hmap0
      _ (Ind.eq_refl ind1)); intros Hex'.
    destruct Hex' as [cap'' Hex'].
    destruct Hex' as [Hex'1 Hex'2].
    apply ex_intro with cap''.
    split; [|split]; auto.
    apply Cap.target_eq; auto.
    eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto].
    (* case where c [<>] ind1 *)
    (* introduce s1' [=] destruct def *)
    generalize (Sys.eq_trans (Sys.eq_sym HeqS) Heq); intros HeqSrev.
    (* use (HmapS : Sys.MapS.MapsTo src_ref1 (src1, lbl1) s1') to show
       exists src1'' lbl1'',
       (src1'', lbl1'') = (src1, lbl1) /\
       Sys.MapS.MapsTo src_ref1 (src1'', lbl1'') destruct_def *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ HeqSrev
      _ _ HmapS
      _ (Ref.eq_refl src_ref1)) as [exP Hex]; 
    destruct_tuple exP src1'' lbl1'' type1'' sched1''; simpl in Hex;
      destruct Hex as [Hex1 Hex5]; destruct_tuple Hex1 Hex1 Hex2 Hex3 Hex4;
        destruct_tuple HeqP HeqSrc1 HeqLbl1 HeqType1 HeqSched1; 
        simpl in HeqSrc1; simpl in HeqLbl1; simpl in HeqType1; simpl in HeqSched1.
    (* start relating src1'' and lbl1'' to src1 and lbl1*)
    apply Sys_Facts.add_mapsto_iff in Hex5.
    destruct Hex5 as [Hex5 | Hex5];
      destruct Hex5 as [Hex5 Hex5']; try contradiction.
    fold Ref.eq in Hex5. (* fixing some unfolding *)
    inversion Hex5'.
    (* use Hmap0 : Sem.Sys.Obj.MapS.MapsTo ind1 cap1 src1' to show 
       exists cap'', cap'' = cap1 /\
       Obj.MapS.MapsTo ind1 cap'' src1'*)
    generalize (Obj_MapEquiv.exists_mapsTo_eq 
      _ _ (Obj.eq_trans (Obj.eq_sym HeqSrc1) Hex1)
      _ _ Hmap0
      _ (Ind.eq_refl ind1)); intros Hex';
    destruct Hex' as [cap'' Hex'];
      destruct Hex' as [Hex'1 Hex'2].
    (* Show Obj.MapS.MapsTo ind1 cap'' src *)
    rewrite <- H1 in Hex'2.
    apply Obj.MapS.remove_3 in Hex'2.

    (* find a tuple that exists for  (target cap1) *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ HeqSrev
      _ _ HmapScap
      _ (Ref.eq_refl (Cap.target cap1))) as [exP Hex].
    destruct_tuple exP cap_obj1 cap_lbl1 cap_type1 cap_sched1.
    destruct_tuple Hex HCex1 HCex3 HCex4 HCex5.
    destruct HCex1 as [HCex1 HCex2].
    simpl in HCex1; simpl in HCex2; simpl in HCex3; simpl in HCex4; simpl in HCex5.
    destruct_tuple HeqPcap HeqCapSrc1 HeqCapLbl1 HeqCapType1 HeqCapSched1.
    simpl in HeqCapSrc1; simpl in HeqCapLbl1; simpl in HeqCapType1; simpl in HeqCapSched1.
    apply Sys_Facts.add_mapsto_iff in HCex5.
    destruct HCex5 as [HCex5 | HCex5];
      destruct HCex5 as [HCex5 HCex5'];
        fold Ref.eq in HCex5. (* fixing some unfolding *)
    (* case where (target cap) [=] (target cap1) *)
    inversion HCex5'.


    (* Apply dirAcc_spec and instantiate*)
    apply H;
      apply_ex_intro_dirAcc s s src_ref1 src lbl src_type src_sched src lbl src_type src_sched ind1 cap'' 
      src lbl src_type src_sched src lbl src_type src_sched rgt1;

(*      apply_ex_intro_dirAcc s s src_ref1 src lbl src lbl ind1 cap'' rgt1; *)
      try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
        try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
          try apply ObjectLabels.ObjectLabel.eq_sym; auto.
    
    apply Sys.MapS.MapsTo_1 with (Cap.target cap); auto;
      [apply Ref.eq_trans with (Cap.target cap1); [auto | apply Cap.target_eq; auto]
        | apply Sys.MapS.find_2 in Hopt1; apply Hopt1].

    eapply Edge.eq_trans; try apply HeqEdge;
      eapply Edges.edge_equal; try apply Cap.target_eq; try apply AccessRight.eq_refl; try apply Ref.eq_refl; auto.

    (* case where (target cap [<>] (target cap1) *)
    apply H;
      apply_ex_intro_dirAcc s s src_ref1 src lbl src_type src_sched src lbl src_type src_sched ind1 cap'' 
      cap_obj1 cap_lbl1 cap_type1 cap_sched1 cap_obj1 cap_lbl1 cap_type1 cap_sched1 rgt1;

      try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
        try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
          try apply ObjectLabels.ObjectLabel.eq_sym; auto.
    
    apply Sys.MapS.MapsTo_1 with (Cap.target cap1); auto; apply Cap.target_eq; auto.

    apply ObjectLabel.eq_trans with cap_lbl'; auto; apply ObjectLabel.eq_trans with cap_lbl; auto.

    eapply Edge.eq_trans; try apply HeqEdge;
      eapply Edges.edge_equal; try apply Cap.target_eq; try apply AccessRight.eq_refl; try apply Ref.eq_refl; auto.

    (* case where Cap.target cap [<>] src_ref1 *)
    (* introduce s1' [=] destruct def *)
    generalize (Sys.eq_trans (Sys.eq_sym HeqS) Heq); intros HeqSrev.
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ HeqSrev
      _ _ HmapS
      _ (Ref.eq_refl src_ref1))as [exP Hex]; 
    destruct_tuple exP src1'' lbl1'' type1'' sched1''; simpl in Hex;
      destruct Hex as [Hex1 Hex5]; destruct_tuple Hex1 Hex1 Hex2 Hex3 Hex4;
        destruct_tuple HeqP HeqSrc1 HeqLbl1 HeqType1 HeqSched1; 
        simpl in HeqSrc1; simpl in HeqLbl1; simpl in HeqType1; simpl in HeqSched1.
    apply Sys.MapS.add_3 in Hex5; auto.

    (* find a tuple that exists for  (target cap1) *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ HeqSrev
      _ _ HmapScap
      _ (Ref.eq_refl (Cap.target cap1))) as [exP Hex].
    destruct_tuple exP cap_obj1 cap_lbl1 cap_type1 cap_sched1.
    destruct_tuple Hex HCex1 HCex3 HCex4 HCex5.
    destruct HCex1 as [HCex1 HCex2].
    simpl in HCex1; simpl in HCex2; simpl in HCex3; simpl in HCex4; simpl in HCex5.
    destruct_tuple HeqPcap HeqCapSrc1 HeqCapLbl1 HeqCapType1 HeqCapSched1.
    simpl in HeqCapSrc1; simpl in HeqCapLbl1; simpl in HeqCapType1; simpl in HeqCapSched1.
    apply Sys_Facts.add_mapsto_iff in HCex5.
    destruct HCex5 as [HCex5 | HCex5];
      destruct HCex5 as [HCex5 HCex5'];
        fold Ref.eq in HCex5. (* fixing some unfolding *)
    (* case where (target cap) [=] (target cap1) *)
    inversion HCex5'.
    (* Apply dirAcc_spec and instantiate*)
    apply H;
      apply_ex_intro_dirAcc s s src_ref1 src1'' lbl1'' type1'' sched1'' src1' lbl1' type1' sched1'
      ind1 cap1 src lbl src_type src_sched src lbl src_type src_sched rgt1;
      try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
        try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
          try apply ObjectLabels.ObjectLabel.eq_sym; auto.
    (* situtations not handled above *)
    unfold Sys.P.eq; simpl; split; 
      [split; 
        [split; 
          [eapply Obj.eq_trans; [apply Obj.eq_sym; apply Hex1 |] 
            | rewrite <- Hex2] 
          | rewrite <- Hex3] 
        | rewrite <- Hex4]; auto.
    eapply Sys.MapS.MapsTo_1; [apply HCex5 | apply Sys.MapS.find_2; apply Hopt1].


    (* case where (target cap) [<>] (target cap1) *)
    (* apply H, instantiate *)
    apply H.
    apply_ex_intro_dirAcc s s src_ref1 src1'' lbl1'' type1'' sched1'' src1' lbl1' type1'' sched1''
    ind1 cap1 cap_obj1 cap_lbl1 cap_type1 cap_sched1 cap_obj1 cap_lbl1 cap_type1 cap_sched1 rgt1;
    try apply Sys.eq_refl; try apply Sys.P.eq_refl.
    (* situations not handled above *)
    unfold Sys.P.eq; simpl; split; 
      [split; 
        [split; 
          [eapply Obj.eq_trans; [apply Obj.eq_sym; apply Hex1 |] 
            | rewrite <- Hex2] 
          | rewrite <- Hex3] 
        | rewrite <- Hex4]; auto.
    apply ObjectLabel.eq_trans with cap_lbl; auto; apply ObjectLabel.eq_trans with cap_lbl'; auto.
  Qed.
  
  Theorem dirAcc_destroy: forall s ag,
    dirAcc_spec s ag ->
    forall a t ag', dirAcc_spec (Sem.do_destroy a t s) ag' ->
      AG.Subset ag' ag.
  Proof.
    intros.
    unfold dirAcc_spec in *; unfold AG.Subset in *; intros x Hsub.
    (* this would definitely be useful to generalize *)
    case (SemDefns.destroy_preReq_dec a t s); intros Hpre; 
      [generalize (Sem.destroy_valid _ _ _ Hpre)
        | generalize (Sem.destroy_invalid _ _ _ Hpre)]; intros Heq;
      [|apply dirAcc_spec_eq_1 with (s:=Sem.do_destroy a t s) (s':=s) (ag:=ag'); auto].
    (* case where destroy happens *)
    (* unfold preReq *)
    unfold SemDefns.destroy_preReq in Hpre; destruct Hpre as [Hpre HhasWrite]; 
      unfold_preReq Hpre Halive HtargetAlive HisActive.
    (* unfold Sem.preReq in Hpre; destruct Hpre as [Halive HtargetAlive];
       destruct HtargetAlive as [HisActive HtargetAlive];
       unfold Sem.target_is_alive in Halive; unfold Sem.SC.is_alive in Halive;
       unfold Sem.SC.is_label in Halive; red in Halive. *)
    (* simplify Halive by cases on Sem.SC.getObjLabel a s *)
    (* contradiction in the None case *)
    unfold SC.getLabel in *.
    case (option_sumbool (SC.getObjTuple a s)); intros Hopt2;[|destruct Hopt2 as [pair Hopt2]];
      rewrite Hopt2 in Halive; 
        [contradiction| destruct_tuple pair actor actor_lbl actor_type actor_sched; simpl in Halive].
    (* simplify Heq by cases on SC.getCap t a s *)
    case (option_sumbool (SC.getCap t a s)); intros Hopt; 
      [|destruct Hopt as [cap Hopt]]; rewrite Hopt in Heq; simpl in Heq;
    (* case where destroy doesn't happen because cap is gone *) 
    (* reduced to do_destroy [=] s *)
        try solve [apply dirAcc_spec_eq_1 with (s:=Sem.do_destroy a t s) (s':=s) (ag:=ag'); auto].
    (* case where cap exists and revoke occurrs *)
    (* simplify HtargetAlive *)
    unfold SemDefns.target_is_alive in HtargetAlive.
    rewrite Hopt in HtargetAlive;simpl in HtargetAlive; unfold SC.is_alive in HtargetAlive;
      unfold SC.is_label in HtargetAlive; unfold SC.getLabel in HtargetAlive; unfold option_map1 in HtargetAlive.
    unfold SC.is_active in HisActive; unfold SC.is_type in HisActive;
      unfold option_map1 in HisActive; rewrite Hopt2 in HisActive; simpl in HisActive.
    (* simplify set_dead in Heq and HtargetAlive *)
    unfold SC.set_dead in Heq;
      unfold SC.set_label in Heq.
    case (option_sumbool (SC.getObjTuple (Cap.target cap) s)); intros Hopt1;
      [|destruct Hopt1 as [tuple Hopt1]]; rewrite Hopt1 in Heq; simpl in Heq;
        rewrite Hopt1 in HtargetAlive; simpl in HtargetAlive;
    (* case where no object exists *)
    (* Target must exist and be alive. *)
          try solve [contradiction].
    (* case where an object exists *)
    (* break up objLbl and simplify in Heq *)
    destruct_tuple tuple src lbl src_type src_sched.
    unfold SC.addObjTuple in Heq; simpl in Heq.
    (* specialize both assumptions on x*)
    generalize (H x); clear H; intros H.
    generalize (H0 x); clear H0; intros H0.
    (* build all assumptions from H0 *)
    destruct H0 as [_ H0].
    generalize (H0 Hsub); clear H0; intros H0.
    destruct_dirAcc H0 s1' HeqS src_ref1 src1 lbl1 type1 sched1 HmapS src1' 
    lbl1' type1' sched1' HeqP HeqL ind1 cap1 Hmap0 cap_obj cap_lbl cap_type cap_sched HmapScap
    cap_obj' cap_lbl' cap_type' cap_sched' HeqPcap HaliveCap rgt1 HinR HeqEdge.
    (* we should now know enough to apply H. *)
    (* introduce s1' [=] destroy def *)
    generalize (Sys.eq_trans (Sys.eq_sym HeqS) Heq); intros HeqS'.
    (* show
       exists (src1'', lbl1''), src1 [=] src1'' /\ lbl1 [=] lbl1'' /\
       MapsTo src_ref1 (src1'', lbl1'') destruct_def *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ HeqS'
      _ _ HmapS
      _ (Ref.eq_refl src_ref1)) as [exP Hex]; 
    destruct_tuple exP src1'' lbl1'' type1'' sched1''; simpl in Hex;
      destruct Hex as [Hex1 Hex5]; destruct_tuple Hex1 Hex1 Hex2 Hex3 Hex4.
    (* break down HeqP *)
    unfold Sys.P.eq in HeqP; simpl in HeqP;
      destruct_tuple HeqP HeqSrc1 HeqLbl1 HeqType1 HeqSched1.
    (* break down HeqPcap *)
    unfold Sys.P.eq in HeqPcap; simpl in HeqPcap;
      destruct_tuple HeqPcap HeqCapSrc1 HeqCapLbl1 HeqCapType1 HeqCapSched1.
    (* this means that it's in s by add def *)
    apply Sys.MapS.add_3 in Hex5; auto; (*subgoal 2 will contradict by isalive *)
    (* Sys.MapS.add_3 subgoal 2, by contradiction *)
    (* if we assumed (Cap.target cap) [=] src_ref1,
       then by (MapsTo_add Hex5), lbl1'' [=] dead, but lbl1'' [=] lbl1 [=] lbl1' [=] alive *)
      [| intro Hfalse;
        apply ObjectLabel.eq_trans with (x:=lbl1') in Hex2; auto;
          apply ObjectLabel.eq_trans with (x:=ObjectLabels.alive) in Hex2; auto;
            apply Sys_Facts.add_mapsto_iff in Hex5;
              destruct Hex5 as [Hex5 | Hex5];
                destruct Hex5 as [Hex5 Hex5']; try contradiction;
                  inversion Hex5';
                    apply ObjectLabel.eq_sym in Hex2;
                      apply ObjectLabel.eq_trans with (x:=ObjectLabels.dead) in Hex2; auto;
                        discriminate Hex2].
    (* show
       exists cap1'', cap1 [=] cap1'' /\
       MapsTo ind1 cap1'' src1'' *)
    generalize (Obj_MapEquiv.exists_mapsTo_eq 
      _ _ (Obj.eq_trans (Obj.eq_sym HeqSrc1) Hex1)
      _ _ Hmap0
      _ (Ind.eq_refl ind1)); intros Hex';
    destruct Hex' as [cap'' Hex'];
      destruct Hex' as [Hex'1 Hex'2].
    (* find a tuple that exists for  (target cap1) *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ HeqS'
      _ _ HmapScap
      _ (Ref.eq_refl (Cap.target cap1))) as [exP HCex].
    destruct_tuple exP cap_obj1 cap_lbl1 cap_type1 cap_sched1.
    destruct_tuple HCex HCex1 HCex3 HCex4 HCex5.
    destruct HCex1 as [HCex1 HCex2].
    simpl in HCex1; simpl in HCex2; simpl in HCex3; simpl in HCex4; simpl in HCex5.
    (* relate cap_obj .. to cap_obj' .. *)
    (* destruct_tuple HeqPcap HeqCapSrc1 HeqCapLbl1 HeqCapType1 HeqCapSched1.
       simpl in HeqCapSrc1; simpl in HeqCapLbl1; simpl in HeqCapType1; simpl in HeqCapSched1. *)
    (* generate mapsto cases *)
    apply Sys_Facts.add_mapsto_iff in HCex5.
    destruct HCex5 as [HCex5 | HCex5];
      destruct HCex5 as [HCex5 HCex5'];
        fold Ref.eq in HCex5. (* fixing some unfolding *)
    (* case where (target cap) [=] (target cap1) *)
    inversion HCex5'.

    (* this is a contradiction by dead = cap_lbl1 = cap_lbl = cap_lbl' = alive *)
    rewrite <- HCex2 in H2; rewrite HeqCapLbl1 in H2; rewrite <- HaliveCap in H2; discriminate H2.

    (* case where (target cap) [<>] (target cap1) *)
    (* Apply dirAcc_spec and instantiate*)
    apply H.
    apply_ex_intro_dirAcc s s src_ref1 src1'' lbl1'' type1'' sched1'' src1'' lbl1'' type1'' sched1''
    ind1 cap'' cap_obj1 cap_lbl1 cap_type1 cap_sched1 cap_obj1 cap_lbl1 cap_type1 cap_sched1 rgt1; 
    try apply Sys.eq_refl; try apply Sys.P.eq_refl; 
      try (eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hex'1| auto]);
        try apply ObjectLabels.ObjectLabel.eq_sym; auto.
    (* situations not handled above *)
    apply ObjectLabel.eq_trans with lbl1; auto;
      apply ObjectLabel.eq_trans with lbl1'; auto.
    apply Sys.MapS.MapsTo_1 with (Cap.target cap1); 
      [ apply Ref.eq_trans with (Cap.target cap1); [auto | apply Cap.target_eq; auto] | auto].
    (* same strategy as before, but no discrimination *)
    rewrite <- HCex2; rewrite HeqCapLbl1; rewrite <- HaliveCap; auto.
    eapply Edge.eq_trans; try apply HeqEdge;
      eapply Edges.edge_equal; try apply Cap.target_eq; try apply AccessRight.eq_refl; try apply Ref.eq_refl; auto.
  Qed.

  (* adding all rgt in (rights a.c), (mkEdge (target a.t) (target a.c) rgt) to ag
     is a dirAcc_spec of store *)
  Theorem dirAcc_store: forall s ag,
    dirAcc_spec s ag ->
    forall a t c i ag', 
      dirAcc_spec (Sem.do_store a t c i s) ag' ->
      AG.Subset ag' (ag_push_cap_by_indices a t a c s (fun c=>c) ag_add_cap_valid_std ag).
  Proof.
    intros; (* unfold dirAcc_spec in *; *) intros.
    (* first, by cases on satisfying the prereq, then finding both caps *)
    case (SemDefns.store_preReq_dec a t s); intros Hpre; 
      [generalize (Sem.store_valid _ _ c i _ Hpre)
        | generalize (Sem.store_invalid _ _ c i _ Hpre)]; intros Heq.
    (* case where preReq is satisfied *)
    (* unfold preReq *)
    unfold SemDefns.store_preReq in Hpre; destruct Hpre as [Hpre HhasWrite]; 
      unfold_preReq Hpre Halive HtargetAlive HisActive. 
    (* simplify Halive by cases on SC.getObjLabel a s *)
    (* contradiction in the None case *)
    unfold SC.getLabel in *.
    case (option_sumbool (SC.getObjTuple a s)); intros Hopt2;[|destruct Hopt2 as [pair Hopt2]];
      rewrite Hopt2 in Halive; 
        [contradiction| destruct_tuple pair actor actor_lbl actor_type actor_sched; simpl in Halive].
    (* simplify Heq by cases on SC.getCap t a s *)
    case (option_sumbool (SC.getCap t a s)); intros Hopt; 
      [|destruct Hopt as [cap Hopt]]; rewrite Hopt in Heq; simpl in Heq;
    (* unfold and rewrite *)
        unfold ag_push_cap_by_indices; unfold ag_add_cap_by_obj_index;
          unfold ag_add_cap_valid; unfold ag_add_cap_valid_std; unfold ag_add_cap_valid_allocate;
            rewrite Hopt; simpl.
    (* case where getCap t a s = None, no change to ag *)
    (* reduces to In edge ag *) 
    assert (AG.eq ag ag');
      [eapply dirAcc_spec_eq;
        first 
          [apply Heq 
            | eapply (dirAcc_spec_iff Heq (AG.eq_refl ag)) 
            | eapply (dirAcc_spec_iff Heq (AG.eq_refl ag'))]; auto |].

    apply AGProps.subset_equal; apply AGProps.equal_sym; auto.

    (* case where getCap t a s = Some cap *)
    unfold SC.copyCap in Heq.
    case (option_sumbool (SC.getCap c a s)); intros Hopt1; 
      [|destruct Hopt1 as [cap1 Hopt1]]; rewrite Hopt1 in Heq; simpl in Heq; rewrite Hopt1; simpl.
    (* case where getCap c a s = None *)
    (* reduces to Subset ag' ag with Equal ag ag' *)
    Ltac subset_reduction ag ag' Heq:=  
    assert (AG.eq ag ag');
      [eapply dirAcc_spec_eq;
        first 
          [apply Heq 
            | eapply (dirAcc_spec_iff Heq (AG.eq_refl ag)) 
            | eapply (dirAcc_spec_iff Heq (AG.eq_refl ag'))]; auto 
        | apply AGProps.subset_equal; apply AGProps.equal_sym; auto].
    subset_reduction ag ag' Heq.
    (* case where getCap c a s = Some cap1 *)
    unfold SC.addCap in Heq.
    unfold SC.getObj in Heq.
    case (option_sumbool (SC.getObjTuple (Cap.target cap) s)); intros Hopt3;
      [|destruct Hopt3 as [tuple Hopt3]]; rewrite Hopt3 in Heq; simpl in Heq; simpl.
    (* case where getObjTuple (target cap) s = None *)
    (* this means that a obj is not alive, so this reduces to In edge ag *)
    (* Instantiate each side, and show one is a contradiction *)

    case (SC.is_alive_dec (Cap.target cap) s); intros Halive1; simpl; auto;
      [unfold SC.is_alive in Halive1; unfold SC.is_label in Halive1; unfold SC.getLabel in Halive1;
        rewrite Hopt3 in Halive1; simpl in Halive1; contradiction 
        | ].

    (* reduces to Subset ag' ag with Equal ag ag' *) 
    subset_reduction ag ag' Heq.

    (* case where getObjTuple (target cap) s = Some tuple*)
    (* unfold and simplify Heq *)
    unfold SC.updateObj in Heq.
    rewrite Hopt3 in Heq; simpl in Heq.
    destruct_tuple tuple obj obj_lbl obj_type obj_sched.
    unfold SC.tupleGetObj in Heq; simpl.
    unfold SC.addObjTuple in Heq.
(*    Module OC := SC.OCap. *)
    unfold OC.addCap in Heq.
    unfold SC.update_pair_object in Heq.
    case (SC.is_alive_dec (Cap.target cap) s); intros Halive1; simpl; auto;
      [case (SC.is_alive_dec (Cap.target cap1) s); intros Halive2; simpl; auto|].
    (* case where both (Cap.target cap) and (Cap.target cap) are alive *)
    (* alright.  We have reduced Heq to its minimal form.
       We should go back and prove something about ag_add_cap and system state adds. *)
    apply dirAcc_addCap_subset with (index := i) (obj := obj)
      (obj_lbl := obj_lbl) (obj_type := obj_type) (obj_sched := obj_sched) (s := s) (ag:=ag); auto;
        try apply (dirAcc_spec_iff Heq (AG.eq_refl ag')); auto;
          try apply Sys.MapS.find_2; auto.
    
    (* next case, ~ is_alive (target cap1) *)
    apply dirAcc_addCap_notAlive_2 with (s:=s) (ref:= (Cap.target cap)) (index:=i) (cap:=cap1)
      (obj:=obj) (obj_lbl:=obj_lbl) (obj_type:=obj_type) (obj_sched:=obj_sched); auto;
        try (apply Sys.MapS.find_2; auto);
          try (eapply dirAcc_spec_iff; solve [apply Sys.eq_sym; apply Heq | apply AG.eq_refl | auto]).
    
    (* case where ~ alive (target cap) *)
    apply dirAcc_addCap_notAlive_1 with (s:=s) (ref:= (Cap.target cap)) (index:=i) (cap:=cap1)
      (obj:=obj) (obj_lbl:=obj_lbl) (obj_type:=obj_type) (obj_sched:=obj_sched); auto;
        try (apply Sys.MapS.find_2; auto);
          try (eapply dirAcc_spec_iff; solve [apply Sys.eq_sym; apply Heq | apply AG.eq_refl | auto]).
    
    (* case where prereq is not satisfied *)
    assert (AG.eq ag' ag); eauto.
    eapply dirAcc_spec_eq; eauto.
  Qed.

 (* okay, so I shouldn't need to check on whether read is in cap.  I should also not need
   to have a weakened version, since weaken just reduces the number of rights in the cap. 
   We're relating this as subset to known trans steps, so it doesn't matter.
   However, we choose to break things down by read and weak case, and then unify.
   This way, more accurate proofs can be made in the future.*)

  Theorem dirAcc_fetch_read: forall s ag,
    dirAcc_spec s ag ->
    forall a t c i ag', 
      dirAcc_spec (Sem.do_fetch a t c i s) ag' ->
      SemDefns.option_hasRight (SC.getCap t a s) AccessRights.rd ->
      AG.Subset ag' (ag_add_cap_by_indirect_index a t c s (fun c => c) ag_add_cap_valid_std ag).
  Proof.
    intros.
    (* first, by cases on satisfying the prereq *)
    case (SemDefns.fetch_preReq_dec a t s); intros Hpre;
   [ generalize (Sem.fetch_read _ _ c i _ Hpre) | generalize (Sem.fetch_invalid _ _ c i _ Hpre)]; intros Heq;
     [|assert (AG.eq ag' ag); eauto; eapply dirAcc_spec_eq; eauto].
    (* case where preReq is satisfied *)
    (* unfold preReq *)
    unfold SemDefns.fetch_preReq in Hpre; destruct Hpre as [Hpre HhasRight]; 
      unfold_preReq Hpre Halive HtargetAlive HisActive. 
    (* eliminate read *)
    clear HhasRight.
    (* simplify Halive by cases on SC.getObjLabel a s *)
    (* contradiction in the None case *)
    unfold SC.getLabel in *.
    case (option_sumbool (SC.getObjTuple a s)); intros Hopt2;[|destruct Hopt2 as [pair Hopt2]];
      rewrite Hopt2 in Halive; 
        [contradiction| destruct_tuple pair actor actor_lbl actor_type actor_sched; simpl in Halive].
    (* simplify Heq.*)
    unfold SC.copyCap in Heq.    
    (* simplify Goal *)
    unfold ag_add_cap_by_indirect_index; unfold ag_add_cap_by_obj_index;
      unfold ag_add_cap_valid; unfold ag_add_cap_valid_std; unfold ag_add_cap_valid_allocate. 
    (* we know that (getCap t a s) exists by option_hasRight, so intro case and contradict *)
    (* apply in Heq and simplify in goal *)
    case (option_sumbool (SC.getCap t a s)); intros Hopt3;[|destruct Hopt3 as [invoked_cap Hopt3]];
      rewrite Hopt3 in H1; simpl in H1; rewrite Hopt3 in Heq; simpl in Heq;
        [contradiction| generalize (Heq H1); clear Heq; intros Heq; rewrite Hopt3; simpl ]. 
    (* simplify Heq and goal by cases on SC.getCap c (target invoked_cap) s *)
    case (option_sumbool (SC.getCap c (Cap.target invoked_cap) s)); intros Hopt; 
      [|destruct Hopt as [copied_cap Hopt]]; rewrite Hopt in Heq; simpl in Heq; rewrite Hopt; simpl.
    (* first case reduces to In edge ag with fetch [=] s *) 
    assert (AG.eq ag ag');
      [eapply dirAcc_spec_eq;
        first 
          [apply Heq 
            | eapply (dirAcc_spec_iff Heq (AG.eq_refl ag)) 
            | eapply (dirAcc_spec_iff Heq (AG.eq_refl ag'))]; auto | auto].
    (* now we come to the is_alive material *)
    (* we know is_alive a s, it was an assumption, now unfolded and blown apart.  assert it. *)
    assert (SC.is_alive a s) as HisAlive;
      [unfold SC.is_alive;
        unfold SC.is_label;
        unfold SC.getLabel;
          rewrite Hopt2; simpl; auto|].
    unfold true_bool_of_sumbool;
      rewrite (proof_r_true_bool_of_sumbool _ (SC.is_alive_dec a s) HisAlive);
        clear HisAlive;
          rewrite andb_true_l.
    (* we do not know if the target of the copied cap is alive, but one case allows us to use dirAcc_spec_not_alive1/2 to reduce to ag.*)
    (* simpolify Heq *)
    unfold SC.addCap in Heq.
    unfold SC.getObj in Heq.
    unfold SC.updateObj in Heq.
    unfold OC.addCap in Heq.
    unfold SC.addObjTuple in Heq.
    rewrite Hopt2 in Heq; simpl in Heq.
    (* cases on whether the target of the copied cap is alive *)
    case (SC.is_alive_dec (Cap.target copied_cap) s); intros Halive1; simpl; auto.
    (* case where (target copied_cap) is alive *)
    (* fetch reduced to minimal form *)
    apply dirAcc_addCap_subset with (index := i) (obj := actor)
      (obj_lbl := actor_lbl) (obj_type := actor_type) (obj_sched := actor_sched) (s := s) (ag:=ag); auto;
        try apply (dirAcc_spec_iff Heq (AG.eq_refl ag')); auto;
          try apply Sys.MapS.find_2; auto.    
    (* case where (target copied_cap) is not alive *)
    apply dirAcc_addCap_notAlive_2 with (s:=s) (ref:= a) (index:=i) (cap:=copied_cap)
      (obj:=actor) (obj_lbl:=actor_lbl) (obj_type:=actor_type) (obj_sched:=actor_sched); auto;
        try (apply Sys.MapS.find_2; auto);
          try (eapply dirAcc_spec_iff; solve [apply Sys.eq_sym; apply Heq | apply AG.eq_refl | auto]).
  Qed.

(* now do fetch_weak *)

  Theorem dirAcc_fetch_weak: forall s ag,
    dirAcc_spec s ag ->
    forall a t c i ag', 
      dirAcc_spec (Sem.do_fetch a t c i s) ag' ->
      ~ SemDefns.option_hasRight (SC.getCap t a s) AccessRights.rd ->
      AG.Subset ag' (ag_add_cap_by_indirect_index a t c s Cap.weaken ag_add_cap_valid_std ag).
  Proof.
    intros.
    (* first, by cases on satisfying the prereq *)
    case (SemDefns.fetch_preReq_dec a t s); intros Hpre;
   [ generalize (Sem.fetch_weak _ _ c i _ Hpre) | generalize (Sem.fetch_invalid _ _ c i _ Hpre)]; intros Heq;
     [|assert (AG.eq ag' ag); eauto; eapply dirAcc_spec_eq; eauto].
    (* case where preReq is satisfied *)
    (* unfold preReq *)
    unfold SemDefns.fetch_preReq in Hpre; destruct Hpre as [Hpre HhasRight]; 
      unfold_preReq Hpre Halive HtargetAlive HisActive. 
    (* eliminate read *)
    destruct HhasRight as [HhasRight|HhasWeak]; try contradiction.
    (* simplify Heq *)
    generalize (Heq H1 HhasWeak); clear Heq; intros Heq.
    (* simplify Halive by cases on SC.getObjLabel a s *)
    (* contradiction in the None case *)
    unfold SC.getLabel in *.
    case (option_sumbool (SC.getObjTuple a s)); intros Hopt2;[|destruct Hopt2 as [pair Hopt2]];
      rewrite Hopt2 in Halive; 
        [contradiction| destruct_tuple pair actor actor_lbl actor_type actor_sched; simpl in Halive].
    (* simplify Heq.*)
    unfold SC.weakCopyCap in Heq; unfold SC.copyCap in Heq.
    (* simplify Goal *)
    unfold ag_add_cap_by_indirect_index; unfold ag_add_cap_by_obj_index;
      unfold ag_add_cap_valid; unfold ag_add_cap_valid_std; unfold ag_add_cap_valid_allocate.
    (* simplify HtargetAlive *)
    unfold SemDefns.target_is_alive in HtargetAlive.
    (* we know that (getCap t a s) exists by option_hasRight, so intro case and contradict *)
    (* apply in Heq and simplify in goal *)
    case (option_sumbool (SC.getCap t a s)); intros Hopt3;[|destruct Hopt3 as [invoked_cap Hopt3]];
      rewrite Hopt3 in H1; simpl in H1; rewrite Hopt3 in Heq; simpl in Heq; 
        rewrite Hopt3 in HtargetAlive; simpl in HtargetAlive;
        [ contradiction | rewrite Hopt3; simpl ]. 
    (* simplify Heq and goal by cases on SC.getCap c (target invoked_cap) s *)
    case (option_sumbool (SC.getCap c (Cap.target invoked_cap) s)); intros Hopt; 
      [|destruct Hopt as [copied_cap Hopt]]; rewrite Hopt in Heq; simpl in Heq; rewrite Hopt; simpl.
    (* first case reduces to In edge ag with fetch [=] s *) 
    assert (AG.eq ag ag');
      [eapply dirAcc_spec_eq;
        first 
          [apply Heq 
            | eapply (dirAcc_spec_iff Heq (AG.eq_refl ag)) 
            | eapply (dirAcc_spec_iff Heq (AG.eq_refl ag'))]; auto | auto].
    (* now we come to the is_alive material *)
    (* we know is_alive a s, it was an assumption, now unfolded and blown apart.  assert it. *)
    assert (SC.is_alive a s) as HisAlive;
      [unfold SC.is_alive;
        unfold SC.is_label;
        unfold SC.getLabel;
          rewrite Hopt2; simpl; auto|].
    unfold true_bool_of_sumbool;
      rewrite (proof_r_true_bool_of_sumbool _ (SC.is_alive_dec a s) HisAlive);
        clear HisAlive;
          rewrite andb_true_l.
    (* we do not know if the target of the copied cap is alive, but one case allows us to use dirAcc_spec_not_alive1/2 to reduce to ag.*)
    (* simpolify Heq *)
    unfold SC.addCap in Heq.
    unfold SC.getObj in Heq.
    unfold SC.updateObj in Heq.
    unfold OC.addCap in Heq.
    unfold SC.addObjTuple in Heq.
    rewrite Hopt2 in Heq; simpl in Heq.
    (* cases on whether the target of the copied cap is alive *)
    case (SC.is_alive_dec (Cap.target copied_cap) s); intros Halive1; simpl; auto.
    (* case where (target copied_cap) is alive *)
    (* fetch reduced to minimal form *)
    apply dirAcc_addCap_subset with (index := i) (obj := actor)
      (obj_lbl := actor_lbl) (obj_type := actor_type) (obj_sched := actor_sched) (s := s) (ag:=ag); auto;
        try apply (dirAcc_spec_iff Heq (AG.eq_refl ag')); auto;
          try apply Sys.MapS.find_2; auto.    
    (* case where (target copied_cap) is not alive *)
    apply dirAcc_addCap_notAlive_2 with (s:=s) (ref:= a) (index:=i) (cap:=(Cap.weaken copied_cap))
      (obj:=actor) (obj_lbl:=actor_lbl) (obj_type:=actor_type) (obj_sched:=actor_sched); auto;
        try (apply Sys.MapS.find_2; auto);
          try (eapply dirAcc_spec_iff; solve [apply Sys.eq_sym; apply Heq | apply AG.eq_refl | auto]).
    idtac.
    intros Hfalse; apply Halive1.
    generalize (CC.weaken_target_eq copied_cap); intros Hweak_eq.
    unfold SC.is_alive in Hfalse; unfold SC.is_alive.
    eapply SC.isLabel_eq with (r:=(Cap.target (Cap.weaken copied_cap))); try apply Hfalse; auto;
      try apply Sys.eq_refl; try apply ObjectLabel.eq_refl.
  Qed.

    Theorem add_dirAcc_exists_Subset: forall s s_add ag ag_add a obj lbl type sched i_add cap_add,
      dirAcc_spec s ag ->
      dirAcc_spec s_add ag_add ->
      Sys.MapS.MapsTo a (obj, lbl, type, sched) s ->
      Sys.eq s_add (Sys.MapS.add a (Obj.MapS.add i_add cap_add obj, lbl, type, sched) s) ->
      Obj_Exists.Exists (fun _ cap => Cap.eq cap cap_add) obj ->
      AG.Subset ag_add ag.
    Proof.
      intros.
      unfold Obj_Exists.Exists in H3;
        destruct H3 as [i H3]; destruct H3 as [cap H3]; destruct H3.
      (* rewrite dirAcc_spec with s' defn inlined *)
      eapply dirAcc_spec_iff in H0; [|apply Sys.eq_sym; apply H2 | eapply AG.eq_refl].
      (* apply dirAcc_spec definitions in goal and Hin *)
      intros edge Hin.
      apply (H edge); clear H.
      apply (H0 edge) in Hin; clear H0; rename Hin into Hda.
      clear s_add H2.
      (* destruct Hda *)
      destruct_dirAcc Hda s' HeqS obj_ref' obj' lbl' type' sched' HmapS obj'' lbl'' type'' sched'' 
      HeqP HeqL i' cap' Hmap0 cap_obj' cap_lbl' cap_type' cap_sched' HmapScap
      cap_obj'' cap_lbl'' cap_type'' cap_sched'' HeqPcap HaliveCap rgt' HinR HeqEdge.
      (* break apart HeqP and HeqPcap *)
      destruct_tuple HeqP HeqSrc HeqLbl HeqType HeqSched; 
      simpl in HeqSrc; simpl in HeqLbl; simpl in HeqType; simpl in HeqSched;
        destruct_tuple HeqPcap HCap1 HCap2 HCap3 HCap4; 
        simpl in HCap1; simpl in HCap2; simpl in HCap3; simpl in HCap4.

      (* these 3 copied from a previous theorem , amy wish to Ltac *)
     
      (* find an ex_obj ... that exists in the state from add. *)
      destruct (Sys_MapEquiv.exists_mapsTo_eq
        _ _ (Sys.eq_sym HeqS)
        _ _ HmapS
        _ (Ref.eq_refl obj_ref')) as [exP Hex];
      destruct_tuple exP ex_obj' ex_lbl' ex_type' ex_sched'; simpl in Hex; destruct Hex as [Hex HexMap];
        destruct_tuple Hex Hex1 Hex2 Hex3 Hex4.
      
      (* find an ex_cap that exists in ex_obj *)
      destruct (Obj_MapEquiv.exists_mapsTo_eq
        _ _ (Obj.eq_trans (Obj.eq_sym HeqSrc) Hex1)
        _ _ Hmap0
        _ (Ind.eq_refl _)) as [ex_cap' HexCapMap];
      destruct HexCapMap as [HexCapEq HexCapMap].
        
      (* find an ex_cap_obj ... that exists in the state from add *)
      destruct (Sys_MapEquiv.exists_mapsTo_eq
        _ _ (Sys.eq_sym HeqS)
        _ _ HmapScap
        _ (Ref.eq_refl (Cap.target cap'))) as [exPcap HCex];
      destruct_tuple exPcap ex_cap'_obj ex_cap'_lbl ex_cap'_type ex_cap'_sched; 
      simpl in HCex; destruct HCex as [HCex HCexMap];
        destruct_tuple HCex HCex1 HCex2 HCex3 HCex4.
    
    (* cases,:
       obj_ref' [=|<>] a (add_mapsto_iff) => Is the source object producing the edge [=] the object being added to?
          False => must exist elsewhere
          True => Next
       i' [=|<>] i_add (add_mapsto_iff) => Is the index in the source object producing the edge [=] the index being overwritten?
          False => Must exist at other index
          True => Next
       i' [=|<>] i => Is the index producing the edge [=] the index of the source cap?
          True => add is a noop, reuse cap.
          False => an equiv cap exists at i in a, Next.
       a [=|<>] (target cap_add) (add_mapsto_iff) => Is the target of the cap producing the edge [=] the object being written to?
          True => an equiv cap is at i in a, and modified target is alive.
          False => an equiv cap is at i in a, and target is unmodified.
*)


      (* begin branch *)
     generalize (Cap.target_eq _ _ HexCapEq); intros HexCapEqTarget.

    (* demonstrate that (target cap') must be alive in s*)
    Module Sys_Exists := SC.Sys_Exists.
    assert (Sys_Exists.Exists (fun ref tuple => Ref.eq ref (Cap.target cap') /\ 
      ObjectLabel.eq (SC.tupleGetLabel tuple) ObjectLabels.alive ) s ) as HexAlive.
    unfold Sys_Exists.Exists.
     (* this will generate 2 subgoals: (Ref.eq_dec rgt (Cap.target cap')) *)
     apply Sys_Facts.add_mapsto_iff in HCexMap;
       destruct HCexMap as [HCexMap|HCexMap];
         destruct HCexMap as [HCexRef HCexMap];
           [ inversion HCexMap as [[HCexMap1 HCexMap2 HCexMap3 HCexMap4]] |].
     (* case 1: a [=] target cap' *)
     eapply Ref.eq_trans in HexCapEqTarget; [ |apply HCexRef].
     apply ex_intro with a; apply ex_intro with (obj,lbl,type,sched).
     split; auto. split; auto. 
     unfold SC.tupleGetLabel; simpl; rewrite HCexMap2; rewrite <- HCex2; rewrite HCap2; apply ObjectLabel.eq_sym; auto.
     (* case 2: a [<>] target cap' *)
     eapply ex_intro; eapply ex_intro.
     split; [apply HCexMap | split; [apply Ref.eq_refl |
          unfold SC.tupleGetLabel; simpl; rewrite <- HCex2; rewrite HCap2; apply ObjectLabel.eq_sym; auto]].
     (* branch out  out target cases *)
     unfold Sys_Exists.Exists in HexAlive.
     unfold SC.tupleGetLabel in HexAlive; simpl in HexAlive;
     destruct HexAlive as [edge_target_ref HexAlive]; destruct HexAlive as [edge_target_tuple HexAlive]; 
       destruct_tuple edge_target_tuple edge_target_obj edge_target_lbl edge_target_type edge_target_sched;
       destruct HexAlive as [Hedge_target_map HexAlive]; destruct HexAlive as [Hedge_target_eq Hedge_target_alive].


(* apply add_mapsto_iff in HexMap to find the cases for add *)
     (* generates 2 subgoals: (Ref.eq_dec a obj_ref') *)
    apply Sys_Facts.add_mapsto_iff in HexMap;
      destruct HexMap as [HexMap | HexMap];
        destruct HexMap as [HexRef HexMap];

    (* Case 1: a [=] obj_ref' case *)
    (* this line is case specific *)
          [ inversion HexMap as [[HexMap1 HexMap2 HexMap3 HexMap4]] |].
    rewrite <- HexMap1 in HexCapMap.
    (* apply add_mapsto_iff in HexCapMap to find the cases for add. *)
    (* generates 2 subgoals : (Ind.eq i_add i') *)
    apply Obj_Facts.add_mapsto_iff in HexCapMap;
      destruct HexCapMap as [HexCapMap|HexCapMap];
        destruct HexCapMap as [HexCapRef HexCapMap].

    (* Case 1.1: i_add [=] i' *)
    assert (Cap.eq cap' cap) as HCap'Eq;[eapply Cap.eq_trans; [apply HexCapEq | rewrite <- HexCapMap; apply Cap.eq_sym; auto]|].
    apply_ex_intro_dirAcc s s a obj lbl type sched obj lbl type sched i cap
    edge_target_obj edge_target_lbl edge_target_type edge_target_sched
    edge_target_obj edge_target_lbl edge_target_type edge_target_sched rgt';
    try apply Sys.eq_refl; try apply Sys.P.eq_refl;
         try apply ObjectLabels.ObjectLabel.eq_sym; auto;
    (* lbl = alive *)
           try solve [rewrite HexMap2; rewrite <- Hex2; rewrite HeqLbl; auto].
    (* MapsTo (target cap) (edge_target_obj, edge_target_lbl, edge_target_type, edge_target_sched) *)
    eapply Sys.MapS.MapsTo_1 in Hedge_target_map; 
      [apply Hedge_target_map | eapply Ref.eq_trans; [apply Hedge_target_eq | apply Cap.target_eq; auto]].
    (* In rgt' (rights cap) *)
    rewrite <- HexCapMap in HexCapEq.
    apply Cap.eq_sym in HexCapEq; apply Cap.eq_trans with (x:=cap) in HexCapEq; auto.
    apply Cap.eq_sym in HCap'Eq; eapply Cap.rights_eq; try apply HCap'Eq; auto.
    (* (mkEdge a (target cap) rgt') [=] edge *)
    apply Edge.eq_sym; eapply Edge.eq_trans; [apply Edge.eq_sym; apply HeqEdge|].
    apply Edges.edge_equal; try solve [apply Ref.eq_sym; auto| eapply Cap.target_eq; auto| apply AccessRight.eq_refl].

    (* Case 1.2 i_add: [<>] i' *)
    apply_ex_intro_dirAcc s s a obj lbl type sched obj lbl type sched i' ex_cap'
    edge_target_obj edge_target_lbl edge_target_type edge_target_sched
    edge_target_obj edge_target_lbl edge_target_type edge_target_sched rgt';
    try apply Sys.eq_refl; try apply Sys.P.eq_refl;
         try apply ObjectLabels.ObjectLabel.eq_sym; auto;
    (* lbl = alive *)
           try solve [rewrite HexMap2; rewrite <- Hex2; rewrite HeqLbl; auto].
    (* MapsTo (target cap) (edge_target_obj, edge_target_lbl, edge_target_type, edge_target_sched) *)
    eapply Sys.MapS.MapsTo_1 in Hedge_target_map; 
      [apply Hedge_target_map | eapply Ref.eq_trans; [apply Hedge_target_eq | apply Cap.target_eq; auto]].
    (* In rgt' (rights ex_cap') *)
    apply Cap.eq_sym in HexCapEq; eapply Cap.rights_eq; [apply HexCapEq|]; auto.
    (* (mkEdge a (target cap) rgt') [=] edge *)
    apply Edge.eq_sym; eapply Edge.eq_trans; [apply Edge.eq_sym; apply HeqEdge|].
    apply Edges.edge_equal; try solve [apply Ref.eq_sym; auto| eapply Cap.target_eq; auto| apply AccessRight.eq_refl].

    (* Case 2: a [<>] obj_ref' case *)
    apply_ex_intro_dirAcc s s obj_ref' ex_obj' ex_lbl' ex_type' ex_sched'
    ex_obj' ex_lbl' ex_type' ex_sched' i' ex_cap'
    edge_target_obj edge_target_lbl edge_target_type edge_target_sched
    edge_target_obj edge_target_lbl edge_target_type edge_target_sched rgt';
    try apply Sys.eq_refl; try apply Sys.P.eq_refl;
         try apply ObjectLabels.ObjectLabel.eq_sym; auto.
    (* ex_lbl' = alive *)
    rewrite <- Hex2; rewrite HeqL; auto.
    (* MapsTo (target ex_cap') (edge_target_obj, edge_target_lbl, edge_target_type, edge_target_sched) *)
    eapply Sys.MapS.MapsTo_1 in Hedge_target_map; 
      [apply Hedge_target_map | eapply Ref.eq_trans; [apply Hedge_target_eq | apply Cap.target_eq; auto]].
    (* In rgt' (rights ex_cap') *)
    apply Cap.eq_sym in HexCapEq; eapply Cap.rights_eq; [apply HexCapEq|]; auto.
    (* (mkEdge a (target cap) rgt') [=] edge *)
    apply Edge.eq_sym; eapply Edge.eq_trans; [apply Edge.eq_sym; apply HeqEdge|].
    apply Edges.edge_equal; try solve [apply Ref.eq_sym; auto| eapply Cap.target_eq; auto| apply AccessRight.eq_refl].
    Qed.


    Theorem add_dirAcc_self_Subset : forall s s' ag ag' i_src a cap cap' obj lbl type sched i_dst,
      dirAcc_spec s ag ->
      dirAcc_spec s' ag' ->
      Sys.MapS.MapsTo a (obj, lbl, type, sched) s ->
      Obj.MapS.MapsTo i_src cap obj ->
      Cap.eq cap cap' ->
      Sys.eq s' (Sys.MapS.add a (Obj.MapS.add i_dst cap' obj, lbl, type, sched) s) ->
      AG.Subset ag' ag.
    Proof.
      intros.
      eapply add_dirAcc_exists_Subset; eauto.
      unfold Obj_Exists.Exists; eapply ex_intro; eapply ex_intro; split; [apply H2| apply H3].
    Qed.


  Theorem dirAcc_send_self: forall s ag,
    dirAcc_spec s ag ->
    forall a t ixi_list opt_i ag', 
      dirAcc_spec (Sem.do_send a t ixi_list opt_i s) ag' ->
      option_map1 (fun cap => Ref.eq a (Cap.target cap)) False (SC.getCap t a s) ->
      AG.Subset ag' (ag_add_caps_reply a t s ag).
  Proof.
    intros s ag H a t ixi_list opt_i.
    (* this is all probably the same as dirAcc_send_other *)
    (* we can't introduce ag', or we won't get a correct induction tactic *)
    case (SemDefns.send_preReq_dec a t s); intros Hpre;
      [ generalize (Sem.send_valid _ _ ixi_list opt_i _ Hpre) 
        | generalize (Sem.send_invalid _ _ ixi_list opt_i _ Hpre)]; intros Heq;
      [|intros; assert (AG.eq ag' ag); eauto; eapply dirAcc_spec_eq; eauto].
    (* case where preReq is satisfied *)
    (* unfold preReq *)
    unfold SemDefns.send_preReq in Hpre; destruct Hpre as [Hpre HhasRight]; 
      unfold_preReq Hpre Halive HtargetAlive HisActive. 
    (* simplify Halive by cases on SC.getObjLabel a s *)
    (* contradiction in the None case *)
    unfold SC.getLabel in *.
    case (option_sumbool (SC.getObjTuple a s)); intros Hopt2;[|destruct Hopt2 as [pair Hopt2]];
      rewrite Hopt2 in Halive; 
        [contradiction| destruct_tuple pair actor actor_lbl actor_type actor_sched; simpl in Halive].
    (* unfold Heq.*)
    unfold SC.copyCapList in Heq; unfold SC.copyCap in Heq.
    (* unfold Goal *)
    unfold ag_add_caps_reply; unfold ag_add_caps_by_index_pair_list; 
      unfold ag_add_cap_by_indirect_index; unfold ag_add_cap_by_obj_index;
        unfold ag_add_cap_valid; unfold ag_add_cap_valid_std; unfold ag_add_cap_valid_allocate.
    (* simplify HtargetAlive *)
    unfold SemDefns.target_is_alive in HtargetAlive.
    (* we know that (getCap t a s) exists by option_hasRight, so intro case and contradict *)
    (* apply in Heq and simplify in goal *)
    case (option_sumbool (SC.getCap t a s)); intros Hopt3;[|destruct Hopt3 as [invoked_cap Hopt3]];
      rewrite Hopt3 in Heq; simpl in Heq; rewrite Hopt3 in HtargetAlive; simpl in HtargetAlive;
        [ contradiction | rewrite Hopt3; simpl ].
  (* we know that (getObjTuple (target invoked_cap) s) exists by is_alive *)
    case (option_sumbool (SC.getObjTuple (Cap.target invoked_cap) s)); intros Hopt4;[|destruct Hopt4 as [invoked_cap_tuple Hopt4]];
      [unfold SC.is_alive in HtargetAlive;
        unfold SC.is_label in HtargetAlive;
        unfold SC.getLabel in HtargetAlive;
          rewrite Hopt4 in HtargetAlive;
            simpl in HtargetAlive;
              contradiction|].
    (* we know is_alive a s, it was an assumption, now unfolded and blown apart.  assert it. *)
    assert (SC.is_alive (Cap.target
                 (Cap.mkCap a
                    (ARSet.singleton AccessRights.tx))) s) as HisAlive.
    unfold SC.is_alive.
    eapply SC.isLabel_eq;
      [apply Ref.eq_sym; eapply CC.mkCap_target
        | eauto
        | apply Sys.eq_refl
        | unfold SC.is_label; unfold SC.getLabel; rewrite Hopt2; simpl; try apply ObjectLabel.eq_refl; auto].
    (* use the above assertion to rewrite true_bool_of_sumbool *)
    unfold true_bool_of_sumbool;
      rewrite (proof_r_true_bool_of_sumbool _ (SC.is_alive_dec _ _) HisAlive);
        rewrite andb_true_r;
          simpl;
            clear HisAlive.
    (* we also know that the invoked cap is alive *)
    rewrite (proof_r_true_bool_of_sumbool _ (SC.is_alive_dec _ _) HtargetAlive); simpl.

    (* now simplify htargetAlive *)
    destruct_tuple invoked_cap_tuple invoked_cap_target invoked_cap_lbl invoked_cap_type invoked_cap_sched.
    unfold SC.is_alive in HtargetAlive;
      unfold SC.is_label in HtargetAlive;
      unfold SC.getLabel in HtargetAlive;
        rewrite Hopt4 in HtargetAlive;
          simpl in HtargetAlive.
  
   (* we may have to induct over ixi_list here.  The reply cap happens in the base case. *)
    induction ixi_list; simpl; simpl in Heq.

    (*okay, to reduce Heq, we have two cases, either we add a reply or not. *)
    intros; destruct opt_i as[i|]; simpl in Heq.

    (* case where things are not equal *)
    (* simpolify Heq *)
    unfold SC.addCap in Heq.
    unfold SC.getObj in Heq.
    unfold SC.updateObj in Heq.
    unfold OC.addCap in Heq.
    unfold SC.update_pair_object in Heq.
    rewrite Hopt4 in Heq.
    simpl in Heq.
    unfold SC.addObjTuple in Heq.
    (* alright.  We have reduced Heq to its minimal form.
       We should go back and prove something about ag_add_cap and system state adds. *)
    apply dirAcc_addCap_subset with (index := i) (obj := invoked_cap_target) (ag:=ag)
      (obj_lbl := invoked_cap_lbl) (obj_type := invoked_cap_type) (obj_sched := invoked_cap_sched) (s := s); auto;
        try apply (dirAcc_spec_iff Heq (AG.eq_refl ag')); auto;
          try apply Sys.MapS.find_2; auto.
    (* case where things are equal *)
    assert (AG.eq ag ag') as HeqAG;
      [eapply dirAcc_spec_eq; apply Sys.eq_sym in Heq; try apply Heq; auto
        | apply ag_eq_Equal in HeqAG; apply AG.eq_sym in HeqAG; auto].

    (* induction case *)
    intros.
    (* destruct the ixi pair *)
    destruct a0 as [i_src i_dst]; simpl in *.
    generalize (Sem.send_valid a t ixi_list opt_i s); intros IHsend.
    (* prereq is in too many pieces *)
    assert (SemDefns.send_preReq a t s) as HpreReq.
    unfold SemDefns.send_preReq.
    split; auto.
    unfold SemDefns.preReq;
      unfold SemDefns.preReqCommon;
    unfold SemDefns.target_is_alive;
    unfold SC.is_alive;
    unfold SC.is_label;
    unfold SC.getLabel;
    unfold SC.is_type.
    rewrite Hopt2; rewrite Hopt3; simpl.
    rewrite Hopt4; simpl.
    split; auto. 
    (* apply HpreReq in IHSend *)
    generalize (IHsend HpreReq); clear IHsend; intros IHsend.
    rewrite Hopt3 in IHsend; simpl in IHsend.
    generalize (IHixi_list IHsend); clear IHsend; clear IHixi_list; intros IH.
    (* okay, we have an IH that will let us recurse, but only if we can instantiate it.
       we have not yet proved that dirAcc_spec is decidable, nor that one always exists.
       If we can show these, thein we can instantiate the IH, and recurse in both cases.*)
    generalize (exists_dirAcc_spec (Sem.do_send a t ixi_list opt_i s)); intros Hex.
    destruct Hex as [ag_spec Hdiracc];
      generalize (IH ag_spec Hdiracc); clear IH; intros IH.
    apply AGFacts.Subset_trans with ag_spec; try apply IH; auto.
    (* we are left with AG.Subset ag' ag_spec, which must be true,
       since each edge in ag_spec is produced by some cap in s + ixi_list.
       self-copying a cap must not actually add any new edge, and so they are equal. *)
    (* generalize the inductive hypothesis send *)
    generalize (Sem.send_valid a t ixi_list opt_i s HpreReq); intros Hsend_i; rewrite Hopt3 in Hsend_i;
      simpl in Hsend_i; unfold SC.copyCapList in Hsend_i; unfold SC.copyCap in Hsend_i.
    (* destruct the cases of getCap i_src a ..., show Subset ag' (dirAcc send) *)
    case (option_sumbool (SC.getCap i_src a
                (fold_right
                   (fun (ixi : Ind.t * Ind.t) (s : Sys.t) =>
                    option_map1
                      (fun cap : Cap.t =>
                       SC.addCap (snd ixi) cap
                         (Cap.target invoked_cap) s) s
                      (SC.getCap (fst ixi) a s))
                   (option_map1
                      (fun i : Ind.t =>
                       SC.addCap i
                         (Cap.mkCap a
                            (ARSet.singleton
                               AccessRights.tx))
                         (Cap.target invoked_cap) s) s opt_i) ixi_list)));
    intros Hopt6; [|destruct Hopt6 as [t_cap Hopt6]]; rewrite Hopt6 in *; simpl in *.
    (* None (...) *)
    (* show that all these are equal, and produce AG.Equal ag' ag_spec *)
    assert (Sys.eq (Sem.do_send a t ((i_src, i_dst) :: ixi_list) opt_i s) (Sem.do_send a t ixi_list opt_i s)) as HsendEq.
    apply Sys.eq_sym in Hsend_i.
    eapply Sys.eq_trans; [apply Heq| apply Hsend_i].
    assert (AG.eq ag' ag_spec) as HagEq;[
      eapply dirAcc_spec_eq; try apply HsendEq; auto|].
    generalize (ag_eq_Equal ag' ag_spec); intros HagEqual; destruct HagEqual as [HagEqual _].
    apply HagEqual in HagEq.
    eauto.

    (* Some ... *)
    assert (Sys.eq (Sem.do_send a t ((i_src, i_dst) :: ixi_list) opt_i s) 
      (SC.addCap i_dst t_cap (Cap.target invoked_cap) (Sem.do_send a t ixi_list opt_i s))) as HsendEq.
(*    apply Sys.eq_sym in Hsend_i. *)
    eapply Sys.eq_trans; [apply Heq | apply SC.addCap_eq; try apply Ref.eq_refl; auto]. 
    (*[apply Heq| apply SC.addCap_eq; auto; apply Sys.eq_sym; auto].*)
   
    (* show 
       AG.eq (dirAcc_spec (SC.addCap i_dst t_cap (Cap.target invoked_cap) (Sem.do_send a t ixi_list opt_i s)))
             (dirAcc_spec (SC.addCap i_dst t_cap (Cap.target invoked_cap) ag_spec)) *)
    unfold SC.addCap in HsendEq.
    unfold OC.addCap in HsendEq.
    unfold SC.updateObj in HsendEq.
    unfold SC.addObjTuple in HsendEq.
    unfold SC.getObj in HsendEq.

    (* okay, bust out the cases in HsendEq.  In all cases, we will end up with an eq, or an (add (send)). 
       in the add (send) case, we should be able to apply dirAcc_addCap_subset. QED. *)
    case (option_sumbool ((SC.getObjTuple (Cap.target invoked_cap) (Sem.do_send a t ixi_list opt_i s)))); intros Hopt_a;
      [|destruct Hopt_a as [tuple_a Hopt_a]]; rewrite Hopt_a in *; simpl in *; 
        [apply AGProps.subset_equal; auto; eapply dirAcc_spec_eq; eauto|].
    destruct_tuple tuple_a obj_a lbl_a type_a sched_a; simpl in *.

    (* begin the setup to add_dirAcc_self_Subset *)

    (* unfold definitions in Hopt 6 *)
    unfold SC.getCap in Hopt6; unfold SC.getObj in Hopt6;
    unfold SC.getObjTuple in Hopt_a; unfold SC.getObjTuple in Hopt6.
    (* change (target invoked_cap) to a in Hopt_a, leave as mapsto *)
    generalize (Sys.MapS.find_2 Hopt_a); intros Hopt_a'.
    apply Sys.MapS.MapsTo_1 with (y:=a) in Hopt_a'; auto.
    apply Sys.MapS.find_2 in Hopt_a.
    
    (* instantiate equiv obj_a' ... in send ixi_list def. *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
        _ _ Hsend_i
        _ _ Hopt_a'
        _ (Ref.eq_refl a)) as [tuple_a' HexOptA];
      destruct_tuple tuple_a' obj_a' lbl_a' type_a' sched_a'; simpl in *;
      simpl in HexOptA; destruct HexOptA as [HexOptA HexOptA_Map];
        destruct_tuple HexOptA HexOptA1 HexOptA2 HexOptA3 HexOptA4.
    
    (* convert MapsTo to Find in HexOptA_Map for rewriting *)
    apply Sys.MapS.find_1 in HexOptA_Map.

    (* convert HexOptA_Map for rewriting into Hopt 6 *)
    unfold SC.getCap in HexOptA_Map;
    unfold SC.getObj in HexOptA_Map;
    unfold SC.getObjTuple in HexOptA_Map;
    repeat progress (unfold Sys.P.t in HexOptA_Map; unfold Sys.P.t in Hopt6).
    rewrite HexOptA_Map in Hopt6; simpl in Hopt6.
    (* reduce Hopt6 to MapsTo *)
    unfold OC.getCap in Hopt6; apply Obj.MapS.find_2 in Hopt6.

    (* generate t_cap' [=] t_cap in obj_a *)
    apply Obj.eq_sym in HexOptA1;
      destruct (Obj_MapEquiv.exists_mapsTo_eq
        _ _ HexOptA1
        _ _ Hopt6
        _ (Ind.eq_refl _)) as [t_cap' HexOptCap];
      destruct HexOptCap as [HexOptCapEq HexOptCapMap].
    
    (* finish with proof to self *)

    eapply add_dirAcc_self_Subset;
      [apply Hdiracc 
        | apply H0 
        | apply Hopt_a
        | apply HexOptCapMap
        | apply Cap.eq_sym; apply HexOptCapEq
        | apply HsendEq].
  Qed.

  Theorem dirAcc_send_other: forall s ag,
    dirAcc_spec s ag ->
    forall a t ixi_list opt_i ag', 
      dirAcc_spec (Sem.do_send a t ixi_list opt_i s) ag' ->
      ~ (option_map1 (fun cap => Ref.eq a (Cap.target cap)) False (SC.getCap t a s)) ->
      AG.Subset ag' (ag_add_caps_send a t ixi_list s ag).
  Proof.
    (* we can't introduce ag', or we won't get a correct induction tactic *)
    intros s ag H a t ixi_list opt_i.
    (* first, by cases on satisfying the prereq *)
    case (SemDefns.send_preReq_dec a t s); intros Hpre;
      [ generalize (Sem.send_valid _ _ ixi_list opt_i _ Hpre) 
        | generalize (Sem.send_invalid _ _ ixi_list opt_i _ Hpre)]; intros Heq;
      [|intros; assert (AG.eq ag' ag); eauto; eapply dirAcc_spec_eq; eauto].
    (* case where preReq is satisfied *)
    (* unfold preReq *)
    unfold SemDefns.send_preReq in Hpre; destruct Hpre as [Hpre HhasRight]; 
      unfold_preReq Hpre Halive HtargetAlive HisActive. 
    (* simplify Halive by cases on SC.getObjLabel a s *)
    (* contradiction in the None case *)
    unfold SC.getLabel in *.
    case (option_sumbool (SC.getObjTuple a s)); intros Hopt2;[|destruct Hopt2 as [pair Hopt2]];
      rewrite Hopt2 in Halive; 
        [contradiction| destruct_tuple pair actor actor_lbl actor_type actor_sched; simpl in Halive].
    (* unfold Heq.*)
    unfold SC.copyCapList in Heq; unfold SC.copyCap in Heq.
    (* unfold Goal *)
    unfold ag_add_caps_send; unfold ag_add_caps_reply; unfold ag_add_caps_by_index_pair_list; 
      unfold ag_add_cap_by_indirect_index; unfold ag_add_cap_by_obj_index;
        unfold ag_add_cap_valid; unfold ag_add_cap_valid_std; unfold ag_add_cap_valid_allocate;
    (* simplify HtargetAlive *)
    unfold SemDefns.target_is_alive in HtargetAlive.
    (* we know that (getCap t a s) exists by option_hasRight, so intro case and contradict *)
    (* apply in Heq and simplify in goal *)
    case (option_sumbool (SC.getCap t a s)); intros Hopt3;[|destruct Hopt3 as [invoked_cap Hopt3]];
      rewrite Hopt3 in Heq; simpl in Heq; rewrite Hopt3 in HtargetAlive; simpl in HtargetAlive;
        [ contradiction | rewrite Hopt3; simpl ].
    (* we know that (getObjTuple (target invoked_cap) s) exists by is_alive *)
    case (option_sumbool (SC.getObjTuple (Cap.target invoked_cap) s)); intros Hopt4;[|destruct Hopt4 as [invoked_cap_tuple Hopt4]];
      [unfold SC.is_alive in HtargetAlive;
        unfold SC.is_label in HtargetAlive;
        unfold SC.getLabel in HtargetAlive;
          rewrite Hopt4 in HtargetAlive;
            simpl in HtargetAlive;
              contradiction|].

    (* we know is_alive (target (mkCap a (singleton send))) s, 
       it was an assumption, now unfolded and blown apart.  assert it. *)
    assert (SC.is_alive (Cap.target
                 (Cap.mkCap a
                    (ARSet.singleton AccessRights.tx))) s) as HisAlive.
    unfold SC.is_alive.
    eapply SC.isLabel_eq;
      [apply Ref.eq_sym; eapply CC.mkCap_target
        | eauto
        | apply Sys.eq_refl
        | unfold SC.is_label; unfold SC.getLabel; rewrite Hopt2; simpl; try apply ObjectLabel.eq_refl; auto].
    (* use the above assertion to rewrite true_bool_of_sumbool *)
    unfold true_bool_of_sumbool;
      rewrite (proof_r_true_bool_of_sumbool _ (SC.is_alive_dec _ _) HisAlive);
        rewrite andb_true_r;
          simpl;
            clear HisAlive.
    (* we also know that the invoked cap is alive *)
    rewrite (proof_r_true_bool_of_sumbool _ (SC.is_alive_dec _ _) HtargetAlive); simpl.

    (* No longer needed... 
    (* we know is_alive a s, it was an assumption, now unfolded and blown apart.  assert it. *)
    assert (SC.is_alive a s) as HisAlive.
    unfold SC.is_alive; unfold SC.is_label; rewrite Hopt2; simpl; try apply ObjectLabel.eq_refl; auto.

    (* use the above assertion to rewrite true_bool_of_sumbool *)
    unfold true_bool_of_sumbool;
      rewrite (proof_r_true_bool_of_sumbool _ (SC.is_alive_dec _ _) HisAlive);
        simpl;
          clear HisAlive. *)

    (* now simplify htargetAlive *)
    destruct_tuple invoked_cap_tuple invoked_cap_target invoked_cap_lbl invoked_cap_type invoked_cap_sched.
    unfold SC.is_alive in HtargetAlive;
      unfold SC.is_label in HtargetAlive;
      unfold SC.getLabel in HtargetAlive;
        rewrite Hopt4 in HtargetAlive;
          simpl in HtargetAlive.

    (*****  AAAAAAAAAUUUUUUUGGGGGGHHHHHH!!!!!!! ******)
    (* something is very very wrong here.  look at the goal at this point *)
    (* it appears that we are copying (fst ixi) (Cap.target invoked_cap) when we should be copying
       (fst ixi) a !!!*)
    (* no wonder the strategy below isnt working. *)
    (* where is the definition getting tripped up? *)

    (* we may have to induct over ixi_list here.  The reply cap happens in the base case. *)
    induction ixi_list; simpl; simpl in Heq.

    (*okay, to reduce Heq, we have two cases, either we add a reply or not. *)
    intros; destruct opt_i as[i|]; simpl in Heq.

    (* case where things are not equal *)
    (* simplify Heq *)
    unfold SC.addCap in Heq.
    unfold SC.getObj in Heq.
    unfold SC.updateObj in Heq.
    unfold OC.addCap in Heq.
    unfold SC.update_pair_object in Heq.
    rewrite Hopt4 in Heq.
    simpl in Heq.
    unfold SC.addObjTuple in Heq.
    (* alright.  We have reduced Heq to its minimal form.
       We should go back and prove something about ag_add_cap and system state adds. *)
    apply dirAcc_addCap_subset with (index := i) (obj := invoked_cap_target) (ag:=ag)
      (obj_lbl := invoked_cap_lbl) (obj_type := invoked_cap_type) (obj_sched := invoked_cap_sched) (s := s); auto;
        try apply (dirAcc_spec_iff Heq (AG.eq_refl ag')); auto;
          try apply Sys.MapS.find_2; auto.
    (* case where things are equal *)
    assert (AG.eq ag ag') as HeqAG;
      [eapply dirAcc_spec_eq; apply Sys.eq_sym in Heq; try apply Heq; auto
        | apply ag_eq_Equal in HeqAG; apply AG.eq_sym in HeqAG; auto].
    (* induction case *)
    (* this looks better *)
    intros.
    (* destruct the ixi pair *)
    destruct a0 as [i_src i_dst]; simpl in *.
    generalize (Sem.send_valid a t ixi_list opt_i s); intros IHsend.
    (* prereq is in too many pieces *)
    assert (SemDefns.send_preReq a t s) as HpreReq.
    unfold SemDefns.send_preReq.
    split; auto.
    unfold SemDefns.preReq;
    unfold SemDefns.preReqCommon;
    unfold SemDefns.target_is_alive;
    unfold SC.is_alive;
    unfold SC.is_label;
    unfold SC.getLabel;
    unfold SC.is_type.
    rewrite Hopt2; rewrite Hopt3; simpl.
    rewrite Hopt4; simpl.
    split; auto. 
    (* apply HpreReq in IHSend *)
    generalize (IHsend HpreReq); clear IHsend; intros IHsend.
    rewrite Hopt3 in IHsend; simpl in IHsend.
    generalize (IHixi_list IHsend); clear IHsend; clear IHixi_list; intros IH.
    (* okay, we have an IH that will let us recurse, but only if we can instantiate it.
       we have not yet proved that dirAcc_spec is decidable, nor that one always exists.
       If we can show these, thein we can instantiate the IH, and recurse in both cases.*)
    generalize (exists_dirAcc_spec (Sem.do_send a t ixi_list opt_i s)); intros Hex.
    destruct Hex as [ag_spec Hdiracc];
      generalize (IH ag_spec Hdiracc H1); clear IH; intros IH.
    (* generalize the inductive hypothesis send *)
    generalize (Sem.send_valid a t ixi_list opt_i s HpreReq); intros Hsend_i; rewrite Hopt3 in Hsend_i;
      simpl in Hsend_i; unfold SC.copyCapList in Hsend_i; unfold SC.copyCap in Hsend_i.

    (* destruct the cases of getCap i_src a ..., show Subset ag' (dirAcc send) *)
    case (option_sumbool 
      (SC.getCap i_src a
        (fold_right
          (fun (ixi : Ind.t * Ind.t) (s : Sys.t) =>
            option_map1
            (fun cap : Cap.t =>
                       SC.addCap (snd ixi) cap
                         (Cap.target invoked_cap) s) s
                      (SC.getCap (fst ixi) a s))
                   (option_map1
                      (fun i : Ind.t =>
                       SC.addCap i
                         (Cap.mkCap a
                            (ARSet.singleton
                               AccessRights.tx))
                         (Cap.target invoked_cap) s) s opt_i) ixi_list))
);
    intros Hopt6; [|destruct Hopt6 as [t_cap Hopt6]]; rewrite Hopt6 in *; simpl in *.
    (* None (...) *)
    (* show that all these are equal, and produce AG.Equal ag' ag_spec *)
    assert (Sys.eq (Sem.do_send a t ((i_src, i_dst) :: ixi_list) opt_i s) (Sem.do_send a t ixi_list opt_i s)) as HsendEq;
      [apply Sys.eq_sym in Hsend_i; eapply Sys.eq_trans; [apply Heq| apply Hsend_i]|].
    (* show ag' [=] ag_spec *)
    assert (AG.eq ag' ag_spec) as HagEq;[
      eapply dirAcc_spec_eq; try apply HsendEq; auto|
        generalize (ag_eq_Equal ag' ag_spec); intros HagEqual; destruct HagEqual as [HagEqual _];
          apply HagEqual in HagEq].
    (* cases on getCap i_src a s  *)
    Ltac solve_send_eq ag_spec IH HagEq element := try apply ag_add_cap_nondecr;
      apply AGFacts.Subset_trans with ag_spec; try apply IH;
        unfold AG.Equal in HagEq; unfold AG.Subset; intro element; eapply (HagEq element).
    case (option_sumbool (SC.getCap i_src a s)); intros Hopt5; [|destruct Hopt5 as [i_cap Hopt5]];
      rewrite Hopt5 in *; simpl in *; try solve [solve_send_eq ag_spec IH HagEq element];
        case (SC.is_alive_dec (Cap.target i_cap) s); intros Hopt7; simpl in *;
          solve_send_eq ag_spec IH HagEq element.
    (* Some ... *)
    (* in the none case of Hopt6, we simply performed cases on (getCap i_src a s). 
       However, in the Some case, we must know something more.  We must know that t_cap is i_cap, since those
       mappings were not updated.  This probably requires a separate theorem.
       Outline: first remove the option_map1 base case as s since it is compatable.
       Next, induct that addcap (snd ixi) ... doesn't modify a.
       Shoot!  What if a is sending to a?  This could overwrite caps. 
       Okay, so we really have two cases.  one where we are sending to a, and one where we are not.
       If we are sending to a, then the entire scenario is simple subset, as caps aren't really going anywhere.
       If we are not sending to a, then we can induct getCap i_src a ... over addCap (snd ixi) cap dest and prove that getCap is 
       unchanged.
       Since getCap is unchanged, it is the same case in the goal.  This should give us subset eventually.*)

    assert (SC.getCap i_src a
            (option_map1
               (fun i : Ind.t =>
                SC.addCap i
                  (Cap.mkCap a
                     (ARSet.singleton
                        AccessRights.tx)) (Cap.target invoked_cap) s)
               s opt_i) = OC.getCap i_src actor ) as Hassert;[
    unfold SC.addCap;
    unfold SC.updateObj;
    unfold SC.getCap;
    unfold SC.getObj;
    unfold OC.addCap; unfold SC.addObjTuple;

    destruct opt_i as [i_reply|]; simpl;
      [try rewrite Hopt4; simpl;
        unfold SC.getObjTuple;
          rewrite Sys_Facts.add_neq_o; auto;
            unfold SC.getObjTuple in Hopt2 |];

    (* both cases identical *)
    unfold Sys.P.t in *;
    rewrite Hopt2; simpl; auto|].



    generalize (SC.getCap_copyCapList_map_eq (option_map1
                  (fun i : Ind.t =>
                   SC.addCap i
                     (Cap.mkCap a
                        (ARSet.singleton
                           AccessRights.tx)) (Cap.target invoked_cap)
                     s) s opt_i) _ _ _ ixi_list i_src (OC.getCap i_src actor) (Some t_cap)
    (Ref.eq_refl a) H1 Hassert Hopt6); intros Hcopy;
    unfold SC.copyCapList in Hcopy;
    unfold SC.copyCap in Hcopy;
    unfold option_map_eq in Hcopy;
    unfold option_map2 in Hcopy.





    case (option_sumbool (SC.getCap i_src a s)); intros Hopt5; [|destruct Hopt5 as [i_cap Hopt5]];
      rewrite Hopt5 in *; simpl in *;
    unfold SC.getCap in Hopt5; unfold SC.getObj in Hopt5; rewrite Hopt2 in *; simpl in *.
    
    (* we have ambiguous paths here, try to resolve *)
    rewrite Hopt5 in *. try contradiction.

    (*  We now have:
        Hcopy : Cap.eq i_cap t_cap
        Hopt5 : SC.OC.getCap i_src actor = Some i_cap *)

    case (SC.is_alive_dec (Cap.target i_cap) s); intros Hopt7; simpl in *.


    assert (Sys.eq (Sem.do_send a t ((i_src, i_dst) :: ixi_list) opt_i s) 
      (SC.addCap i_dst t_cap (Cap.target invoked_cap) (Sem.do_send a t ixi_list opt_i s))) as HsendEq.
    eapply Sys.eq_trans; [apply Heq | apply SC.addCap_eq; try apply Ref.eq_refl; auto]. 
    (*eapply Sys.eq_trans; [apply Heq| apply SC.addCap_eq; auto; apply Sys.eq_sym; auto].*)

    (* IH is ag_spec [<=] ag_spec_fold
       Goal is ag' [<=] ag_add_cap (target invoked_cap) i_cap ag_spec_fold.
       By definition dirAcc_spec ag_spec (do_send ixi_list ...) and
       dirAcc_spec ag' (do_send ((i_src, i_dst) :: ixi_list) ...).

       We should be able to apply dirAcc_addCap_subset.
       ag' := ag'
       ref := (target invoked_cap)
       cap := i_cap
       ag := ag_spec_fold_defn

       perhaps by (do_send ((i_src, i_dst) :: ixi_list) ...) [=] (do_send ixi_list ...) we may
       reduce (do_send ((i_src, i_dst) :: ixi_list) ...) to 
       (add ref (add index i_cap obj, obj_lbl, obj_type, obj_sched) (do_send ixi_list ...))
       with MapsTo ref (obj, obj_lbl, obj_type, obj_sched) (do_send ixi_list ...)
       however, that leaves ag := ag_spec, not ag_spec_fold.

       We probably need to generalize dirAcc_addCap_subset as:

       Theorem dirAcc_addCap_subset : forall ref index cap obj obj_lbl obj_type obj_sched s ag ag2 ag',
         Sys.MapS.MapsTo ref (obj, obj_lbl, obj_type, obj_sched) s ->
         dirAcc_spec s ag ->
         dirAcc_spec 
         (Sys.MapS.add ref
           (Obj.MapS.add index cap obj, obj_lbl, obj_type, obj_sched)
           s) ag' ->
         AG.Subset ag ag2 ->
         AG.Subset ag' (ag_add_cap ref cap ag2).
       
       Before attempting, check that the current theorem reduces to this goal.
       We may be able to discharge this theorem without altering dirAcc_addCap_subset.
       We may be able to instantiate and use add over subset rules to generalize.







       1. By subset_add(?) on IH, we know:
       ag_add_cap (target invoked_cap) i_cap ag_spec [<=] ag_add_cap (target invoked_cap) i_cap ag_spec_fold.
       2. by subset_equal, goal becomes
       ag' [=] ag_add_cap (target invoked_cap) i_cap ag_spec
       3. we know:
       (do_send ((i_src, i_dst) :: ixi_list) ...) [=] (do_send ixi_list ...)
       4. Therefore, we should be able to show theorem 2.
       (we may not require equality in step 2, only subset)
       this may actually require generalizing diracc_addcap_subset.
       
*)

    unfold SC.addCap in HsendEq.
    unfold SC.updateObj in HsendEq.
    unfold SC.addObjTuple in HsendEq.
    unfold SC.getObj in HsendEq.

    case (option_sumbool (SC.getObjTuple (Cap.target invoked_cap) (Sem.do_send a t ixi_list opt_i s))); intros Hopt8;
    [|destruct Hopt8 as [tuple_8 Hopt8]; destruct_tuple tuple_8 obj_8 lbl_8 type_8 sched_8];
    rewrite Hopt8 in *; simpl in *.

    (* technically a contradiciton case, but it's easier to just instantiate from subset *)
    eapply AGFacts.Subset_trans with ag_spec; auto.

    (*copied from above, may wish to ltac *)
    (* show ag' [=] ag_spec *)
    assert (AG.eq ag' ag_spec) as HagEq;[
      eapply dirAcc_spec_eq; try apply HsendEq; auto|
        generalize (ag_eq_Equal ag' ag_spec); intros HagEqual; destruct HagEqual as [HagEqual _];
          apply HagEqual in HagEq].
    (*solve *)
    intro edge; eapply (HagEq edge); auto.

    (* case where things are intereting *)
    unfold OC.addCap in HsendEq.
    unfold SC.getObjTuple in Hopt8.
    apply Sys.MapS.find_2 in Hopt8.

    (* apply diracc_addcap_subset, reduce to add over send ixi_list *)
    eapply dirAcc_addCap_subset with (ag:=ag_spec); [ apply Hopt8 | apply Hdiracc | | apply IH ].
    (* apply dirAcc_spec_iff to get close to HsendEq *)
    eapply dirAcc_spec_iff; [| apply AG.eq_refl| apply H0].
    (* apply eq_trans and HsendEq for nearly eq types except for i_cap *)
    eapply Sys.eq_trans; [|apply Sys.eq_sym; apply HsendEq].
    (* reduce to i_cap [=] t_cap *)
    eapply SC.addObjTuple_eq; eauto; try apply Sys.eq_refl.
    apply Ref.eq_refl.
    unfold Sys.P.eq; simpl.
    repeat progress (try split; eauto).
    eapply OC.addCap_eq; auto; try apply Obj.eq_refl.
    rewrite Hopt5 in Hcopy. auto.

    (* case where target i_cap is not alive *)


    assert (Sys.eq (Sem.do_send a t ((i_src, i_dst) :: ixi_list) opt_i s) 
      (SC.addCap i_dst t_cap (Cap.target invoked_cap) (Sem.do_send a t ixi_list opt_i s))) as HsendEq;
    [eapply Sys.eq_trans; [apply Heq | apply SC.addCap_eq; try apply Ref.eq_refl; auto]|].
    unfold SC.addCap in HsendEq.
    unfold SC.updateObj in HsendEq.
    unfold SC.addObjTuple in HsendEq.
    unfold SC.getObj in HsendEq.

case (option_sumbool (SC.getObjTuple (Cap.target invoked_cap) (Sem.do_send a t ixi_list opt_i s))); intros Hopt8;
    [|destruct Hopt8 as [tuple_8 Hopt8]; destruct_tuple tuple_8 obj_8 lbl_8 type_8 sched_8];
    rewrite Hopt8 in *; simpl in *.

    (* technically a contradiciton case, but it's easier to just instantiate from subset *)
    eapply AGFacts.Subset_trans with ag_spec; auto.

    (*copied from above, may wish to ltac *)
    (* show ag' [=] ag_spec *)
    assert (AG.eq ag' ag_spec) as HagEq;[
      eapply dirAcc_spec_eq; try apply HsendEq; auto|
        generalize (ag_eq_Equal ag' ag_spec); intros HagEqual; destruct HagEqual as [HagEqual _];
          apply HagEqual in HagEq].
    (*solve *)
    intro edge; eapply (HagEq edge); auto.

    (* case where things are interesting *)
    unfold OC.addCap in HsendEq.
    unfold SC.getObjTuple in Hopt8.
    apply Sys.MapS.find_2 in Hopt8.

    apply AGFacts.Subset_trans with ag_spec; auto.
    eapply dirAcc_addCap_notAlive_2;
    [ apply Hopt8
      | apply Hdiracc
      | 
      | eapply dirAcc_spec_iff; [| apply AG.eq_refl| apply H0]; apply Sys.eq_sym in HsendEq; apply HsendEq].
        
(* ~ SC.is_alive (Cap.target i_cap) s ->
   ~ SC.is_alive (Cap.target t_cap) (Sem.do_send a t ixi_list opt_i s) *)

  intro Hnot.
  apply Hopt7.
  unfold SC.is_alive. unfold SC.is_alive in Hnot.
  eapply (SC.isLabel_eq _ _ _ _ _ _ (Ref.eq_refl _ ) (ObjectLabel.eq_refl _) Hsend_i) in Hnot.

 
  eapply SC.is_label_iff_getLabel.
  eapply SC.is_label_iff_getLabel in Hnot.



  eapply SC.getLabel_copyCapList_map_1 with (opt_i_lbl:= Some ObjectLabels.alive) in Hnot; 
    [| simpl; auto; apply ObjectLabel.eq_refl].
 
  unfold SC.addCap in Hnot.
  unfold SC.updateObj in Hnot.
  unfold SC.getObj in Hnot.
  unfold SC.addObjTuple in Hnot.
  rewrite Hopt4 in Hnot; simpl in Hnot.
  rewrite Hopt5 in Hcopy.

  generalize (SC.getLabel_eq _ _ _ _ (Cap.target_eq _ _ Hcopy) (Sys.eq_refl s)); intros Heq1.

  (* cases on opt_i *)
  destruct opt_i as [i|]; simpl in *.
  unfold SC.getLabel in Hnot. 
  unfold SC.getObjTuple in Hnot.

  case (Ref.eq_dec (Cap.target t_cap) (Cap.target invoked_cap)); intros Hopt9.
  (* (target t_cap) [=] (target invoked_cap) *)
  (* (target invoked_cap) is alive in s, so must be (target i_cap) *)
  unfold SC.getLabel in *.
  unfold SC.getObjTuple in *.
  rewrite Sys_Facts.find_o with (y:=(Cap.target t_cap))in Hopt4; auto.
  rewrite Sys_Facts.find_o with (y:= (Cap.target t_cap)); try apply Cap.target_eq; auto.
  rewrite Hopt4; simpl; rewrite HtargetAlive; auto.

  (* (target t_cap) [<>] (target invoked_cap) *)
  rewrite Sys_Facts.add_neq_o in Hnot; simpl in Hnot; auto.
  unfold SC.getLabel in *.
  unfold SC.getObjTuple in *.
  unfold Sys.P.t in *.
  rewrite Hnot in Heq1.
  case (option_sumbool (Sys.MapS.find (Cap.target i_cap) s)); intros Hopt10;
    [|destruct Hopt10 as [tuple Hopt10]; destruct_tuple tuple t_obj t_lbl t_type t_sched];
    rewrite Hopt10 in *; simpl in *; try contradiction; try rewrite Heq1; auto.

  (* no reply *)
  unfold SC.getLabel in *.
  unfold SC.getObjTuple in *.
  rewrite Hnot in Heq1.
  case (option_sumbool (Sys.MapS.find (Cap.target i_cap) s)); intros Hopt10;
    [|destruct Hopt10 as [tuple Hopt10]; destruct_tuple tuple t_obj t_lbl t_type t_sched];
    rewrite Hopt10 in *; simpl in *; try contradiction; try rewrite Heq1; auto.
Qed.

(* Read:
   If ag' conservatively approximates (dirAcc s), then
   (Fa ag') conservatively approximates (dirAcc (Fs s)). *)
Definition dirAcc_approx Fs Fa := forall s ag ag' ag2, 
  dirAcc_spec s ag -> dirAcc_spec (Fs s) ag2 -> AG.Subset ag ag' -> AG.Subset ag2 (Fa ag').

Theorem dirAcc_approx_comp: forall Fs Fa Fs' Fa',
  dirAcc_approx Fs Fa -> dirAcc_approx Fs' Fa' -> dirAcc_approx (fun s => Fs' (Fs s)) (fun a => Fa' (Fa a)).  
Proof.
  unfold dirAcc_approx; intros.
  destruct (exists_dirAcc_spec (Fs s)) as [Fs_s HFs_s].
  eapply H0; [apply HFs_s | auto | eapply H; first [apply H1 | auto]].
Qed.

Theorem dirAcc_addCap_subset_approx_equiv: forall ref index cap , 
  dirAcc_approx 
  (fun s => 
    match Sys.MapS.find ref s with
      | Some (obj, obj_lbl, obj_type, obj_sched) =>
        (Sys.MapS.add ref (Obj.MapS.add index cap obj, obj_lbl, obj_type, obj_sched) s) 
      | None => s
    end)
  (fun ag => ag_add_cap ref cap ag).
Proof.
  unfold dirAcc_approx.
  intros.
  case (Sys_Facts.In_dec s ref); intros Hcase;
    [unfold Sys.MapS.In in Hcase; destruct Hcase as [p Hcase]; apply Sys_Facts.find_mapsto_iff in Hcase
      | apply Sys_Facts.not_find_in_iff in Hcase];
  rewrite Hcase in *; simpl in *.
   
  apply Sys_Facts.find_mapsto_iff in Hcase.
  destruct_tuple p obj obj_lbl obj_type obj_sched.
  apply dirAcc_addCap_subset with (s:=s) (ag:=ag) (index:=index)
    (obj:=obj) (obj_lbl:=obj_lbl) (obj_type:=obj_type) (obj_sched:=obj_sched); assumption.

  apply ag_add_cap_nondecr.
  eapply AGProps.subset_trans with ag; auto.
  apply AGProps.subset_equal.
  generalize (dirAcc_spec_eq _ _ _ _ (Sys.eq_refl s) H H0); auto.
Qed.






(* we need some rmCapsByTarget theorems before we can prove this *)
(* recommend an 
   SC.getObjTuple a s = (obj, lbl, typ, sch) -> 
   SC.getObjTuple a (SC.rmCapsByTarget n s) = ((OC.rmCapsByTarget n obj), lbl, typ, sch) *)



  Theorem rmCapsByTarget_dirAcc_subset: forall n s s' ag,
    SC.rmCapsByTarget_spec n s s' -> dirAcc_spec s ag -> 
    forall ag', dirAcc_spec s' ag' -> AG.Subset ag' ag.
  Proof.
    intros.
    unfold SC.rmCapsByTarget_spec in *.
    (* setup the edge property for subset *)
    unfold AG.Subset.
    intros edge; intros Hin.
    (* instantiate dirAcc_spec as both goal and hypothesis *)
    eapply H1 in Hin; clear H1.
    eapply H0; clear H0.
    (* destruct the hypothesis diracc_spec *)
    destruct_dirAcc Hin Hag'_s' Hag'_HeqS Hag'_src_ref Hag'_src Hag'_srcLbl Hag'_srcType Hag'_srcSched Hag'_mapS 
    Hag'_src' Hag'_srcL'bl Hag'_srcType' Hag'_srcSched' Hag'_HeqP Hag'_Halive Hag'_ind Hag'_cap Hag'_HmapSrc'
    Hag'_cap_obj Hag'_cap_lbl Hag'_cap_type Hag'_cap_sched Hag'_mapScap 
    Hag'_cap_obj' Hag'_cap_lbl' Hag'_cap_type' Hag'_cap_sched' 
    Hag'_eqPcap Hag'_aliveCap Hag'_rgt Hag'_inR Hag'_eqEdge.
    (* clean tuples *)
    destruct Hag'_HeqP as [[[Hag'_eqSrc Hag'_eqLbl] Hag'_eqType] Hag'_eqSched]; simpl in *.
    destruct Hag'_eqPcap as [[[Hag'_eqObj Hag'_eqObjLbl] Hag'_eqObjType] Hag'_eqObjSched]; simpl in *.
    (* split rmCapsByTarget *)
    destruct H as [_ [H' [_ H]]].
    (* specialize and split rmCapsByTarget_spec over Hag'_cap *)
    generalize (H Hag'_src_ref Hag'_ind Hag'_cap Hag'_srcLbl Hag'_srcType Hag'_srcSched); intros [Hrm _].
    (* assert the given of Hrm *)
    Require Import ObjectSchedules.
    Require Import ObjectTypes.
    assert (exists o' : Obj.MapS.t Cap.t,
           exists l' : ObjectLabel.t,
             exists t' : ObjectType.t,
               exists d' : ObjectSchedule.t,
                 exists c' : Cap.t,
                   ObjectLabel.eq Hag'_srcLbl l' /\
                   ObjectType.eq Hag'_srcType t' /\
                   ObjectSchedule.eq Hag'_srcSched d' /\
                   Cap.eq Hag'_cap c' /\
                   Sys.MapS.MapsTo Hag'_src_ref (o', l', t', d') s' /\
                   Obj.MapS.MapsTo Hag'_ind c' o') as Hexists;
    [clear Hrm | apply Hrm in Hexists; clear Hrm].
    (* build equuivalent mappings in new diracc *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ (Sys.eq_sym Hag'_HeqS)
      _ _ Hag'_mapS
      _ (Ref.eq_refl Hag'_src_ref)) as [exP Hex].
    destruct_tuple exP ex_cap'_obj ex_cap'_lbl ex_cap'_type ex_cap'_sched;
      simpl in Hex; destruct Hex as [Hex HexMap];
        destruct_tuple Hex Hex1 Hex2 Hex3 Hex4.
    destruct (Obj_MapEquiv.exists_mapsTo_eq
      _ _ (Obj.eq_sym Hag'_eqSrc)
      _ _ Hag'_HmapSrc'
      _ (Ind.eq_refl Hag'_ind)) as [ex_cap [HCeq HCMap]].
    destruct (Obj_MapEquiv.exists_mapsTo_eq
      _ _ Hex1
      _ _ HCMap
      _ (Ind.eq_refl Hag'_ind)) as [ex_cap' [HCeq' HCMap']].
    (* rewrite and introduce *)
    rewrite Hex2; rewrite Hex3; rewrite Hex4;
      apply ex_intro with ex_cap'_obj; apply ex_intro with ex_cap'_lbl; apply ex_intro with ex_cap'_type;
            apply ex_intro with ex_cap'_sched;  apply ex_intro with ex_cap';
              repeat progress (split; auto).
    (* solve for equiv caps *)
    eapply Cap.eq_trans; [apply HCeq | auto].
    (* destruct result of assertion *)
    destruct Hexists as [o' [l' [t' [d' [c' [HeqL' [HeqT' [HeqD' [HeqC' [HmapS [HmapO' Hneq]]]]]]]]]]].

    generalize (H' (Cap.target Hag'_cap)  Hag'_cap_lbl Hag'_cap_type Hag'_cap_sched);
      intros [Hrm _].
    assert (exists o' : Obj.MapS.t Cap.t,
           exists l' : ObjectLabels.ObjectLabel.t,
             exists t' : ObjectTypes.ObjectType.t,
               exists d' : ObjectSchedules.ObjectSchedule.t,
                 ObjectLabels.ObjectLabel.eq Hag'_cap_lbl l' /\
                 ObjectTypes.ObjectType.eq Hag'_cap_type t' /\
                 ObjectSchedules.ObjectSchedule.eq Hag'_cap_sched d' /\
                 Sys.MapS.MapsTo (Cap.target Hag'_cap)
                   (o', l', t', d') s') as Hexists;
    [clear Hrm | apply Hrm in Hexists; clear Hrm].
    (* build equuivalent mappings in new diracc *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ (Sys.eq_sym Hag'_HeqS)
      _ _ Hag'_mapScap
      _ (Ref.eq_refl(Cap.target Hag'_cap))) as [exP Hex].
    destruct_tuple exP ex_cap'_obj ex_cap'_lbl ex_cap'_type ex_cap'_sched;
      simpl in Hex; destruct Hex as [Hex HexMap];
        destruct_tuple Hex Hex1 Hex2 Hex3 Hex4.
    (* rewrite and introduce *)
    rewrite Hex2; rewrite Hex3; rewrite Hex4;
      apply ex_intro with ex_cap'_obj; apply ex_intro with ex_cap'_lbl; apply ex_intro with ex_cap'_type;
            apply ex_intro with ex_cap'_sched;
              repeat progress (split; auto).
    (* destruct result of assertion *)
    destruct Hexists as [o2' [l2' [t2' [d2' [HeqL2' [HeqT2' [HeqD2' HmapS2]]]]]]].

    (* INSTANTIATE! *)
    apply_ex_intro_dirAcc s s Hag'_src_ref o' Hag'_srcLbl Hag'_srcType Hag'_srcSched 
    o' Hag'_srcLbl Hag'_srcType Hag'_srcSched Hag'_ind c'
    o2' l2' t2' d2' o2' l2' t2' d2' Hag'_rgt; 
    try apply Sys.eq_refl; eauto.
    (* clause 1 *)
    unfold ObjectLabel.eq in *;
    unfold ObjectType.eq in *;
    unfold ObjectSchedule.eq in *;
    rewrite HeqL'; rewrite HeqT'; rewrite HeqD'; eauto.
    (*clause 2 *)
    repeat progress (split; simpl; eauto; try apply Obj.eq_refl).
    (* clause 3 *)
    rewrite <- Hag'_Halive in Hag'_eqLbl; rewrite Hag'_eqLbl; apply ObjectLabel.eq_refl.
    (*clause 4*)
    eapply (Sys_Facts.MapsTo_iff _ _ (Cap.target_eq _ _ HeqC')); auto.
    (* clause 5 *)
    repeat progress (split; simpl; eauto; try apply Obj.eq_refl).
    (* clause 6 *)
    rewrite <- HeqL2'; rewrite Hag'_eqObjLbl; rewrite <- Hag'_aliveCap; apply ObjectLabel.eq_refl.
    (* clause 7 *)
    eapply (Cap.rights_eq _ _ HeqC'); auto.
    (* clause 8 *)
    eapply Edge.eq_trans; [|eapply Hag'_eqEdge];
    eapply Edges.edge_equal; eauto;
    try apply Cap.target_eq; eauto; try apply Ref.eq_refl;try apply AccessRight.eq_refl.
  Qed.




  Theorem dirAcc_approx_rmCapsByTarget: forall n,
    dirAcc_approx (fun s => SC.rmCapsByTarget n s) (fun ag => ag).
  Proof.
    unfold dirAcc_approx; intros.
    apply AGProps.subset_trans with ag; auto. clear H1.
    (* This is essentially monotonicity of rmCapsByTarget, when ag [=] ag' *)
    eapply rmCapsByTarget_dirAcc_subset with (n:=n); eauto.
    (*  apply SC.rmCapsByTarget_spec_rmCapsByTarget. *)
  Qed.

    Theorem dirAcc_approx_set_alive_empty: forall n l t d,
      dirAcc_approx 
      (fun s => 
        if true_bool_of_sumbool (SC.safe_to_make_alive_dec n s) 
          then (SC.set_alive n (Sys.MapS.add n (Obj.MapS.empty Cap.t, l, t, d) s))
          else s)
      (fun ag => ag).
    Proof.
      unfold dirAcc_approx; unfold AG.Subset; intros n l t d s ag ag' ag2 H H0 H1 edge H2.
      case (SC.safe_to_make_alive_dec n s); intros Hsafe;
        unfold true_bool_of_sumbool in H0; 
          [rewrite (proof_r_true_bool_of_sumbool _ (SC.safe_to_make_alive_dec n s) Hsafe) in H0
            |rewrite (proof_l_true_bool_of_sumbool _ (SC.safe_to_make_alive_dec n s) Hsafe) in H0 ]; eauto.
    (* case true *)
    unfold SC.safe_to_make_alive in *.
    eapply H1; clear H1.
    generalize (H edge); clear H; intros [H _];
    generalize (H0 edge); clear H0; intros [_ H0].
    eapply H; clear H.
    apply H0 in H2; clear H0.
    destruct_dirAcc H2 Hag'_s' Hag'_HeqS Hag'_src_ref Hag'_src Hag'_srcLbl Hag'_srcType Hag'_srcSched Hag'_mapS 
    Hag'_src' Hag'_srcL'bl Hag'_srcType' Hag'_srcSched' Hag'_HeqP Hag'_Halive Hag'_ind Hag'_cap Hag'_HmapSrc'
    Hag'_cap_obj Hag'_cap_lbl Hag'_cap_type Hag'_cap_sched Hag'_mapScap 
    Hag'_cap_obj' Hag'_cap_lbl' Hag'_cap_type' Hag'_cap_sched' 
    Hag'_eqPcap Hag'_aliveCap Hag'_rgt Hag'_inR Hag'_eqEdge.    
    (* clean tuples *)
    destruct Hag'_HeqP as [[[Hag'_eqSrc Hag'_eqLbl] Hag'_eqType] Hag'_eqSched]; simpl in *.
    destruct Hag'_eqPcap as [[[Hag'_eqObj Hag'_eqObjLbl] Hag'_eqObjType] Hag'_eqObjSched]; simpl in *.
    (* To spell this out with abbreviation, we know that edge is in (dirAcc Hag'_s'), where Hag'_s' is
       the result of setting n to alive with an empty object.
       Our goal is to show that edge is in s.
       This is true, because the only object changed is n, and nothing targets n as we have assumed it is
       safe to allocate.
       Things we can prove:
       If n <> Hag'_src_ref, because in Hag'_s', n names an empty object.
       If n <> (target Hag'_cap), by Hsafe and prev statement.
       all other objects are unaffected, so there must be an equiv obj and state for with edge.
       *)
    (* build equuivalent mappings in new dirAcc *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ (Sys.eq_sym Hag'_HeqS)
      _ _ Hag'_mapS
      _ (Ref.eq_refl Hag'_src_ref)) as [exP Hex].
    destruct_tuple exP ex_obj ex_lbl ex_type ex_sched;
      simpl in Hex; destruct Hex as [Hex HexMap];
        destruct_tuple Hex Hex1 Hex2 Hex3 Hex4.
    destruct (Obj_MapEquiv.exists_mapsTo_eq
      _ _ (Obj.eq_sym Hag'_eqSrc)
      _ _ Hag'_HmapSrc'
      _ (Ind.eq_refl Hag'_ind)) as [ex_cap [HCeq HCMap]].
    destruct (Obj_MapEquiv.exists_mapsTo_eq
      _ _ Hex1
      _ _ HCMap
      _ (Ind.eq_refl Hag'_ind)) as [ex_cap' [HCeq' HCMap']].

    unfold SC.set_alive in HexMap; unfold SC.set_label in HexMap.
    unfold SC.addObjTuple in HexMap; unfold SC.getObjTuple in HexMap.
    rewrite Sys_Facts.add_eq_o in HexMap; eauto; simpl in *.
    eapply Sys_Facts.add_mapsto_iff in HexMap; simpl in *.
    destruct HexMap as [[Heq HexMap]|[Hneq HexMap]].
    (* case n [=] Hag'_src_ref *)
    (* contradiction: empty [=] ex_cap'obj /\  MapsTo Hag'_ind ex_cap' ex_cap'_obj*)
    inversion HexMap as [[H0 H1 H2 H3]];
      rewrite <- H0 in HCMap';
        eapply Obj_Facts.empty_mapsto_iff in HCMap'; contradiction.
    (* case n [<>] Hag'_src_ref *)
    (* simpl out the inner hexmap. *)
    eapply Sys_Facts.add_mapsto_iff in HexMap; simpl in *.
    destruct HexMap as [[Heq' HexMap]|[Hneq' HexMap]]; try contradiction ; simpl in *; clear Hneq'.
    (* we now have:
       HexMap: MapsTo Hag'_src_ref (ex_obj, ...) s
       HCMap': MapsTo Hag'_ind ex_cap' ex_obj
       ex_cap' [=] ex_cap [=] Hag'_cap  which is target.
       and ex_cap'lbl [=] Hag'_srcLbl [=] Hag'_srcL'bl [=] alive. *)

    (* build equuivalent mappings in new diracc *)
    destruct (Sys_MapEquiv.exists_mapsTo_eq
      _ _ (Sys.eq_sym Hag'_HeqS)
      _ _ Hag'_mapScap
      _ (Ref.eq_refl (Cap.target Hag'_cap))) as [exP Hex].
    destruct_tuple exP ex_cap'_obj ex_cap'_lbl ex_cap'_type ex_cap'_sched;
      simpl in Hex; destruct Hex as [HCex HCexMap];
        destruct_tuple HCex HCex1 HCex2 HCex3 HCex4.
    unfold SC.set_alive in HCexMap; unfold SC.set_label in HCexMap.
    unfold SC.addObjTuple in HCexMap; unfold SC.getObjTuple in HCexMap.
    rewrite Sys_Facts.add_eq_o in HCexMap; eauto; simpl in *.
    eapply Sys_Facts.add_mapsto_iff in HCexMap; simpl in *.
    destruct HCexMap as [[Heq' HCexMap]|[Hneq' HCexMap]].
    (* case n [=] (target Hag'_cap) *)
    (* contradiction: by Heq' and Hsafe *)
    assert (False); try contradiction.
    apply Hsafe.
    apply ex_intro with Hag'_src_ref; apply ex_intro with (ex_obj, ex_lbl, ex_type, ex_sched).
    split; auto.
    apply ex_intro with Hag'_ind; apply ex_intro with ex_cap'.
    split; auto.
    (* n = target Hag'_cap.  Hag'_cap [=] ex_cap [=] ex_cap' *)
    rewrite Heq'.
    eapply Cap.target_eq.
    eapply Cap.eq_trans;
       [eapply Cap.eq_sym; eapply HCeq' | eapply Cap.eq_sym; auto].
    (* case n [<>] (target Hag'_cap) *)
    (* simpl out the inner hexmap. *)
    eapply Sys_Facts.add_mapsto_iff in HCexMap; simpl in *.
    destruct HCexMap as [[Heq'' HCexMap]|[Hneq'' HCexMap]]; try contradiction ; simpl in *; clear Hneq''.

    assert (Cap.eq Hag'_cap ex_cap') as Hcapeq;
      [eapply Cap.eq_trans; [apply HCeq | apply HCeq']|].
    (* INSTANTIATE! *)
    apply_ex_intro_dirAcc s s Hag'_src_ref ex_obj ex_lbl ex_type ex_sched 
    ex_obj ex_lbl ex_type ex_sched  Hag'_ind ex_cap'
    ex_cap'_obj ex_cap'_lbl ex_cap'_type ex_cap'_sched 
    ex_cap'_obj ex_cap'_lbl ex_cap'_type ex_cap'_sched Hag'_rgt;
      try apply Sys.eq_refl; try apply Sys.P.eq_refl; eauto.
    (* case alive [=] ex_lbl *)
    rewrite <- Hex2.
    rewrite Hag'_eqLbl.
    apply ObjectLabel.eq_sym; auto.
    (* case MapsTo (target ex_cap') (ex_cap'_obj, ...) s *)
    eapply Sys_Facts.MapsTo_iff; [eapply Cap.target_eq; apply Cap.eq_sym; apply Hcapeq| auto].
    (* alive [=] ex_cap'_lbl *)
    rewrite <- HCex2.
    rewrite Hag'_eqObjLbl.
    apply ObjectLabel.eq_sym ; auto.
    (* case In Hag'_rgt (rights ex_cap') *)
    eapply Cap.rights_eq; [apply Cap.eq_sym; apply Hcapeq | auto].
    (* case eq (mkEdge Hag'_src_ref (target ex-cap') Hag'_rgt) edge *)
    apply Edge.eq_sym; eapply Edge.eq_trans.
    apply Edge.eq_sym; apply Hag'_eqEdge.
    apply Edges.edge_equal; try apply Ref.eq_refl; try apply Cap.target_eq;  try apply AccessRight.eq_refl; auto.
    (* case false *)
    clear Hsafe.
    eapply H1; clear H1.
    eapply dirAcc_spec_eq; [ eapply Sys.eq_refl | apply H | apply H0 | eauto].
    Qed.

      Theorem dirAcc_approx_iso_sub: forall Fs Fs' Fa Fa',
        (forall s, Sys.eq (Fs s) (Fs' s)) -> 
        (forall a, AG.Subset (Fa a) (Fa' a)) -> 
        dirAcc_approx Fs Fa -> dirAcc_approx Fs' Fa'.
      Proof.
        unfold dirAcc_approx; intros.
        eapply dirAcc_spec_iff in H3; [|apply H | apply AG.eq_refl].
        generalize (H1 s ag ag' ag2 H2 H3 H4); clear H1; intros H1.
        generalize (H0 ag'); clear H0; intros H0.
        intros element Hin; eapply H0; auto.
      Qed.
        (* generalize (ag_eq_Equal (Fa ag') (Fa' ag')); intros [Heq _]. *)
        (* apply Heq in H0; clear Heq. *)


      Theorem dirAcc_approx_iso: forall Fs Fs' Fa Fa',
        (forall s, Sys.eq (Fs s) (Fs' s)) -> 
        (forall a, AG.eq (Fa a) (Fa' a)) -> 
        dirAcc_approx Fs Fa -> dirAcc_approx Fs' Fa'.
      Proof.
        intros.
        eapply dirAcc_approx_iso_sub; [eapply H | |  eapply H1].
        intros ag; generalize (ag_eq_Equal (Fa ag) (Fa' ag)); intros [Heq _];  apply Heq in H0; clear Heq.
        intros element; eapply H0.
      Qed.

    (* let us combine dirAcc_approx_rmCapsByTarget and dirAcc_approx_set_alive_empty *)
    Theorem dirAcc_approx_set_alive_empty_o_rmCapsByTarget : forall n l t d,
      dirAcc_approx
        (fun s => SC.set_alive n (Sys.MapS.add n (Obj.MapS.empty Cap.t, l, t, d) (SC.rmCapsByTarget n s)))
        (fun ag => ag).
    Proof.
        intros.
        generalize (dirAcc_approx_comp _ _ _ _ (dirAcc_approx_rmCapsByTarget n) (dirAcc_approx_set_alive_empty n l t d));
          intros Hcomp.
        assert (forall s, SC.safe_to_make_alive n (SC.rmCapsByTarget n s)) as Hassert;
        [intros; eapply SC.safe_to_make_alive_rmCapsByTarget_spec;
        eapply SC.rmCapsByTarget_spec_rmCapsByTarget|].
        eapply dirAcc_approx_iso with 
          (Fs:=
            (fun s : Sys.t =>
              if true_bool_of_sumbool
                (SC.safe_to_make_alive_dec n
                  (SC.rmCapsByTarget n s))
                then
                  SC.set_alive n
                  (Sys.MapS.add n
                    (Obj.MapS.empty Cap.t, l, t, d)
                    (SC.rmCapsByTarget n s))
                else SC.rmCapsByTarget n s)); eauto; try solve [intros edge; simpl; apply AG.eq_refl].
      intros.
      unfold true_bool_of_sumbool.
      rewrite proof_r_true_bool_of_sumbool; try apply Sys.eq_refl; eauto.
    Qed.



    Theorem dirAcc_approx_allocate : forall n a l t d index,
    let rgts := (ARSet.add AccessRights.rd
          (ARSet.add AccessRights.wr
            (ARSet.add AccessRights.wk
              (ARSet.singleton AccessRights.tx)))) in
    let cap:= (Cap.mkCap n rgts) in
      dirAcc_approx
      (fun s =>
        let s:= SC.set_alive n (Sys.MapS.add n (Obj.MapS.empty Cap.t, l, t, d) (SC.rmCapsByTarget n s)) in
        match Sys.MapS.find a s with
          | Some (obj, obj_lbl, obj_type, obj_sched) =>
            (Sys.MapS.add a (Obj.MapS.add index cap obj, obj_lbl, obj_type, obj_sched) s) 
          | None => s
        end)
      (fun ag => ag_add_cap a cap ag).
    Proof.
      intros.
      generalize (dirAcc_approx_comp _ _ _ _ 
        (dirAcc_approx_set_alive_empty_o_rmCapsByTarget n l t d)
        (dirAcc_addCap_subset_approx_equiv a index cap));intros Hiso.
      eapply dirAcc_approx_iso_sub with
        (Fs := 
          (fun s : Sys.t =>
            match
              Sys.MapS.find a
                (SC.set_alive n
                   (Sys.MapS.add n
                      (Obj.MapS.empty Cap.t, l, t, d)
                      (SC.rmCapsByTarget n s)))
            with
            | Some (pair (pair (pair obj obj_lbl) obj_type) obj_sched) =>
                Sys.MapS.add a
                  (Obj.MapS.add index cap obj, obj_lbl, obj_type,
                  obj_sched)
                  (SC.set_alive n
                     (Sys.MapS.add n
                        (Obj.MapS.empty Cap.t, l, t, d)
                        (SC.rmCapsByTarget n s)))
            | None =>
                SC.set_alive n
                  (Sys.MapS.add n
                     (Obj.MapS.empty Cap.t, l, t, d)
                     (SC.rmCapsByTarget n s))
            end)); eauto; intros; simpl in *; try solve [apply AG.eq_refl | apply Sys.eq_refl].
     Qed.

    Theorem ag_add_cap_ag_add_cap: forall n cap n' cap' ag,
       AG.eq (ag_add_cap n cap (ag_add_cap n' cap' ag))
             (ag_add_cap n' cap' (ag_add_cap n cap ag)).
    Proof.
      intros.
      eapply ag_eq_Equal.
      intros edge.
      generalize (ag_add_cap_spec edge n cap _ _ (AG.eq_refl (ag_add_cap n' cap' ag))); intros Hag1.
      generalize (ag_add_cap_spec edge n cap _ _ (AG.eq_refl ag)); intros Hag1'.
      generalize (ag_add_cap_spec edge n' cap' _ _ (AG.eq_refl (ag_add_cap n cap ag))); intros Hag2.
      generalize (ag_add_cap_spec edge n' cap' _ _ (AG.eq_refl ag)); intros Hag2'.
      intuition auto.
    Qed.


Theorem addCap_addCap: forall i cap n i' cap' n' s,
  ~ Ref.eq n n' ->
  Sys.eq (SC.addCap i cap n (SC.addCap i' cap' n' s))
       (SC.addCap i' cap' n' (SC.addCap i cap n s)).
Proof.
   intros.
   unfold SC.addCap.
   unfold SC.updateObj.
   unfold SC.getObj.
   (* cases on getObjTuple n s *)
   case (option_sumbool (SC.getObjTuple n s)); intros Hns; 
     [|destruct Hns as [[[[ns_obj ns_lbl] ns_typ] ns_schd] Hns]];  
   (* cases on getObjTuple n' s *)
   (case (option_sumbool (SC.getObjTuple n' s)); intros Hn's; 
     [|destruct Hn's as [[[[n's_obj n's_lbl] n's_typ] n's_schd] Hn's]];  
        repeat progress (try rewrite Hns in *; try rewrite Hn's in *; simpl in *)).
   (* base case *)
   apply Sys.eq_refl.
   (* None / Some *)
   unfold SC.getObjTuple in *; unfold SC.addObjTuple in *.
   rewrite Sys_Facts.add_neq_o; simpl; auto.
   unfold Sys.P.t in *.
   rewrite Hns; simpl in *.
   apply Sys.eq_refl.
   (* Some / None *)
   unfold SC.getObjTuple in *; unfold SC.addObjTuple in *.
   rewrite Sys_Facts.add_neq_o; simpl; auto.
   unfold Sys.P.t in *.
   rewrite Hn's; simpl in *.
   apply Sys.eq_refl.
   (* Some / Some *)
   unfold SC.getObjTuple in *; unfold SC.addObjTuple in *.
   repeat progress (rewrite Sys_Facts.add_neq_o; simpl; auto).
   unfold Sys.P.t in *.
   rewrite Hns; simpl in *.
   rewrite Hn's; simpl in *.
   (* this is going to be a lot of work here. we might want to generalize this now *)
   apply Sys_OrdAdd.sord_add_add; auto.
   apply Sys.eq_refl.
Qed.


  Theorem dirAcc_allocate: forall s ag,
    dirAcc_spec s ag ->
    forall a n i ixi_list ag',
      dirAcc_spec (Sem.do_allocate a n i ixi_list s) ag' ->
      AG.Subset ag' (ag_add_caps_allocate a n ixi_list s ag).
  Proof.
    (* we can't introduce ag', or we won't get a correct induction tactic *)
    intros s ag H a n i ixi_list.
    (* first, by cases on satisfying the prereq *)
    case (SemDefns.allocate_preReq_dec a n s); intros Hpre;
      [ generalize (Sem.allocate_valid _ _ i ixi_list _ Hpre)
        | generalize (Sem.allocate_invalid _ _ i ixi_list _ Hpre)]; intros Heq;
      [|intros; assert (AG.eq ag' ag); eauto; eapply dirAcc_spec_eq; eauto].
    (* case where preReq is satisfied *)
    (* unfold preReq *)
    unfold SemDefns.allocate_preReq in Hpre.
    unfold SemDefns.preReqCommon in Hpre.
    destruct Hpre as [[Halive Hactive] HtargetUnborn].
    unfold SemDefns.target_is_alive in Halive; unfold SC.is_alive in Halive;
          unfold SC.is_label in Halive; unfold SC.getLabel in Halive; red in Halive.
    unfold SC.is_unborn in HtargetUnborn;
          unfold SC.is_label in HtargetUnborn; unfold SC.getLabel in HtargetUnborn; red in HtargetUnborn.
    (* simplify Halive by cases on SC.getObjLabel a s *)
    (* contradiction in the None case *)
    unfold SC.getLabel in *.
    case (option_sumbool (SC.getObjTuple a s)); intros Hopt2;[|destruct Hopt2 as [pair Hopt2]];
      rewrite Hopt2 in Halive;
        [contradiction| destruct_tuple pair actor actor_lbl actor_type actor_sched; simpl in Halive].
    (* simplify HtargetUnborn by cases on SC.getObjLabel a s *)
    (* contradiction in the None case *)
    unfold SC.getLabel in *.
    case (option_sumbool (SC.getObjTuple n s)); intros Hopt2u;[|destruct Hopt2u as [pair Hopt2u]];
      rewrite Hopt2u in HtargetUnborn;
        [contradiction| destruct_tuple pair child child_lbl child_type child_sched; simpl in HtargetUnborn].
    (* unfold Heq.*)
    unfold SC.copyCapList in Heq; unfold SC.copyCap in Heq.
    (* unfold Goal *)
    unfold ag_add_caps_allocate. unfold ag_add_caps_by_index_pair_list.
      unfold ag_add_cap_by_indirect_index. unfold ag_add_cap_by_obj_index.
        unfold ag_add_cap_valid; unfold ag_add_cap_valid_allocate.

    (* we know is_alive a s,  *)
(*        it was an assumption, now unfolded and blown apart.  assert it. *)
    assert (SC.is_alive a s) as HisAlive;
      [unfold SC.is_alive; unfold SC.is_label; unfold SC.getLabel; rewrite Hopt2; simpl; auto|].
(* With the fix to ag_add_caps_allocate, this no longer works, because n is not alive in s. *)
(* ag_add_caps_allocate is only to apply after setting the cap alive.
   we've written the wrong theorem, yet again. *)

(* this is no longer necessary, as we have eliminated the check in s *)
    (* use the above assertion to rewrite true_bool_of_sumbool *)
(*    unfold true_bool_of_sumbool;
      rewrite (proof_r_true_bool_of_sumbool _ (SC.is_alive_dec _ _) HisAlive);
          simpl;
            clear HisAlive. *)

    (* show that a <> n *)
    assert (~ Ref.eq a n);
      [intro Hnot; unfold SC.getObjTuple in *;
        rewrite Sys_Facts.find_o with (y:=n) in Hopt2; auto;
          rewrite Hopt2 in Hopt2u; inversion Hopt2u;
            rewrite H2 in *; apply ObjectLabel.eq_trans with (x:=ObjectLabels.unborn) in Halive; auto;
              discriminate Halive|].

    (* attempt to remove getObjTuple a ... (rmCapsByTarget n s) *)
    generalize (SC.getObjTuple_rmCapsByTarget_some _ _ _ _ _ _ n Hopt2); intros [actor' [Hopt2_eq Hopt2']].
    assert (SC.getObjTuple a (SC.set_alive n
      (Sys.MapS.add n (Obj.MapS.empty Cap.t, child_lbl, child_type, child_sched) (SC.rmCapsByTarget n s))) = 
        Some (OC.rmCapsByTarget n actor', actor_lbl, actor_type, actor_sched)) as Harm;
    [unfold SC.set_alive; unfold SC.set_label; unfold SC.getObjTuple;
    (* simplify find n add n *)
      rewrite Sys_Facts.add_eq_o; simpl; try solve [apply Ref.eq_refl];
    (* simplify via outer add *)
        unfold SC.addObjTuple;
    repeat progress (rewrite Sys_Facts.add_neq_o); auto|].

    (* we may have to induct over ixi_list here.  The add happens in the base case. *)
    induction ixi_list; simpl; intros; simpl in *.

    (* base case *)
    (* simplify Heq *)
    unfold SC.addCap in Heq.
    unfold SC.getObj in Heq.
    unfold SC.updateObj in Heq.
    unfold OC.addCap in Heq.
    unfold SC.update_pair_object in Heq.
    simpl in Heq.
    (* attempt to remove getObjTuple n (rmCapsByTarget n s) *)
    generalize (SC.getObjTuple_rmCapsByTarget_some _ _ _ _ _ _ n Hopt2u); intros [child' [Hopt2u_eq Hopt2u']].
    unfold SC.addObjTuple in Heq.
    rewrite Hopt2u' in Heq; simpl in Heq.
(*    rewrite (Sys_Facts.add_neq_o _ _ H0) in Heq.
    unfold SC.getObjTuple in Hopt2u'; rewrite Hopt2u' in *; simpl in *.*)
    unfold Sys.P.t in Heq; unfold Obj.t in Heq.
    rewrite Harm in Heq; simpl in Heq.

    (* alright!  Ath this point we have rmCapsByTarget, followed by
       setting n alive, and finished an operation captured by ag_add_cap.
       We know that rmCapsByTarget is approximated by (fun ag => ag),
       we need to know that setting an empty active child is as well, fed something
       that is a rmCapsByTarget_spec *)
    (* The best way I can think of to say this is to have Fs be
       (fun s => 
         if true_bool_of_sumbool (SC.safe_to_make_alive n s) then 
        (SC.set_alive n (Sys.MapS.add n (Obj.MapS.empty Cap.t, l, t, d) s))
        else s ) 
        and then prove that when s is (SC.rmCapsByTarget n s), this is the function we were solving for,
        only reduced.  *)


(* well, this is almost correct.
   we can't unfold do_allocate, but we know what it's equivalent to. 
   a [<>] n, so there must be a match, and the body reduces to something equiv to do_allocate.
   we have the right parts, we just need to set all of them up *)
eapply (dirAcc_approx_allocate n a child_lbl child_type child_sched i); simpl in *;
(* okay, these might not be correct *)
[apply H | | eauto ].
    (* rewrite using Harm *)
    unfold SC.getObjTuple in Harm.
    rewrite Harm; simpl.
    eapply dirAcc_spec_iff; [apply Sys.eq_sym; apply Heq | apply AG.eq_refl |  auto].

    (* induction case *)
    (* this looks better *)
    intros.
    (* destruct the ixi pair *)
    destruct a0 as [i_src i_dst]; simpl in *.
    generalize (Sem.allocate_valid a n i ixi_list s); intros IHallocate.
    (* prereq is in too many pieces *)
    assert (SemDefns.allocate_preReq a n s) as HpreReq.
    unfold SemDefns.allocate_preReq.
    split; auto;
    unfold SemDefns.preReq;
    unfold SemDefns.preReqCommon;
    unfold SemDefns.target_is_alive;
    unfold SC.is_alive;
    unfold SC.is_unborn;
    unfold SC.is_label;
    unfold SC.getLabel;
    unfold SC.is_type.
    (* rewrite Hopt2;*) (* rewrite Hopt3; *) simpl; eauto.
    rewrite Hopt2u; simpl; eauto.    
    (* apply HpreReq in IHallocate *)
    generalize (IHallocate HpreReq); clear IHallocate; intros IHallocate.
    (* rewrite Hopt3 in IHallocate; simpl in IHallocate. *)
    generalize (IHixi_list IHallocate); clear IHallocate; clear IHixi_list; intros IH.
    (* okay, we have an IH that will let us recurse, but only if we can instantiate it. *)
(*        we have not yet proved that dirAcc_spec is decidable, nor that one always exists. *)
(*        If we can show these, thein we can instantiate the IH, and recurse in both cases.*)
    generalize (exists_dirAcc_spec (Sem.do_allocate a n i ixi_list s)); intros Hex.
    destruct Hex as [ag_spec Hdiracc];
      generalize (IH ag_spec Hdiracc); clear IH; intros IH.
    (* generalize the inductive hypothesis allocate *)
    generalize (Sem.allocate_valid a n i ixi_list s HpreReq); intros Hallocate_i; (* rewrite Hopt3 in Hallocate_i; *)
      simpl in Hallocate_i; unfold SC.copyCapList in Hallocate_i; unfold SC.copyCap in Hallocate_i.
    (* at this point the (fold_right ...) parts in the goal should be the same as in IH.
       We need to reduce the goal and Heq together and show they are the same. *)
    (* destruct the cases of getCap i_src a ..., show Subset ag' (dirAcc allocate) *)

    (* with the change to creae_valid, everything compiles and is correct to here *)
    (* Heq has the addCap on the outside, so we are going to need to deal with that eventually.
       However, to continue reducing cases, we need to eliminate the addCap below *)

    case (option_sumbool 
      (SC.getCap i_src a
                (fold_right
                   (fun (ixi : Ind.t * Ind.t) (s : Sys.t) =>
                    option_map1
                      (fun cap : Cap.t =>
                      SC.addCap (snd ixi) cap n s) s
                      (SC.getCap (fst ixi) a s))
                      (SC.set_alive n
                         (SC.updateObj n
                            (Obj.MapS.empty Cap.t)
                            (SC.rmCapsByTarget n s))) ixi_list))); intros Hi_src; 
      [| destruct Hi_src as [i_cap Hi_src]]; try rewrite Hi_src in *; simpl in *.
    (* None (...) *)
    (* show that all these are equal, and produce AG.Equal ag' ag_spec *)
    assert (Sys.eq (Sem.do_allocate a n i ((i_src, i_dst) :: ixi_list) s) (Sem.do_allocate a n i ixi_list s)) as HallocateEq;
      [apply Sys.eq_sym in Hallocate_i; eapply Sys.eq_trans; [apply Heq| apply Hallocate_i]|].
    (* show ag' [=] ag_spec *)
    assert (AG.eq ag' ag_spec) as HagEq;[
      eapply dirAcc_spec_eq; try apply HallocateEq; auto|
        generalize (ag_eq_Equal ag' ag_spec); intros HagEqual; destruct HagEqual as [HagEqual _];
          apply HagEqual in HagEq].
    (* cases on getCap i_src a s  *)
    case (option_sumbool (SC.getCap i_src a s)); intros Hopt5; [|destruct Hopt5 as [i_cap Hopt5]];
      rewrite Hopt5 in *; simpl in *.
      apply AGFacts.Subset_trans with ag_spec.
        unfold AG.Equal in HagEq; unfold AG.Subset; intro element; eapply (HagEq element).
        apply IH.    
      case (SC.is_alive_dec (Cap.target i_cap) s); intros Hopt7; simpl in *.
        apply AGFacts.Subset_trans with (ag_add_cap n i_cap ag_spec).
          apply ag_add_cap_nondecr. unfold AG.Equal in HagEq; unfold AG.Subset; intro element; eapply (HagEq element).
        unfold ag_add_cap_mod.
  (* reorder the ag_add_cap calls in the conclusion *)
  eapply AGProps.subset_trans; [|eapply AGProps.subset_equal; eapply ag_add_cap_ag_add_cap].
  (* run ag_add_cap_subset and use IH *)
  apply ag_add_cap_subset; try apply Ref.eq_refl; try apply Cap.eq_refl; apply IH.
  apply AGFacts.Subset_trans with  ag_spec.
        unfold AG.Equal in HagEq; unfold AG.Subset; intro element; eapply (HagEq element).
        apply IH.
   (* Some (...) *)
    (* rephrase the our equality in the induction *)
    assert (Sys.eq (Sem.do_allocate a n i ((i_src, i_dst) :: ixi_list) s) 
      (SC.addCap i_dst i_cap n (Sem.do_allocate a n i ixi_list s))) as HallocateEq.

    eapply Sys.eq_trans.
      (* case 1 *) 
      apply Heq.
      (* case 2 *)
(* move to system state *)
   eapply Sys.eq_trans.
   eapply addCap_addCap; auto.
   apply SC.addCap_eq; auto. try apply Ref.eq_refl.
   (* apply Sys.eq_sym. *)
   (* apply Sem.allocate_valid; eauto. *)

    (* we need to know that getCap i_src a s [=] Some i_cap *)
    (* use getCap_copyCapList_map_eq and cases on getCap i_src a s.*)

 

(* unfurl copyCapList in Hi_src *)
generalize (SC.getCap_copyCapList_map_eq _ _ _ _ _ _ _ _ (Ref.eq_refl a) H0 (refl_equal _) Hi_src);
  intros Hfold.
case (option_sumbool 
   (SC.getCap i_src a (SC.set_alive n (SC.updateObj n (Obj.MapS.empty Cap.t) (SC.rmCapsByTarget n s))))); 
      intros Hcase; [|destruct Hcase as [i_cap' Hcase]]; rewrite Hcase in Hfold; simpl in Hfold; try contradiction.

(* unfurl getCap in Hcase *)
unfold SC.set_alive in Hcase.
idtac.
rewrite SC.getCap_set_label_neq_o in Hcase; [|auto].

idtac.
rewrite SC.getCap_updateObj_neq_o in Hcase; [|auto].

generalize (SC.rmCapsByTarget_spec_rmCapsByTarget n s); intros [_[Hmapsto [_ Htarget]]].
unfold SC.rmCapsByTarget_spec_mapsto in *.
generalize (Hmapsto a actor_lbl actor_type actor_sched); clear Hmapsto; intros [_ Hmapsto].
assert (exists o' : Obj.MapS.t Cap.t,
               exists l' : ObjectLabels.ObjectLabel.t,
                 exists t' : ObjectTypes.ObjectType.t,
                   exists d' : ObjectSchedules.ObjectSchedule.t,
                     ObjectLabels.ObjectLabel.eq actor_lbl l' /\
                     ObjectTypes.ObjectType.eq actor_type t' /\
                     ObjectSchedules.ObjectSchedule.eq actor_sched d' /\
                     Sys.MapS.MapsTo a (o', l', t', d') s) as Hassert.
do 4 (eapply ex_intro).
repeat progress (split; try apply ObjectLabel.eq_refl; try apply ObjectType.eq_refl; try apply ObjectSchedule.eq_refl).
eapply Sys_Facts.find_mapsto_iff.
eauto.

eapply Hmapsto in Hassert. clear Hmapsto;
destruct Hassert as [o' [l' [t' [d' [Hl [Ht [Hd Hm]]]]]]].

unfold SC.rmCapsByTarget_spec_not_target in *.
generalize (Htarget a i_src i_cap' actor_lbl actor_type actor_sched); clear Htarget; intros [Htarget _].

assert (exists o' : Obj.MapS.t Cap.t,
               exists l' : ObjectLabels.ObjectLabel.t,
                 exists t' : ObjectTypes.ObjectType.t,
                   exists d' : ObjectSchedules.ObjectSchedule.t,
                     exists c' : Cap.t,
                       ObjectLabels.ObjectLabel.eq actor_lbl l' /\
                       ObjectTypes.ObjectType.eq actor_type t' /\
                       ObjectSchedules.ObjectSchedule.eq actor_sched d' /\
                       Cap.eq i_cap' c' /\
                       Sys.MapS.MapsTo a (o', l', t', d')
                         (SC.rmCapsByTarget n s) /\
                       Obj.MapS.MapsTo i_src c' o') as Hassert.
do 5 (eapply ex_intro).
repeat progress (split; try apply Hl; try apply Ht; try apply Hd; try apply Hm; try apply Cap.eq_refl).
unfold SC.getCap in Hcase.
unfold SC.getObj in Hcase.
eapply Sys_Facts.find_mapsto_iff in Hm.
unfold SC.getObjTuple in Hcase.
rewrite Hm in Hcase; simpl in *.
eapply Obj_Facts.find_mapsto_iff in Hcase.
auto.

eapply Htarget in Hassert.
clear Htarget.

(* done with assertions, back to Some ... case. We can continue rewriting. *)
destruct Hassert as [o'2 [l'2 [t'2 [d'2 [i_cap'2 [Hl' [Ht' [Hd' [Hc' [Hm' [Hi' Hneq']]]]]]]]]]].
unfold SC.getObjTuple in Hopt2.
eapply Sys_Facts.find_mapsto_iff in Hm'; rewrite Hopt2 in Hm'.
inversion Hm' as [[Hao' Hal' Hat' Had']]; rewrite <- Hao' in *; rewrite <-  Hal' in *;
   rewrite <- Had' in *; rewrite <- Hat' in *; simpl in *. clear Hm'.
assert (SC.getCap i_src a s = Some i_cap'2) as Hget.
unfold SC.getCap.
unfold SC.getObj.
unfold SC.getObjTuple.
rewrite Hopt2. simpl.
eapply Obj_Facts.find_mapsto_iff.
auto.

(* we can now rewrite SC.getCap i_src a s *)
rewrite Hget; simpl.

(* perform cases on if it is alive *)

 case (SC.is_alive_dec (Cap.target i_cap'2) s); intros Hopt7; simpl in *.

 unfold SC.addCap in HallocateEq.
 unfold SC.updateObj in HallocateEq.
    unfold SC.addObjTuple in HallocateEq.
    unfold SC.getObj in HallocateEq.


 case (option_sumbool (SC.getObjTuple n (Sem.do_allocate a n i ixi_list s))); intros Hopt8;
    [|destruct Hopt8 as [tuple_8 Hopt8]; destruct_tuple tuple_8 obj_8 lbl_8 type_8 sched_8];
    rewrite Hopt8 in *; simpl in *.

    (* technically a contradiciton case, but it's easier to just instantiate from subset *)
    eapply AGFacts.Subset_trans with ag_spec; auto.

   (* show ag' [=] ag_spec *)
    assert (AG.eq ag' ag_spec) as HagEq;[
      eapply dirAcc_spec_eq; try apply HallocateEq; auto|
        generalize (ag_eq_Equal ag' ag_spec); intros HagEqual; destruct HagEqual as [HagEqual _];
          apply HagEqual in HagEq].
    (*solve *)
    intro edge; eapply (HagEq edge); auto.
    unfold ag_add_cap_mod.
    Ltac ag_subset_swap :=
      eapply AGFacts.Subset_trans; [|eapply AGProps.subset_equal; eapply ag_add_cap_ag_add_cap].
    ag_subset_swap.
    eapply ag_add_cap_nondecr.
    eapply IH.


(* case where things are intereting *)
    unfold OC.addCap in HallocateEq.
    unfold SC.getObjTuple in Hopt8.
    apply Sys.MapS.find_2 in Hopt8.

    (* apply diracc_addcap_subset, reduce to add over send ixi_list *)
    ag_subset_swap.
    eapply dirAcc_addCap_subset with (ag:=ag_spec); [ apply Hopt8 | apply Hdiracc | | apply IH ].
    (* apply dirAcc_spec_iff to get close to HsendEq *)
    eapply dirAcc_spec_iff; [| apply AG.eq_refl| apply H1].
    (* apply eq_trans and HsendEq for nearly eq types except for i_cap *)
    eapply Sys.eq_trans; [|apply Sys.eq_sym; apply HallocateEq].
    (* reduce to i_cap [=] i_cap'2 *)
    eapply SC.addObjTuple_eq; eauto; try apply Sys.eq_refl; try apply Ref.eq_refl.
    unfold Sys.P.eq; simpl.
    repeat progress (try split; eauto).
    eapply OC.addCap_eq; auto; try apply Obj.eq_refl.
    eapply Cap.eq_trans ;[|eapply Hfold]; apply Cap.eq_sym; auto.

(* and now the not alive case *)

 unfold SC.addCap in HallocateEq.
 unfold SC.updateObj in HallocateEq.
    unfold SC.addObjTuple in HallocateEq.
    unfold SC.getObj in HallocateEq.


 case (option_sumbool (SC.getObjTuple n (Sem.do_allocate a n i ixi_list s))); intros Hopt8;
    [|destruct Hopt8 as [tuple_8 Hopt8]; destruct_tuple tuple_8 obj_8 lbl_8 type_8 sched_8];
    rewrite Hopt8 in *; simpl in *.

    (* technically a contradiciton case, but it's easier to just instantiate from subset *)
    eapply AGFacts.Subset_trans with ag_spec; auto.

   (* show ag' [=] ag_spec *)
    assert (AG.eq ag' ag_spec) as HagEq;[
      eapply dirAcc_spec_eq; try apply HallocateEq; auto|
        generalize (ag_eq_Equal ag' ag_spec); intros HagEqual; destruct HagEqual as [HagEqual _];
          apply HagEqual in HagEq].
    (*solve *)
    intro edge; eapply (HagEq edge); auto.

(* case where things are intereting *)
    unfold OC.addCap in HallocateEq.
    unfold SC.getObjTuple in Hopt8.
    apply Sys.MapS.find_2 in Hopt8.

    (* apply diracc_addcap_subset, reduce to add over send ixi_list *)
    apply AGFacts.Subset_trans with ag_spec; auto.
    
eapply dirAcc_addCap_notAlive_2;
    [ apply Hopt8
      | apply Hdiracc
      | 
      | eapply dirAcc_spec_iff; [| apply AG.eq_refl| apply H1]; apply Sys.eq_sym in HallocateEq; apply HallocateEq].
 intro Hnot.
  apply Hopt7.
  unfold SC.is_alive. unfold SC.is_alive in Hnot.
  eapply (SC.isLabel_eq _ _ _ _ _ _ (Ref.eq_refl _ ) (ObjectLabel.eq_refl _) Hallocate_i) in Hnot.

  eapply SC.is_label_iff_getLabel.
  eapply SC.is_label_iff_getLabel in Hnot.



  (* send was expecting Hnot to not include addCap *)

  eapply SC.getLabel_addCap_map_1 with (opt_i_lbl:= Some ObjectLabels.alive) in Hnot;
    [| simpl; auto; apply ObjectLabel.eq_refl].

  eapply SC.getLabel_copyCapList_map_1 with (opt_i_lbl:= Some ObjectLabels.alive) in Hnot; 
    [| simpl; auto; apply ObjectLabel.eq_refl].
 
unfold SC.set_alive in Hnot.
rewrite SC.getLabel_set_label_neq_o in Hnot. (* come back to ~ n [=] (target i_cap)*)


rewrite SC.getLabel_updateObj_o in Hnot.

rewrite SC.getLabel_rmCapsByTarget_o in Hnot.
eapply Cap.eq_trans in Hc'; [|apply Cap.eq_sym; apply Hfold].
generalize (Cap.target_eq _ _ Hc'); intros Hteq.
generalize (SC.getLabel_eq _ _ _ _ Hteq (Sys.eq_refl s)). intros Hleq.
rewrite Hnot in Hleq; simpl in Hleq.
case (option_sumbool (SC.getLabel (Cap.target i_cap'2) s)); intros Hcase2;
[|destruct Hcase2 as [l Hcase2]]; rewrite Hcase2 in Hleq; try contradiction.
rewrite <- Hleq in Hcase2.
auto.

(* (target i_cap) [<>] n *)

intro Hnot2.
apply Hneq'.
eapply Ref.eq_trans.
eapply Cap.target_eq.
eapply Hfold.
auto.
Qed.

End MakeDirectAccessSemantics.