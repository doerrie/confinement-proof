Require Import OptionSumbool.
Require Import AccessRights.
Require Import References.
Require Import Capabilities.
Require Import Indices.
Require Import Objects.
Require Import ObjectLabels.
Require Import SystemState.
Require Import SemanticsDefinitions.
Require Import Semantics.
Require Import Semantics_Conv.
Require Import AccessRightSets.
Require Import Execution.
Require Import RefSets.
Require Import Iff_Equiv.
Require Import AccessGraphs.
Require Import AccessEdge.
Require Import SequentialAccess.
Require Import Mutability.
Require Import Mutation.
Require Import AccessExecutionImpl.
Require Import Morphisms.
Require Import Basics.
Require Import Sumbool_dec.
Require Import MutableSubsetImpl.
Require Import CapSets.
Require Import Subsystem.
Require Import Decidable.
Require Import Irrelevance.


(* type_remove *)
 Require Import Confinement.

Module MakeConfinement (Ref:ReferenceType) (RefS: RefSetType Ref) (Edges: AccessEdgeType Ref) (AccessGraph:AccessGraphType Ref Edges) (Seq:SeqAccType Ref RefS Edges AccessGraph) (Cap:CapabilityType Ref) (CapS: CapSetType Ref Cap) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) (SemDefns: SemanticsDefinitionsType Ref Cap Ind Obj Sys) (Sem: SemanticsType Ref RefS Cap Ind Obj Sys SemDefns) (Exe: ExecutionType Ref RefS Cap Ind Obj Sys SemDefns Sem) (Mut: MutationType Ref RefS Cap Ind Obj Sys SemDefns Sem Exe) (Sub: SubsystemType Ref RefS Edges AccessGraph Seq Cap CapS Ind Obj Sys SemDefns Sem Exe) : ConfinementType Ref RefS Edges AccessGraph Seq Cap CapS Ind Obj Sys SemDefns Sem Exe Mut Sub.

Module MSub := MakeMutableSubset Ref RefS Edges AccessGraph Seq Cap Ind Obj Sys SemDefns Sem Exe Mut.

Import MSub.
Import Mut.
Import AE.
Import RefS.
Import Mutable.




    Theorem dirAcc_rmCap_monotonic : forall S D, dirAcc_spec S D ->
      forall i o S',  Sys.eq (SC.rmCap i o S) S' ->
        forall D', dirAcc_spec S' D' ->
          AG.Subset D' D.
    Proof.
      intros S D Hda i o S' Hs D' Hda'.
      unfold SC.rmCap in *.
      unfold OC.rmCap in *.
      unfold SC.getObj in *.
      unfold SC.updateObj in *.      
      case (option_sumbool (SC.getObjTuple o S)); intros Hopt';
        [|destruct Hopt' as [[[[Eobj Elbl] Etyp] Esch] Hopt']]; rewrite Hopt' in *; simpl in *;
          (* solve None case *)
          [ solve [eapply AGProps.subset_equal; eapply AG.eq_sym ; eapply dirAcc_spec_eq; eauto]|].
      unfold SC.addObjTuple in *.

      generalize Hs; intros Hda'2; apply Sys.eq_sym in Hda'2.
      eapply dirAcc_spec_if in Hda'2; [| apply AG.eq_refl
        | apply Hda'
          ].

      intros edge Hin.
      eapply Hda' in Hin.

      (* I would think the cases of this are to instantiate all lookups required by dirAcc_spec S D
         and eliminate contradicitons.  Then case on (source edge) [=|<>] o .
         Then case on (target edge) [=|<>] (target (find i Eobj)), though this might want to be a 
         separate theorem. *)

      destruct_dirAcc Hin s1' HeqS src_ref1 src1 lbl1 type1 sched1 HmapS src1' 
      lbl1' type1' sched1' HeqP HaliveL ind1 cap1 Hmap0 cap_obj cap_lbl cap_type cap_sched HmapScap
      cap_obj' cap_lbl' cap_type' cap_sched' HeqPcap HaliveCap rgt1 HinR HeqEdge.    

    (* This code is largely hauled in from DirAccessSemanticsImpl.v and should probably be generalized.
       If this works, go back and generalize theorems which rely on SC.rmCap to reuse this general theorem
       The right starting point is below*)

    (* we should now know enough to apply H. *)
    (* the case analysis is as follows *)
    (* when (target cap) [<>] src_refl1, we can determine (MapsTo src_ref1 (src1, lbl1, type1, sched1) s),
       since do_revoke did not modify src1 under src_refl1, and use H to show (In x ag) *)
    (* when (target cap) [=] src_refl1 /\  c [<>] ind1,  we can determine 
       (MapsTo ind1 cap1 src1'), and use H to show (In x ag) *)
    (* when (target cap) [=] src_refl1 /\ c [=] ind1, there is one remaining case:
       Either there is some other cap that could contribute edge from s, for which we use it; 
       or this is not, and we have a contradiction with H *)
    destruct_tuple HeqP HeqSrc HeqLbl HeqSch HeqTyp; simpl in *.
    destruct_tuple HeqPcap HeqCapSrc1 HeqCapLbl1 HeqCapType1 HeqCapSched1; simpl in *.

    generalize Hs; intros Hs'; eapply Sys.eq_sym in Hs'. 
    eapply Sys.eq_trans in Hs'; [apply Sys.eq_sym in Hs' | apply Sys.eq_sym; apply HeqS].


    case (Ref.eq_dec o src_ref1); intros HeqA.

    (* case where o [=] src_ref1 *)
    (* find src_ref1 in S *)
    generalize Hopt'; intros Hopt1'.
    unfold SC.getObjTuple in Hopt1';
      apply Sys.MapS.find_2 in Hopt1';
        apply Sys.MapS.MapsTo_1 with (y:=src_ref1) in Hopt1'; auto.

    (* at this point, we should know that Elbl [=] lbl1, by Hs*)   

    generalize (Sys_MapEquiv.mapsTo_eq _ _ _ _ _ _  HeqA Hs' (Sys.MapS.add_1 _ _ (eq_refl _)) HmapS);
      intros [[[EobjEq ElblEq] EtypEq] EschEq]; simpl in *.

    (* no case analysis needed, we infer that i [<>] ind1 from remove_mapsoto_iff and Hmap0 *)

    generalize Hmap0; intros Hmap0'.
    eapply Obj_MapEquiv.exists_mapsTo_eq in Hmap0'; [ |
      eapply Obj.eq_trans; [apply Obj.eq_sym; apply HeqSrc | apply Obj.eq_sym; apply EobjEq] |
        eapply Ind.eq_refl].
    destruct Hmap0' as [cap1' [HeqCap1' Hmap0']].
    eapply Obj_Facts.remove_mapsto_iff in Hmap0'; destruct Hmap0' as [Hneq' Hmap0'].

    (* show Elbl = alive *)
    rewrite HeqLbl in ElblEq; rewrite <- HaliveL in ElblEq.
    rewrite <- HaliveCap in HeqCapLbl1.

    (* at this point, the cases are either (target cap1) [=|<>] o *)
    case (Ref.eq_dec o (Cap.target cap1)); intros HtargetEq.

    (* case where o = target cap1 *)
    (* apply dirAcc and instantiate *)
    apply Hda;
      apply_ex_intro_dirAcc S S src_ref1 Eobj Elbl Etyp Esch Eobj Elbl Etyp Esch ind1 cap1' 
      Eobj Elbl Etyp Esch Eobj Elbl Etyp Esch rgt1;
      try apply Sys.eq_refl; try apply Sys.P.eq_refl;
          try apply ObjectLabels.ObjectLabel.eq_sym; auto.

    apply Sys.MapS.MapsTo_1 with src_ref1; auto.
    rewrite <- HeqA; rewrite HtargetEq; apply Cap.target_eq; apply HeqCap1'.

    eapply Cap.rights_eq;
      [apply Cap.eq_sym; apply HeqCap1'| auto].

    eapply Edge.eq_trans; try apply HeqEdge;
      eapply Edges.edge_equal; try apply Cap.target_eq; try apply AccessRight.eq_refl; try apply Ref.eq_refl; auto.

    (* case where o <> target cap1 *)
    (* find target cap in S *)
    generalize HmapScap; intros Hadd.
    eapply Sys_MapEquiv.exists_mapsTo_eq in Hadd;
    [destruct Hadd as [[[[cap_obj2 cap_lbl2] cap_typ2] cap_sch2] [[[[HcapObjeq HcapLblEq] HcapTypEq] HcapSchEq] Hadd]]; simpl in *
      | apply Sys.eq_sym; apply Hs'
        | apply Ref.eq_refl].
    eapply Sys.MapS.add_3 in Hadd; [| apply HtargetEq].

    (* apply dirAcc and instantiate *)
    apply Hda;
      apply_ex_intro_dirAcc S S src_ref1 Eobj Elbl Etyp Esch Eobj Elbl Etyp Esch ind1 cap1' 
      cap_obj2 cap_lbl2 cap_type2 cap_sched2 cap_obj cap_lbl cap_type cap_sched rgt1;
      try apply Sys.eq_refl; try apply Sys.P.eq_refl;
          try apply ObjectLabels.ObjectLabel.eq_sym; auto.

    rewrite HcapTypEq; rewrite HcapSchEq; auto.
    eapply Sys.MapS.MapsTo_1;
      [apply Cap.target_eq; apply HeqCap1'
        | auto].

    rewrite HcapTypEq; rewrite HcapSchEq; rewrite HcapLblEq; auto.
    do 3 (split; simpl; auto); apply Obj.eq_sym; auto.
    
    eapply Cap.rights_eq;
      [apply Cap.eq_sym; apply HeqCap1'| auto].

    eapply Edge.eq_trans; try apply HeqEdge;
      eapply Edges.edge_equal; try apply Cap.target_eq; try apply AccessRight.eq_refl; try apply Ref.eq_refl; auto.

    (* case where o [<>] src_ref1 *)
    
    (* find src_ref1 in S *)
    generalize HmapS; intros HmapS'.
    eapply Sys_MapEquiv.exists_mapsTo_eq in HmapS';
      [ destruct HmapS' as [[[[src2 lbl2] type2] sched2] [[[[HObjEq HLblEq] HTypEq] HSchEq] HmapS']]; simpl in *
        | apply Sys.eq_sym; apply Hs'
        | apply Ref.eq_refl].
    apply Sys.MapS.add_3 in HmapS'; [| auto].

    (* find target cap in (add o  ... S) *)
    generalize HmapScap; intros Hadd.
    eapply Sys_MapEquiv.exists_mapsTo_eq in Hadd;
    [destruct Hadd as [[[[cap_obj2 cap_lbl2] cap_typ2] cap_sch2] [[[[HcapObjeq HcapLblEq] HcapTypEq] HcapSchEq] Hadd]]; simpl in *
      | apply Sys.eq_sym; apply Hs'
        | apply Ref.eq_refl].


    (* demonstrate lbl2 is alive *)
    rewrite <- HeqLbl in HaliveL;
    rewrite HLblEq in HaliveL;
    eapply ObjectLabel.eq_sym in HaliveL.

    (* find cap1 in src2 *)
    eapply Obj_MapEquiv.exists_mapsTo_eq in Hmap0;
      [destruct Hmap0 as [cap1' [HcapEq' Hmap0]]
        |  eapply Obj.eq_trans;
          [apply Obj.eq_sym; apply HeqSrc 
            | apply HObjEq]
        | apply Ind.eq_refl ].

   (* at this point, the cases are either (target cap1) [=|<>] o *)
    eapply Sys_Facts.add_mapsto_iff in Hadd.
    destruct Hadd as [[HeqO Htuple]| [HneqO HmapStarget]].

    (* case where o = target cap1 *)

    inversion Htuple as [[HtargetObj  HtargetLbl HtargetType HtargetSched]]; clear Htuple.
    unfold SC.getObjTuple in Hopt'; eapply Sys_Facts.find_mapsto_iff in Hopt'.

    (* show Elbl = alive *)
    rewrite <- HcapLblEq in HtargetLbl;
    rewrite HeqCapLbl1 in HtargetLbl;
    rewrite <- HaliveCap in HtargetLbl.

    (* apply dirAcc and instantiate *)
    apply Hda;
      apply_ex_intro_dirAcc S S src_ref1 src2 lbl2 type2 sched2 src2 lbl2 type2 sched2 ind1 cap1'
      Eobj Elbl Etyp Esch Eobj Elbl Etyp Esch rgt1;
      try apply Sys.eq_refl; try apply Sys.P.eq_refl;
          try apply ObjectLabels.ObjectLabel.eq_sym; auto.

    rewrite Cap.target_eq; [| apply Cap.eq_sym; apply HcapEq'].
    rewrite <- HeqO; auto.

    eapply Cap.rights_eq;
      [apply Cap.eq_sym; apply HcapEq'| auto].

    eapply Edge.eq_trans; try apply HeqEdge;
      eapply Edges.edge_equal; try apply Cap.target_eq; try apply AccessRight.eq_refl; try apply Ref.eq_refl; auto.

    (* case where o <> target cap1 *)
    (* show cap_lbl2 = alive *)
    rewrite HeqCapLbl1 in HcapLblEq.
    rewrite <- HaliveCap in HcapLblEq.
    apply eq_sym in HcapLblEq.
    

    (* apply dirAcc and instantiate *)
    apply Hda;
      apply_ex_intro_dirAcc S S src_ref1 src2 lbl2 type2 sched2 src2 lbl2 type2 sched2 ind1 cap1'
      cap_obj2 cap_lbl2 cap_typ2 cap_sch2 cap_obj2 cap_lbl2 cap_typ2 cap_sch2 rgt1;
      try apply Sys.eq_refl; try apply Sys.P.eq_refl;
          try apply ObjectLabels.ObjectLabel.eq_sym; auto.

    rewrite Cap.target_eq; [| apply Cap.eq_sym; apply HcapEq']; auto.

    eapply Cap.rights_eq;
      [apply Cap.eq_sym; apply HcapEq'| auto].

    eapply Edge.eq_trans; try apply HeqEdge;
      eapply Edges.edge_equal; try apply Cap.target_eq; try apply AccessRight.eq_refl; try apply Ref.eq_refl; auto.


  Qed.

(* DirAcc is unchanged by removing an empty cap or invalid cap*)
  Theorem void_dirAcc_unchanged: 
    forall S D, DA.dirAcc_spec S D ->
    forall i e cap, SC.getCap i e S = Some cap ->
      ARSet.Empty (Cap.rights cap) ->
    forall S', Sys.eq (SC.rmCap i e S) S' ->
    forall D', DA.dirAcc_spec S' D' ->
    AG.Equal D D'.
  Proof.
    intros S D Hda i e cap Hcap Hrights S' HS' D' Hda'.
    intros x; split; intros Hin.

    eapply Hda in Hin.
    destruct_dirAcc Hin s'' HeqS src_ref src lbl srcType srcSched HmapS 
    src' lbl' srcType' srcSched' HeqP Halive ind1 cap1 HmapSrc'
    cap_obj cap_lbl cap_type cap_sched HmapScap cap_obj' cap_lbl' cap_type' cap_sched' 
    HeqPcap HaliveCap rgt HinR HeqEdge.

    destruct_tuple HeqP HeqSrc HeqLbl HeqType HeqSched; simpl in *.

    (* cases on e [=|<>] src_ref 
       e [=] src_ref => further cases.
       e [<>] src_ref => all other mappings in S' are identical to S.*)

    case (Ref.eq_dec e src_ref); intros Hcase1.

    (* cases on i [=|<>] ind1.
       i [=] ind1 => cap [=] cap1 => Empty (Cap.rights cap1) => contradiction
       i [<>] ind1 => all other mappings in S' identical to S 
          Should have a theorem somewhere for this*)

    case (Ind.eq_dec i ind1); intros Hcase2.

    generalize( SC.getCap_eq  _ _ _ _ _ _ (Sys.eq_refl S) Hcase2 Hcase1); intros Heq.
    rewrite Hcap in Heq.
    unfold SC.getCap in Heq.
    unfold OC.getCap in Heq.
    unfold SC.getObj in Heq.
    unfold SC.getObjTuple in Heq.
    generalize (Sys_MapEquiv.exists_mapsTo_eq  _ _ (Sys.eq_sym HeqS) _ _ HmapS _ (Ref.eq_refl _));
       intros [[[[obj2 lbl2] typ2] sched2] [[[[Hobj2 Hlbl2] Htyp2] Hsched2] Hmap2]]; simpl in *.
    eapply Sys_Facts.find_mapsto_iff in Hmap2; rewrite Hmap2 in Heq; simpl in *.

    rewrite Hobj2 in HeqSrc.
    generalize (Obj_MapEquiv.exists_mapsTo_eq  _ _ (Obj.eq_sym HeqSrc) _ _ HmapSrc' _ (Ind.eq_refl _));
      intros [cap2 [Hcap2eq Hcap2Map]]; simpl in *.
    
    eapply Obj_Facts.find_mapsto_iff in Hcap2Map; rewrite Hcap2Map in Heq; simpl in *.
    rewrite <- Hcap2eq in Heq.

    eapply Cap.rights_eq in Heq.
    eapply Heq in HinR.
    eapply Hrights in HinR. contradiction.

    (* The next two cases should be nearly identical.
       As the capability motivating the addition of an edge has not been removed,
       the edge must still exist in the access graph *)

    (* first demonstrate that there is a label to our cap target, regardless of the object *)
    generalize (is_label_rmCap _ _ _ _ HS' (Cap.target cap1) cap_lbl); intros Hlabel.
    unfold SC.is_label in Hlabel.
    unfold SC.getLabel in Hlabel.
    generalize (Sys_MapEquiv.exists_mapsTo_eq  _ _ (Sys.eq_sym HeqS) _ _ HmapScap _ (Ref.eq_refl _));
      intros [[[[obj3 lbl3] typ3] sched3] [[[[Hobj3 Hlbl3] Htyp3] Hsched3] Hmap3]]; simpl in *.
    eapply Sys_Facts.find_mapsto_iff in Hmap3; simpl in *.
    unfold SC.getObjTuple in Hlabel.
    rewrite Hmap3 in Hlabel; simpl in Hlabel.
    eapply eq_sym in Hlbl3.
    destruct Hlabel as [Hlabel' _].
    generalize Hlbl3; intros Hlabel.
    eapply Hlabel' in Hlabel.
    clear Hlabel'.
    case (option_sumbool (Sys.MapS.find (Cap.target cap1) S')); intros HtargetObj;
      [|destruct HtargetObj as [[[[tobj tlbl] ttyp] tsched]  HtargetObj]]; rewrite HtargetObj in *; simpl in *; try contradiction.

    (* use our knowledge of e maping to src ... in s'' to reduce HS' *)
    unfold SC.rmCap in *.
    unfold SC.updateObj in HS'.
    unfold SC.addObjTuple in HS'.
    unfold SC.getObj in HS'.
    unfold SC.getObjTuple in HS'.
    generalize (Sys_MapEquiv.exists_mapsTo_eq  _ _ (Sys.eq_sym HeqS) _ _ HmapS _ (Ref.eq_sym Hcase1));
      intros [[[[obj2 lbl2] typ2] sched2] [[[[Hobj2 Hlbl2] Htyp2] Hsched2] Hmap2]]; simpl in *.
    eapply Sys_Facts.find_mapsto_iff in Hmap2; simpl in *.
    rewrite Hmap2 in HS'; simpl in HS'.

    (* generate an equivalent OC.rmCap i obj2 for the value of e in S'.*)

    generalize (Sys_MapEquiv.exists_mapsTo_eq _ _ HS'); intros HeqMap.
    generalize Sys.MapS.add_1; intros Hadd.
    eapply HeqMap in Hadd; try solve [apply eq_refl].
    destruct Hadd as [[[[obj2' lbl2'] typ2'] sched2'] [[[[Hobj2' Hlbl2'] Htyp2'] Hsched2'] HmapS']]; simpl in *.
    clear HeqMap.

    (* generate an equivalent cap1 in src *)
    edestruct (Obj_MapEquiv.exists_mapsTo_eq _ _ (Obj.eq_sym HeqSrc)) as [cap1' [HCapEq HmapSrc]];
      [apply HmapSrc' |  apply Ind.eq_refl | ].


    apply Hda'.
    apply_ex_intro_dirAcc S' S' e obj2' lbl2' typ2' sched2'  (OC.rmCap i src) lbl2 typ2 sched2 
    ind1 cap1' tobj tlbl ttyp tsched tobj tlbl ttyp tsched rgt;
    try solve [apply Sys.eq_refl | apply Sys.P.eq_refl| auto].

    do 3 (split; simpl; auto).
    apply Obj.eq_sym. eapply Obj.eq_trans. 2: apply Hobj2'.

    (* This has moved *)
    apply OC.removeCap_eq; auto.


    (* moving on to easy goals, top goal should go through by equivalence *)
    (* 2: do 3 (split; simpl; auto). *)
    (* 2: unfold OC.rmCap; *)
    (*   eapply Obj_MapEquiv.remove_m;  *)
    (*     solve [ eauto *)
    (*       | apply Obj.eq_sym; auto *)
    (*       | rewrite <- Hlbl2; rewrite HeqLbl; eauto]. *)

    rewrite <- Hlbl2.
    rewrite HeqLbl.
    rewrite <- Halive.
    eapply ObjectLabel.eq_refl.

    unfold OC.rmCap.
    eapply Obj_Facts.remove_neq_mapsto_iff; auto.


    eapply Sys_Facts.find_mapsto_iff in HtargetObj.
    eapply Sys_Facts.MapsTo_iff; [| apply HtargetObj].
    eapply Cap.target_eq; auto.

    rewrite Hlabel.
    destruct HeqPcap as [[[_ HeqCapLbl] _] _]; simpl in HeqCapLbl.
    rewrite HeqCapLbl.
    rewrite HaliveCap.
    apply ObjectLabel.eq_refl.

    eapply ARSet.eq_trans;
      [apply ARSet.eq_refl |
        apply Cap.rights_eq; apply Cap.eq_sym; apply HCapEq|
          auto].

    rewrite <- HeqEdge.
    eapply Edges.edge_equal; try solve[ apply Ref.eq_refl | apply AccessRight.eq_refl | apply Cap.target_eq; auto | auto] .

    (* Second similar case, a few steps will be skipped. *)


    (* first demonstrate that there is a label to our cap target, regardless of the object *)
    generalize (is_label_rmCap _ _ _ _ HS' (Cap.target cap1) cap_lbl); intros Hlabel.
    unfold SC.is_label in Hlabel.
    unfold SC.getLabel in Hlabel.
    generalize (Sys_MapEquiv.exists_mapsTo_eq  _ _ (Sys.eq_sym HeqS) _ _ HmapScap _ (Ref.eq_refl _));
      intros [[[[obj3 lbl3] typ3] sched3] [[[[Hobj3 Hlbl3] Htyp3] Hsched3] Hmap3]]; simpl in *.
    eapply Sys_Facts.find_mapsto_iff in Hmap3; simpl in *.
    unfold SC.getObjTuple in Hlabel.
    rewrite Hmap3 in Hlabel; simpl in Hlabel.
    eapply eq_sym in Hlbl3.
    destruct Hlabel as [Hlabel' _].
    generalize Hlbl3; intros Hlabel.
    eapply Hlabel' in Hlabel.
    clear Hlabel'.
    case (option_sumbool (Sys.MapS.find (Cap.target cap1) S')); intros HtargetObj;
      [|destruct HtargetObj as [[[[tobj tlbl] ttyp] tsched]  HtargetObj]]; rewrite HtargetObj in *; simpl in *; try contradiction.



    (* find the object i e in S *)
    case (option_sumbool (SC.getObjTuple e S)); intros HcaseT;
      [|destruct HcaseT as [[[[obj2 lbl2] typ2] sched2] HcaseT]];
        try solve [unfold SC.getCap in Hcap; unfold SC.getObj in Hcap; 
          rewrite HcaseT in Hcap; simpl in *; discriminate Hcap].
    
    (* reduce HS' *)
    unfold SC.rmCap in *.
    unfold SC.updateObj in HS'.
    unfold SC.addObjTuple in HS'.
    unfold SC.getObj in HS'.
    rewrite HcaseT in HS'; simpl in *.
    
    (* generate an equivalent obj2 for the value of src_ref in S'.*)

    generalize (Sys_MapEquiv.exists_mapsTo_eq _ _ (Sys.eq_sym HeqS) _ _ HmapS _ (eq_refl _)); 
      intros [[[[obj2'' lbl2''] typ2''] sched2''] [[[[Hobj2'' Hlbl2''] Htyp2''] Hsched2''] HeqSMap]]; simpl in *.
    generalize (Sys_MapEquiv.exists_mapsTo_eq _ _ HS'); intros HeqMap.
    generalize Sys.MapS.add_2; intros Hadd.
    eapply HeqMap in Hadd; [ clear HeqMap HeqSMap | eapply Hcase1 | apply HeqSMap| apply eq_refl].
    destruct Hadd as [[[[obj2' lbl2'] typ2'] sched2'] [[[[Hobj2' Hlbl2'] Htyp2'] Hsched2'] HmapS']]; simpl in *.
    

    (* generate an equivalent cap1 in src *)
    edestruct (Obj_MapEquiv.exists_mapsTo_eq _ _ (Obj.eq_sym HeqSrc)) as [cap1' [HCapEq HmapSrc]];
      [apply HmapSrc' |  apply Ind.eq_refl | ].

    apply Hda'.
    apply_ex_intro_dirAcc S' S' src_ref obj2' lbl2' typ2' sched2' src lbl srcType srcSched
    ind1 cap1' tobj tlbl ttyp tsched tobj tlbl ttyp tsched rgt;
    try solve [apply Sys.eq_refl | apply Sys.P.eq_refl| auto].

    do 3 (split; simpl; eauto).
    apply Obj.eq_sym. eapply Obj.eq_trans; [eauto | apply Hobj2'].
    



    
    rewrite HeqLbl.
    rewrite <- Halive.
    eapply ObjectLabel.eq_refl.

    eapply Sys_Facts.find_mapsto_iff in HtargetObj.
    eapply Sys_Facts.MapsTo_iff; [| apply HtargetObj].
    eapply Cap.target_eq; auto.

    rewrite Hlabel.
    destruct HeqPcap as [[[_ HeqCapLbl] _] _]; simpl in HeqCapLbl.
    rewrite HeqCapLbl.
    rewrite HaliveCap.
    apply ObjectLabel.eq_refl.

    eapply ARSet.eq_trans;
      [apply ARSet.eq_refl |
        apply Cap.rights_eq; apply Cap.eq_sym; apply HCapEq|
          auto].

    rewrite <- HeqEdge.
    eapply Edges.edge_equal; try solve[ apply Ref.eq_refl | apply AccessRight.eq_refl | apply Cap.target_eq; auto | auto] .

    (* I think the second half of this should be proved from rmCap is monotonic and dirAcc is monotonic.  
       This should exist in some form somewhere *)

  eapply dirAcc_rmCap_monotonic; eauto.

  Qed.

  Hint Resolve void_dirAcc_unchanged.


(* removing a void capability to any object does not alter any mutation *)
  Theorem void_irrelevant: 
    forall S D, DA.dirAcc_spec S D ->
    forall P, Seq.potAcc D P ->
    forall E M, mutable_spec P E M ->
    forall i o cap, SC.getCap i o S = Some cap ->
      ARSet.Empty (Cap.rights cap) ->
    forall S', Sys.eq (SC.rmCap i o S) S' ->
    forall D', DA.dirAcc_spec S' D' ->
    forall P', Seq.potAcc D' P' ->
    forall M', mutable_spec P' E M' ->
    RefSet.Equal M' M.
  Proof.
    intros S D Hda P Hpa E M Hm i o cap Hcap Hempty S' Hs' D' Hda' P' Hpa' M' Hm'.
    eapply mutable_spec_eq_iff; eauto; try apply RefSet.eq_refl.
    eapply potAcc_eq_iff; eauto; try apply AG.eq_refl.
  Qed.












  (* At this point, we focus on the notions of simply confined access grapns *)

  Definition subset_pred P A B := forall x, P A B x -> AG.In x A -> AG.In x B.

  Theorem subset_pred_subset :
    Proper ( (AG.Subset ==> AG.Subset --> Edge.eq ==> impl) --> AG.Subset --> AG.Subset ==> impl) subset_pred.
  Proof.
    unfold Proper; unfold respectful; unfold flip; unfold impl; unfold subset_pred.
    intros P P' Pimpl x0 y0 Hsub0 x1 y1 Hsub1 Hpred x2 P2' Hin.
    eapply Hsub1.
    eapply Hpred; [|apply Hsub0; auto].
    eapply Pimpl; eauto.
  Qed.

  Theorem Proper_subset_pred_P : forall f, Proper (AG.Subset ==> AG.Subset --> Edge.eq ==> impl) f -> 
    Proper (AG.eq ==> AG.eq ==> Edge.eq ==> iff) f.
  Proof.
    unfold Proper; unfold respectful; unfold impl.
    intros f P x y Heq x0 y0 Heq0 x1 y1 Heq1.
    split; intros Hf; eapply P; unfold flip.
    apply AGProps.subset_equal; eauto.
    apply AGProps.subset_equal; apply AG.eq_sym; eauto.
    eauto.
    apply Hf.
    apply AGProps.subset_equal; apply AG.eq_sym; eauto.
    apply AGProps.subset_equal; eauto.
    apply Edge.eq_sym; eauto.
    apply Hf.
  Qed.
  Hint Resolve Proper_subset_pred_P.

  Theorem subset_pred_eq : Proper ( (AG.eq ==> AG.eq ==> Edge.eq ==> iff) ==> AG.eq ==> AG.eq ==> iff) subset_pred.
  Proof.
    unfold Proper; unfold respectful; unfold subset_pred.
    intros P P' Peq x0 y0 Heq0 x1 y1 Heq1; split; 
      (intros Hsub x2 Hpred Hin;
        eapply Heq1; eapply Hsub; [eapply Peq; eauto| apply Heq0; auto]).
  Qed.
  Hint Resolve subset_pred_eq.

  Definition subset_eq_pred P A B := AG.Subset A B /\ subset_pred (fun B A => P A B) B A.

  Theorem subset_eq_pred_eq : 
    Proper ( (AG.eq ==> AG.eq ==> Edge.eq ==> iff ) ==> AG.eq ==> AG.eq ==> iff) subset_eq_pred.
  Proof.
    unfold Proper; unfold respectful.
    intros P P' Peq x0 y0 Heq0 x1 y1 Heq1.


    Ltac solve_tac Heq Heq' Heq2 :=  
      solve [apply Heq | apply AG.eq_sym; apply Heq 
        | apply Heq' | apply AG.eq_sym; apply Heq' 
        | apply Heq2 | apply Edge.eq_sym; apply Heq2].

    split; (intros [Hsub HP]; split;
      [rewrite Heq0 in *; rewrite Heq1 in *; auto
        | eapply subset_pred_eq;
          [ unfold respectful; intros x y Heq x' y' Heq' x2 y2 Heq2;
            solve [apply iff_sym; eapply Peq; solve_tac Heq Heq' Heq2 | eapply Peq; solve_tac Heq Heq' Heq2]
            | solve [apply AG.eq_sym ; eauto | eauto]
            | solve [apply AG.eq_sym ; eauto | eauto]
            | eauto ]]).
  Qed.


(* I find that we are trying to reason about mutability pointwise when describing Confinement. 
   TODO: consider going back to mutable and adding pointwise support *)

  Definition ag_ex_flow' A E o := RefSet.In o (mutable A E).

  Definition ag_flow' A e o :=
    Ref.eq e o \/
    AG.In (Edges.mkEdge e o tx) A \/
    AG.In (Edges.mkEdge e o wr) A \/
    AG.In (Edges.mkEdge o e wk) A \/
    AG.In (Edges.mkEdge o e rd) A.
   

 Theorem Proper_ag_flow'_eq :
    Proper (AG.eq ==> Ref.eq ==> Ref.eq ==> iff) ag_flow'.
  Proof.
    unfold Proper; unfold respectful; unfold ag_flow'.
    intros A A' HeqE e1 e1' Heq1 e2 e2' Heq2.
    try rewrite (Edges.eq_source _ _ Heq2); 
    try rewrite (Edges.eq_target _ _ Heq2);
    try rewrite (Edges.eq_right _ _ Heq2).
    try rewrite HeqE;
      try rewrite Heq1;
        try rewrite Heq2.
    intuition auto.
  Qed.

  Hint Resolve Proper_ag_flow'_eq.

  Theorem ag_flow'_dec : forall E x x',
    {ag_flow' E x x'} + {~ ag_flow' E x x'}.
  Proof.
    unfold ag_flow'.
    intros E x x'.
    Sumbool_decide; solve [eapply Ref.eq_dec | eapply AGProps.In_dec].
  Qed.

  Hint Resolve ag_flow'_dec.

  Theorem compat_P_ag_flow' : forall A x, SetoidList.compat_P Ref.eq ((fun e => ag_flow' A e x)).
  Proof.
    unfold SetoidList.compat_P.
    unfold Proper; unfold respectful; unfold impl. intros.
    eapply Proper_ag_flow'_eq;
      [eapply AG.eq_refl
        |eapply Ref.eq_sym; eauto
        |eapply Ref.eq_refl
        |eauto].
  Qed.

   Inductive ag_flow P a b : Prop := 
     | ag_flow_refl : Ref.eq a b -> ag_flow P a b
     | ag_flow_tx : AG.In (Edges.mkEdge a b tx) P -> ag_flow P a b
     | ag_flow_wr : AG.In (Edges.mkEdge a b wr) P -> ag_flow P a b
     | ag_flow_wk : AG.In (Edges.mkEdge b a wk) P -> ag_flow P a b
     | ag_flow_rd : AG.In (Edges.mkEdge b a rd) P -> ag_flow P a b.

   Hint Constructors ag_flow.

   Theorem ag_flow_iff_ag_flow' : forall P a b ,
     ag_flow' P a b <-> ag_flow P a b.
   Proof.
     unfold ag_flow'.
     split; [intuition auto| intro H; destruct H; intuition].
   Qed.

   Hint Immediate ag_flow_iff_ag_flow'.

   Theorem ag_flow_dec : forall P a b ,
     {ag_flow P a b} + {~ ag_flow P a b}.
   Proof.
     intros; eapply Sumbool_dec_iff_imp; eauto.
   Qed.

   Hint Resolve ag_flow_dec.

   (* This is basically mutable_maximal, phrased pointwise. *)
   Theorem maxTransfer_ag_flow_trans : forall P a b c ,
     Seq.maxTransfer P -> ag_flow P a b -> ag_flow P b c -> ag_flow P a c.
   Proof.
     intros P a b c Hmax Hab Hbc.
     destruct Hab as [Hab | Hab | Hab | Hab | Hab];
       destruct Hbc as [Hbc | Hbc | Hbc | Hbc | Hbc];
     eapply ag_flow_iff_ag_flow';
       try solve [try rewrite Hab in *; try rewrite Hbc in *; unfold ag_flow'; intuition].


     Ltac reduce_maxTrans Hmax trans_op :=
       eapply Hmax; [|eapply AGProps.Add_add; left; apply Edge.eq_refl];
         eapply trans_op; auto.
     
     (* send *)
     right; left.
     reduce_maxTrans Hmax Seq.transfer_send; [| apply Hbc].
     reduce_maxTrans Hmax Seq.transfer_send_reply; apply Hab.
     do 2 right; left.
     reduce_maxTrans Hmax Seq.transfer_send; [| apply Hbc].
     reduce_maxTrans Hmax Seq.transfer_send_reply; apply Hab.
     do 3 right; left.
     reduce_maxTrans Hmax Seq.transfer_weak; [ apply Hbc|].
     reduce_maxTrans Hmax Seq.transfer_send; [apply Hab |].
     reduce_maxTrans Hmax Seq.transfer_self_src; apply Hab.
     do 4 right.
     reduce_maxTrans Hmax Seq.transfer_read; [ apply Hbc|].
     reduce_maxTrans Hmax Seq.transfer_send; [apply Hab |].
     reduce_maxTrans Hmax Seq.transfer_self_src; apply Hab.
     
     (* write *)
     do 1 right; left.
     reduce_maxTrans Hmax Seq.transfer_write; [ | apply Hbc].
     reduce_maxTrans Hmax Seq.transfer_write; [ apply Hab| ].
     reduce_maxTrans Hmax Seq.transfer_self_src; apply Hab.
     do 2 right; left.
     reduce_maxTrans Hmax Seq.transfer_write; [ | apply Hbc].
     reduce_maxTrans Hmax Seq.transfer_write; [ apply Hab| ].
     reduce_maxTrans Hmax Seq.transfer_self_src; apply Hab.
     do 3 right; left.
     reduce_maxTrans Hmax Seq.transfer_weak; [ apply Hbc|].
     reduce_maxTrans Hmax Seq.transfer_write; [apply Hab |].
     reduce_maxTrans Hmax Seq.transfer_self_src; apply Hab.
     do 4 right.
     reduce_maxTrans Hmax Seq.transfer_read; [ apply Hbc|].
     reduce_maxTrans Hmax Seq.transfer_write; [apply Hab |].
     reduce_maxTrans Hmax Seq.transfer_self_src; apply Hab.

     (* weak *)
     do 3 right; left.
     reduce_maxTrans Hmax Seq.transfer_weak; [|apply Hab].
     reduce_maxTrans Hmax Seq.transfer_send; [apply Hbc|].
     reduce_maxTrans Hmax Seq.transfer_self_src; apply Hbc.
     do 3 right; left.
     reduce_maxTrans Hmax Seq.transfer_weak; [|apply Hab].
     reduce_maxTrans Hmax Seq.transfer_write; [apply Hbc|].
     reduce_maxTrans Hmax Seq.transfer_self_src; apply Hbc.
     do 3 right; left.
     reduce_maxTrans Hmax Seq.transfer_weak; [apply Hbc|apply Hab].
     do 3 right; left.
     reduce_maxTrans Hmax Seq.transfer_read; [apply Hbc|apply Hab].

     (* read *)
     do 4 right.
     reduce_maxTrans Hmax Seq.transfer_send; [apply Hbc|apply Hab].
     do 4 right.
     reduce_maxTrans Hmax Seq.transfer_write; [apply Hbc|apply Hab].
     do 3 right; left.
     eapply Hmax; [|eapply AGProps.Add_add; left; apply Edge.eq_refl];
         eapply Seq.transfer_weak;
           [apply Hbc
             |apply Hab
             |intuition
             |auto].
     do 4 right.
     reduce_maxTrans Hmax Seq.transfer_read; [apply Hbc|apply Hab].

   Qed.

   Hint Resolve maxTransfer_ag_flow_trans.

 Theorem Proper_ag_flow_eq :
    Proper (AG.eq ==> Ref.eq ==> Ref.eq ==> iff) ag_flow.
  Proof.
    unfold Proper; unfold respectful; intros.
    repeat progress rewrite <- ag_flow_iff_ag_flow'.
    eapply Proper_ag_flow'_eq; eauto; try apply Ref.eq_refl.
  Qed.

  Hint Resolve Proper_ag_flow_eq.

  (* Note, we can't use this form with generated code *)

  Theorem compat_P_ag_flow : forall A x, SetoidList.compat_P Ref.eq ((fun e => ag_flow A e x)).
  Proof.
    unfold SetoidList.compat_P.
    unfold Proper; unfold respectful; unfold impl; intros.
    rewrite <-  ag_flow_iff_ag_flow' in *.
    eapply compat_P_ag_flow'; eauto.
  Qed.

  Implicit Arguments compat_P_ag_flow [A x].

  Definition ag_ex_flow E A o := RefSet.Exists ((fun e => ag_flow A e o)) E.

  Theorem Proper_ag_ex_flow_eq : Proper (RefSet.eq ==> AG.eq ==> Ref.eq ==> iff) ag_ex_flow.
  Proof.
    unfold Proper; unfold respectful; unfold ag_ex_flow; unfold AG.Exists.
    intros x y H x0 y0 H0 x1 y1 H1.
    split;
    (intros [x2 [Hin Hconf]]; eapply ex_intro with x2; split; 
      [ rewrite H in *; eauto
        | generalize (AG.eq_sym H0) (Ref.eq_sym H1) (RefSet.eq_sym H); intros;
          eapply Proper_ag_flow_eq; eauto; try apply Ref.eq_refl]).
  Qed.
  Hint Resolve Proper_ag_ex_flow_eq.

  Theorem ag_ex_flow_dec : forall E A x, {ag_ex_flow E A x} + {~ ag_ex_flow E A x}.
  Proof.
    intros E A x. unfold ag_ex_flow.
    apply RefSetExists.exists_'; [intros x'; eapply ag_flow_dec|apply compat_P_ag_flow].
  Qed.
  Hint Resolve ag_ex_flow_dec.

  Definition ag_simply_confined E x :=
    ~ (Ref.eq (Edges.source x) (Edges.target x)) /\
    
    ~(RefSet.In (Edges.source x) E /\
      ~ RefSet.In (Edges.target x) E /\
      AccessRight.eq (Edges.right x) wk).

  Theorem Proper_ag_simply_confined_eq : Proper (RefSet.eq ==> Edge.eq ==> iff) ag_simply_confined.
  Proof.
    unfold Proper; unfold respectful; unfold flip; unfold impl;
      unfold ag_simply_confined.
    intros E E' HeqE edge edge' Heqe;
    rewrite (Edges.eq_source _ _ Heqe);
    rewrite (Edges.eq_target _ _ Heqe);
    rewrite (Edges.eq_right _ _ Heqe).

    generalize (RefSet.eq_sym HeqE) (Edge.eq_sym Heqe); intros HeqE' Heqe'.
    
    (* TODO: LTAC this *)

    split; intros [H1 H2].
    
    split; [try rewrite <- HeqE; eauto|].
    intros [Hnot1 Hnot2];
    apply H2; clear H2.
    rewrite HeqE; auto.

    split; [try rewrite <- HeqE; eauto|].
    intros [Hnot1 Hnot2];
    apply H2; clear H2.
    rewrite HeqE in *; auto.
  Qed.
  Hint Resolve Proper_ag_simply_confined_eq.


  Theorem ag_simply_confined_dec : forall E x, {ag_simply_confined E x} + {~ ag_simply_confined E x}.
  Proof.
    intros E x; unfold ag_simply_confined; Sumbool_decide; 
      try apply RefSetProps.In_dec; try apply Ref.eq_dec; try apply AccessRight.eq_dec; eauto.
  Qed.
  Hint Resolve ag_simply_confined_dec.

  Definition ag_confined E P x := 
    ~ (Ref.eq (Edges.source x) (Edges.target x)) /\

    ~(AccessRight.eq (Edges.right x) wk /\
      ( ag_ex_flow E P (Edges.source x) \/ ~ ag_ex_flow E P (Edges.target x))).


  Theorem Proper_ag_confined_eq : Proper (RefSet.eq ==> AG.eq ==> Edge.eq ==> iff) ag_confined.
  Proof.
    unfold Proper; unfold respectful; unfold flip; unfold impl;
      unfold ag_confined; unfold ag_simply_confined.
    intros E E' HeqE P P' HeqP edge edge' Heqe;
    rewrite (Edges.eq_source _ _ Heqe);
    rewrite (Edges.eq_target _ _ Heqe);
    rewrite (Edges.eq_right _ _ Heqe).

    generalize (RefSet.eq_sym HeqE) (AG.eq_sym HeqP) (Edge.eq_sym Heqe); intros HeqE' HeqP' Heqe'.
    
    (* TODO: LTAC this *)

    split; intros [H1 H2].
    
    split; [try rewrite <- HeqE; eauto|].
    intros [Hnot1 Hnot2];
    apply H2; clear H2.
    split; [auto|].
    destruct Hnot2 as [Hnot2 | Hnot2]; [left|right; intros Hnot2'; apply Hnot2];
       eapply Proper_ag_ex_flow_eq; eauto; apply Ref.eq_refl.

    split; [try rewrite <- HeqE; eauto|].
    intros [Hnot1 Hnot2];
    apply H2; clear H2.
    split; [auto|].
    destruct Hnot2 as [Hnot2 | Hnot2]; [left|right; intros Hnot2'; apply Hnot2];
       eapply Proper_ag_ex_flow_eq; eauto; apply Ref.eq_refl.
  Qed.
  Hint Resolve Proper_ag_confined_eq.

  Theorem ag_confined_dec : forall E P x, {ag_confined E P x} + {~ ag_confined E P x}.
  Proof.
    intros E P x; unfold ag_confined; Sumbool_decide; 
      try apply RefSetProps.In_dec; try apply Ref.eq_dec; try apply AccessRight.eq_dec; eauto.
  Qed.
  Hint Resolve ag_confined_dec.


(* The above decidability rules require interesting predicates *)
(* In particular, (exists y, P y) and (exists y, ~ P y) must both be decidable in set *)
(* This is true for FSets, but may not hold for other all structures. *)

  Definition ag_confined' E P x := 
    ~ (Ref.eq (Edges.source x) (Edges.target x)) /\
    (~ AccessRight.eq (Edges.right x) wk \/
      (~ ag_ex_flow E P (Edges.source x) /\ ag_ex_flow E P (Edges.target x))).

Theorem ag_confined_iff_ag_confined' : forall E A x,
  ag_confined E A x <-> ag_confined' E A x.
Proof.
  intros E A x.
  unfold ag_confined; unfold ag_confined'.
  

  generalize (RefSetProps.In_dec (Edges.source x) E); intros Pdec.
  (* AccessRight.eq_dec is automatically unfolding when we didn't ask it to. This is an inelegant fix*)
  unfold AccessRight.eq in *.
  generalize (AccessRight.eq_dec (Edges.right x) wk);
      intros Qdec.
  generalize (RefSetProps.In_dec (Edges.target x) E); intros Rdec.
  generalize (ag_ex_flow_dec E A (Edges.source x)); intros Sdec.
  generalize (ag_ex_flow_dec E A (Edges.target x)); intros Tdec.

  repeat progress (rewrite Sumbool_not_and; Sumbool_decide; eauto).
  repeat progress (rewrite <- Sumbool_dec_not_not_iff; Sumbool_decide; eauto).
  intuition.
  Qed.

  Definition subset_eq_ag_confined E A B:= subset_eq_pred (fun P _ => (ag_confined E P)) A B.

  Theorem subset_eq_ag_confined_eq :
    Proper (RefSet.eq ==> AG.eq ==> AG.eq ==> iff) subset_eq_ag_confined.
  Proof.
    unfold Proper; unfold respectful.
    intros x y Heq x0 y0 Heq0 x1 y1 Heq1.
    eapply subset_eq_pred_eq; eauto.
    unfold respectful.
    intros x2 y2 Heq2 x3 y3 Heq3 x4 y4 Heq4.
    eapply Proper_ag_confined_eq; eauto.
  Qed.

  Hint Resolve subset_eq_ag_confined_eq.

  Definition subset_eq_ag_simply_confined E A B := subset_eq_pred (fun _ _ => ag_simply_confined E) A B.

  Theorem subset_eq_ag_simply_confined_eq :
    Proper (RefSet.eq ==> AG.eq ==> AG.eq ==> iff) subset_eq_ag_simply_confined.
  Proof.
    unfold Proper; unfold respectful.
    intros x y Heq x0 y0 Heq0 x1 y1 Heq1.
    eapply subset_eq_pred_eq; eauto.
    unfold respectful.
    intros x2 y2 Heq2 x3 y3 Heq3 x4 y4 Heq4.
    eapply Proper_ag_simply_confined_eq; eauto.
  Qed.
  Hint Resolve subset_eq_ag_simply_confined_eq.


  Theorem ag_ex_flow_in : forall e E, RefSet.In e E -> forall A, ag_ex_flow E A e.
  Proof.
    intros.
    eapply ex_intro.
    split; eauto; apply ag_flow_refl; apply Ref.eq_refl.
  Qed.

  Hint Resolve ag_ex_flow_in.

  Theorem ag_confined_ag_simply_confined : forall E P x, ag_confined E P x -> ag_simply_confined E x.
  Proof.
    unfold ag_confined; unfold ag_simply_confined.
    intros E P x [Heq Hflow].
    split; auto.
    intros [Hs [Ht Hr]].
    apply Hflow.
    split; [auto| left].
    eauto.
  Qed.
  Hint Resolve ag_confined_ag_simply_confined.

  Theorem subset_eq_ag_simply_confined_ag_confined : forall E A B,
    subset_eq_ag_simply_confined E A B -> subset_eq_ag_confined E A B.
  Proof.
    unfold subset_eq_ag_simply_confined; unfold subset_eq_ag_confined; unfold subset_eq_pred.
    intros E A P [Hsub HsubP].
    split; auto.
    unfold subset_pred in *.
    intros x Hconf Hin.
    eapply HsubP; eauto.
  Qed.
  Hint Resolve subset_eq_ag_simply_confined_ag_confined.

  Theorem subset_eq_ag_confined_mutable:
    forall P P' E, subset_eq_ag_confined E P' P ->
    forall M, mutable_spec P E M ->
    forall M', mutable_spec P' E M' ->
      RefSet.Equal M M'.
  Proof.
    intros P P' E Hwkeq M Hm M' Hm' x.
    eapply iff_trans; [eapply Hm|clear Hm].
    eapply iff_sym; eapply iff_trans; [eapply Hm'|clear Hm'].
    destruct Hwkeq as [Hsub Hwksub].

    unfold ag_confined in *; unfold subset_pred in *.
    case (RefSetProps.In_dec x E); intros Hcase;
      (* If x in E, then we have one of our assumptions *)
      [split; intro H; left; assumption | ].
    (* solve when ~ x in E , remember to place x in E for a contradiction later.*)
    split;
      (intro H; destruct H as [H|H]; 
        [left; assumption 
          | right; destruct H as [e [Hin HinP]]]).
    (* solve P' -> P *)
    eapply ex_intro; split; [apply Hin|intuition].
    (* solve P -> P' *)

    destruct HinP as [HinP | [HinP | [HinP | HinP]]];
      try solve 
        [case (ag_ex_flow_dec E P' x); intros Hflow;
          [ destruct Hflow as [e' [Hin'  [Hflow' | Hflow' | Hflow' | Hflow' | Hflow']]];
            solve [rewrite Hflow' in *; contradiction
              | eapply ex_intro; intuition (solve [eapply Hin' | eapply Hflow'])]
            | eapply Hwksub in HinP;
              [eapply ex_intro; split; [eauto | intuition]
                | try rewrite Edges.source_rewrite in *;
                  try rewrite Edges.target_rewrite in *;
                    try rewrite Edges.right_rewrite in *;
                      split; 
                        [ intros Hneq; apply Hcase; first [rewrite Hneq | rewrite <- Hneq]; auto
                          | try solve [intros [Hneq1 Hneq2]; solve [discriminate| intuition eauto]]]]]].
  Qed.


  (* TODO: Some of these properties probably should live in Sequential Access 
     as they are more general than this proof *)

  Theorem add_potTrans_fn : forall A B x, AGProps.Add x A B ->
    exists Fadd, AG.Equal B (Fadd A) /\ Seq.ag_potTransfer_fn_req Fadd.
  Proof.
    intros.
    eapply ex_intro.
    split; [eapply AG.eq_sym; eapply AGAddEq.Add_add; eauto|].
    split; [eapply Seq.add_add_commute|].
    split; [unfold ag_nondecr; intros; eapply AGProps.subset_add_2; eauto|].
     unfold Seq.ag_equiv; intros; eapply AGFacts.add_m; eauto.
   Qed.

   (* NOTE:  subset_union_diff has moved to FSetAddEq *)

   Hint Resolve AGAddEq.subset_union_diff.

   (* TODO: Move to sequential access *)
   Theorem subset_potTransfer_fn_union_diff: forall A B, AG.Subset A B ->
     Seq.ag_potTransfer_fn_req (fun Z => (AG.union Z (AG.diff B A))).
   Proof.
     intros A B H.
     split.
     unfold Seq.ag_add_commute; intros ag ag' x Hedge.
     intros y.
     generalize (Hedge y); clear Hedge; intros Hedge.
     generalize (H y); intros Hy.
     generalize (H x); intros Hx.
       Ltac simple_solver_7 H1 :=      
         eapply AGFacts.union_iff in H1; destruct H1 as [H1 | H1]; [| apply AGFacts.diff_iff in H1]; 
           intuition; AGFacts.set_iff; auto.
     case (Edge.eq_dec x y); intros Heq;
     intuition (AGFacts.set_iff; auto); 
       solve [simple_solver_7 H1 | simple_solver_7 H4].

     split.
     unfold ag_nondecr; intros ag ag' Hsub.
     intros x Hin.
     generalize (Hsub x Hin); intros Hin'.
     AGFacts.set_iff; intuition.

     unfold Seq.ag_equiv; intros ag ag' Heq.
     rewrite Heq. auto.
   Qed.

   Hint Resolve subset_potTransfer_fn_union_diff.


   (* TODO: Move to sequential access *)
   Theorem subset_potTransfer_fn_union_diff2: forall A B, AG.Subset A B ->
     Seq.ag_potTransfer_fn_req (fun A => (AG.union A (AG.diff B A))).
   Proof.
     intros A B H.
     split.
     unfold Seq.ag_add_commute; intros ag ag' x Hedge.
     intros y.
     generalize (Hedge y); clear Hedge; intros Hedge.
     generalize (H y); intros Hy.
     generalize (H x); intros Hx.
     case (Edge.eq_dec x y); intros Heq;
     intuition (AGFacts.set_iff; auto); 
       solve [simple_solver_7 H1 | simple_solver_7 H4].

     split.
     unfold ag_nondecr; intros ag ag' Hsub.
     intros x Hin.
     generalize (Hsub x Hin); intros Hin'.
     AGFacts.set_iff; intuition.

     unfold Seq.ag_equiv; intros ag ag' Heq.
     rewrite Heq. auto.
   Qed.

   Hint Resolve subset_potTransfer_fn_union_diff2.


   (* TODO: Place in Sequential Access *)
   Theorem subset_potTrans_fn: forall A B, AG.Subset A B -> 
     exists Fadd, AG.Equal B (Fadd A) /\ Seq.ag_potTransfer_fn_req Fadd.
   Proof.
     intros.
     eapply ex_intro with (fun Z => (AG.union Z (AG.diff B A))); eauto.
   Qed.
     
   (* This theorem obviates a lot of others *)
   (* TODO: move to SequentialAccessImpl.v *)
   Theorem ag_potTransfer_fn_req_empty :
     forall Fa, Seq.ag_add_commute Fa -> Seq.ag_equiv Fa ->
       forall A, AG.Equal (Fa A) (AG.union A (Fa AG.empty)).
   Proof.
     intros Fa HaddComm Hequiv.
     eapply AGProps.set_induction.
     (* base *)
     intros s Hempty.
     eapply AGProps.empty_is_empty_1 in Hempty.
     intros x.
     generalize (Hequiv _ _ Hempty x); intros Heq.
     generalize (Hempty x).
     revert Heq.
     intuition (AGFacts.set_iff; auto).
     apply AGFacts.union_iff in H; intuition.
     eapply AGFacts.empty_iff in H; contradiction.
     (* step *)
     intros s s' IH x HninX Hadd.
     generalize (HaddComm _ _ _ Hadd); intros Hadd'.
     intros y.
     eapply iff_sym.
     eapply iff_trans.
     eapply AGFacts.union_iff.
     generalize (IH y); intros IHy.
     eapply iff_sym in IHy.
     eapply iff_trans in IHy; [| eapply iff_sym; eapply AGFacts.union_iff].
     generalize (Hadd y); clear Hadd; intros Hadd.
     generalize (Hadd' y); clear Hadd'; intros Hadd'.
     intuition auto.
   Qed.

   (* TODO: This obviates the need for ag_nondecr as a fn req. *)
   (* Fix in Sequential Access *)
   Theorem ag_add_commute_equiv_impl_monotonic :
     forall Fa, Seq.ag_add_commute Fa -> Seq.ag_equiv Fa ->
       ag_nondecr Fa.
   Proof.
     unfold ag_nondecr. intros Fa Hcomm Hequiv ag ag' Hsub.
     intros x Hin.
     eapply ag_potTransfer_fn_req_empty; [eauto | eauto |].
     AGFacts.set_iff.
     intuition eauto.
   Qed.


   (* Note the signature here on P has different variance from above.  P
      must consider this argument irrelevant to apply both rules *)
   (*  *)
   Theorem subset_pred_add_commute: forall Fadd, Seq.ag_add_commute Fadd -> Seq.ag_equiv Fadd ->
     forall P, Proper (AG.Subset --> AG.Subset --> Edge.eq ==> impl) P ->
     forall A B, subset_pred P A B -> 
       subset_pred P (Fadd A) (Fadd B).
   Proof.
     unfold subset_pred in *.
     intros Fa Hcomm Hequiv P Pproper A B Hpred x Px HinX.
     eapply ag_potTransfer_fn_req_empty; auto.
     eapply ag_potTransfer_fn_req_empty in HinX; auto.
     eapply AGFacts.union_iff.
     eapply AGFacts.union_iff in HinX.
     intuition auto.
     left.
     unfold Proper in *; unfold respectful in *; unfold flip in *; unfold impl in *.
     eapply Hpred; [|apply H].
     eapply Pproper; [| | apply Edge.eq_refl 
         | apply Px]; apply ag_add_commute_equiv_impl_monotonic; auto.
   Qed.

   Hint Resolve subset_pred_add_commute.

   Theorem subset_eq_pred_add_commute: forall Fadd, Seq.ag_add_commute Fadd -> Seq.ag_equiv Fadd ->
     forall P, Proper (AG.Subset --> AG.Subset --> Edge.eq ==> impl) P ->
     forall A B, subset_eq_pred P A B -> 
       subset_eq_pred P (Fadd A) (Fadd B).
   Proof.
     intros.
     destruct H2.
     unfold Proper in *; unfold respectful in *; unfold flip in *.
     split;
       solve [ eapply Seq.ag_subset_add_commute; eauto
         | eapply subset_pred_add_commute; eauto].
   Qed.


(*
   Theorem weak_subset_add_commute: forall Fadd, Seq.ag_add_commute Fadd -> Seq.ag_equiv Fadd ->
     forall A B E, weak_subset A E B -> weak_subset (Fadd A) E (Fadd B).
   Proof.
     unfold weak_subset; intros; auto.
   Qed.

   Hint Resolve weak_subset_add_commute.
*)


   (* Theorem subset_eq_ag_confined_add_commute: forall Fadd,  Seq.ag_add_commute Fadd -> Seq.ag_equiv Fadd -> *)
   (*   forall A B E, subset_eq_ag_confined E A B -> *)
   (*     subset_eq_ag_confined E (Fadd A) (Fadd B). *)
   (* Proof. *)
   (*   intros Fadd Hcomm Hequiv A B E [Hsub Hwksub]. *)
   (*   generalize (Seq.ag_subset_add_commute Hcomm Hequiv); intros Hsubcomm. *)
   (*   split; eauto. *)
   (*   eapply subset_pred_add_commute; eauto. *)
   (*   eapply Proper_irrel_subst_contravariant; *)
   (*   eapply Proper_irrel_ignore_contravariant. *)
   (*   apply ag_confined_sub; *)
   (*   apply RefSetProps.subset_equal; apply RefSet.eq_refl. *)
   (* Qed. *)

   (* Hint Resolve subset_eq_ag_confined_add_commute. *)


  (* This relies on the fact that potTrans commutes with Add 
     We might need to prove subset_eq_ag_confined has the ag_fn_req properties.*)

   (* Theorem subset_eq_ag_confined_potTrans_func : *)
   (*   forall Fa, Seq.ag_potTransfer_fn_req Fa -> *)
   (*   forall Fa', Seq.ag_potTransfer_fn_req Fa' -> *)
   (*   forall A, Seq.potTrans A (Fa A) -> *)
   (*   forall E, subset_eq_ag_confined E A (Fa' A) -> *)
   (*   Seq.potTrans (Fa' A) (Fa (Fa' A)) /\ subset_eq_ag_confined E (Fa A) (Fa (Fa' A)). *)
   (* Proof. *)
   (*   intros Fa Freq Fa' Freq' A Htrans E Hwkeq. *)
   (*   split; *)
   (*     solve [ *)
   (*       eapply Seq.potTrans_eq; *)
   (*         [eapply AG.eq_refl *)
   (*           | apply add_commute_increasing_transpose; unfold Seq.ag_potTransfer_fn_req in *; intuition *)
   (*           | apply Seq.potTrans_commute_monotonic; unfold Seq.ag_potTransfer_fn_req in *; intuition] *)
   (*       | eapply subset_eq_ag_confined_add_commute; unfold Seq.ag_potTransfer_fn_req in *; intuition]. *)
   (* Qed. *)

  (* This theorem, subset_eq_ag_confined_potTrans, could be formulated over a single A,
     and two functions Fa and Fa' satisfying ag_potTransfer_fn_req :
     (A':=A) (B' := (Fa A)) and (A := (Fa' A)) and (B := (Fa' (Fa A))). *)

  (* Theorem subset_eq_ag_confined_potTrans: *)
  (*   forall A' B', Seq.potTrans A' B' -> *)
  (*   forall A E, subset_eq_ag_confined E A' A -> *)
  (*   exists B, Seq.potTrans A B /\ subset_eq_ag_confined E B' B. *)
  (* Proof. *)
  (*   intros A' B' Htrans A E Hwkeq. *)

  (*   (* Find Fa and Fa' *) *)
  (*   generalize Hwkeq; intros [Hsub _]. *)
  (*   eapply subset_potTrans_fn in Hsub; destruct Hsub as [Fa' [Hequiv' Freq']]. *)
  (*   generalize (subset_potTrans_fn _ _ (Seq.potTrans_subset Htrans)); intros [Fa [Hequiv Freq]]. *)
    
  (*   (* solve for weak_eq_subset_potTrans_func *) *)
  (*   eapply Seq.potTrans_eq in Htrans; [ *)
  (*     | eapply AG.eq_refl *)
  (*     | eapply Hequiv]. *)
  (*   eapply subset_eq_ag_confined_eq in Hwkeq; [ *)
  (*     | apply RefSet.eq_refl *)
  (*     | apply AG.eq_refl *)
  (*     | apply AG.eq_sym; apply Hequiv']. *)
    
  (*   generalize (subset_eq_ag_confined_potTrans_func _ Freq _ Freq' _ Htrans _ Hwkeq). *)
  (*   intros [Htrans' Hwkeq']. *)

  (*   (* instantiate and solve *) *)
  (*   eapply ex_intro; split. *)
  (*   eapply Seq.potTrans_eq. *)
  (*   apply AG.eq_sym; apply Hequiv'. *)
  (*   apply AG.eq_refl. *)
  (*   apply Htrans'. *)
    
  (*   eapply subset_eq_ag_confined_eq. *)
  (*   apply RefSet.eq_refl. *)
  (*   apply Hequiv. *)
  (*   apply AG.eq_refl. *)
  (*   apply Hwkeq'. *)
  (* Qed. *)


      Ltac destruct_ag_confined Px := 
        let Px1 := fresh "Px1" in
          let Px2 := fresh "Px2" in
            destruct Px as [Px1 Px2].
      
      Ltac destruct_ag_confined' Px := 
        let Px1 := fresh "Px1" in
          let Px2 := fresh "Px2" in
              destruct Px as [Px1 Px2].

      Ltac edge_simpl := 
        try rewrite Edges.source_rewrite in *; try rewrite Edges.target_rewrite in *; 
          try rewrite Edges.right_rewrite in *.
      
      Ltac predicate_simpl Heq := 
        generalize (Edges.eq_source _ _ Heq) (Edges.eq_target _ _ Heq) (Edges.eq_right _ _ Heq); 
          let HeqS := fresh "HeqS" in let HeqR := fresh "HeqR" in let HeqT := fresh "HeqT" in 
            intros HeqS HeqT HeqR; try rewrite <- HeqS in *; try rewrite <- HeqT in *; try rewrite <- HeqR in *;
              edge_simpl; clear HeqS HeqR HeqT.


    Theorem subset_eq_ag_confined_trans_max:
      forall A B, Seq.transfer A B ->
        forall P, Seq.maxTransfer P ->
          forall E, subset_eq_ag_confined E P A ->
            subset_eq_ag_confined E P B.
    Proof.
      intros A B Htrans P Hmax E Hwkeq.
      destruct Hwkeq as [Hsub Hwksub].
      split.
      eapply AGProps.subset_trans;
        [apply Hsub
          | eapply Seq.transfer_subset; auto].

      unfold subset_pred in *. (* unfold ag_confined in *. *)
      intros x Px Hin.
      generalize (Hwksub _ Px); intros HwksubPx.
        (* destruct Px as [Px1 [Px2 [Px3 Px4]]]. *)

      destruct Htrans.
      
      (* src self *)
      destruct (H0 x) as [Hadd _].
      apply Hadd in Hin; clear Hadd; destruct Hin as [Heq|Hin]; try solve [intuition];
        destruct_ag_confined Px; predicate_simpl Heq.
      generalize (Px1 (Ref.eq_refl _)); contradiction.

      (* src tgt, same *)
      destruct (H0 x) as [Hadd _].
      apply Hadd in Hin; clear Hadd; destruct Hin as [Heq|Hin]; try solve [intuition];
        destruct_ag_confined Px; predicate_simpl Heq.
      generalize (Px1 (Ref.eq_refl _)); contradiction.

      (* read *)
      Ltac preamble H1 x Hin Px :=
        let Hadd := fresh "Hadd" in
        let Heq := fresh "Heq" in 
      destruct (H1 x) as [Hadd _];
      apply Hadd in Hin; clear Hadd;
      destruct Hin as [Heq|Hin]; try solve [intuition];

      rewrite ag_confined_iff_ag_confined' in Px;
      unfold ag_confined' in Px;
      destruct_ag_confined' Px;
      predicate_simpl Heq.

      preamble H1 x Hin Px.
      

      (* if src = tgt, then we are reading from ourself, and the edge we read is already in A placing it in P *)
         
      case (Ref.eq_dec src tgt); intros Hcase1; 
        [rewrite Hcase1 in *;eapply HwksubPx; eapply AGFacts.In_eq_iff; [apply Edge.eq_sym; apply Heq | auto]|].
      (* We know src <> tgt *)

      (* place (src tgt read) in P *)

      eapply Hwksub in H; [|
        rewrite ag_confined_iff_ag_confined'; unfold ag_confined'; predicate_simpl Heq;
          split; [eauto | solve [intuition discriminate]]].

      (* if tgt = tgt', then we are reading a reflexive edge. 
         By H, this edge must be in P, and so too must (tgt tgt' rgt) *)

      case (Ref.eq_dec tgt tgt'); intros Hcase2.
      rewrite Hcase2 in *;
      eapply Hmax;
        [ eapply Seq.transfer_read;
          [ apply H
            | eapply Hmax;
              [eapply Seq.transfer_self_tgt;
                [ apply H
                  | apply AGProps.Add_add]
                | apply AGProps.Add_add; eauto]
            | apply AGProps.Add_add]
          | apply AGProps.Add_add; eauto].
      (* tgt <> tgt' *)

      Ltac solution_1 Hwksub H0 Heq Hmax H trans_op:=
      eapply Hwksub in H0; [
      | rewrite ag_confined_iff_ag_confined';
        unfold ag_confined'; unfold ag_ex_flow; unfold AG.Exists;
          predicate_simpl Heq; split; intuition eauto];

      (* place the edge in P by trans_op *)
      eapply Hmax;
        [ eapply trans_op;
          [ apply H
            | apply H0
            | apply AGProps.Add_add]
          | apply AGProps.Add_add; eauto].

      (* By cases on access right.  If it is not weak, (tgt tgt' rgt) in P*)
      case (AccessRight.eq_dec rgt wk); intros HcaseRight;
        [rewrite HcaseRight in *;
          destruct Px2 as [Px2 | Px2]; try solve [contradict Px2; apply AccessRight.eq_refl] |
            solution_1 Hwksub H0 Heq Hmax H Seq.transfer_read].

      (* rgt= wk *)
      destruct Px2 as [Pxsrc Pxtgt'].


      (* there must also not be a flow from E to tgt.  If there were, this would violate the lack of flow to src.*)
      case (ag_ex_flow_dec E P tgt) as [[e [HinE Hflow]] | Hflow];
        [ contradict Pxsrc; eapply ex_intro; split; eauto
          | solution_1 Hwksub H0 Heq Hmax H Seq.transfer_read].

      (* write *)
      preamble H1 x Hin Px.

      (* if src = tgt, then we are writing to ourself, and the edge we write is already in A placing it in P *)
         
      case (Ref.eq_dec src tgt); intros Hcase1; 
        [rewrite Hcase1 in *;eapply HwksubPx; eapply AGFacts.In_eq_iff; [apply Edge.eq_sym; apply Heq | auto]|].
      (* We know src <> tgt *)

      (* place (src tgt write) in P *)

      eapply Hwksub in H; [|
        rewrite ag_confined_iff_ag_confined'; unfold ag_confined'; predicate_simpl Heq;
          split; [eauto | solve [intuition discriminate]]].

      (* if src = tgt', then we are creating a reflexive edge. 
         By H, this edge must be in P, and so too must (tgt tgt' rgt) *)

      case (Ref.eq_dec src tgt'); intros Hcase2.
      rewrite Hcase2 in *.

      eapply Hmax;
        [ eapply Seq.transfer_write;
          [ apply H
            | eapply Hmax;
              [eapply Seq.transfer_self_src;
                [ apply H
                  | apply AGProps.Add_add]
                | apply AGProps.Add_add; eauto]
            | apply AGProps.Add_add]
          | apply AGProps.Add_add; eauto].
      
      (* src <> tgt' *)

      (* By cases on access right.  If it is not weak, (tgt tgt' rgt) in P*)
      case (AccessRight.eq_dec rgt wk); intros HcaseRight;
        [rewrite HcaseRight in *;
          destruct Px2 as [Px2 | Px2]; try solve [contradict Px2; apply AccessRight.eq_refl] |
            solution_1 Hwksub H0 Heq Hmax H Seq.transfer_write].

      (* rgt = wk *)
      destruct Px2 as [Pxtgt Pxtgt'].

      (* there must also not be a flow from E to tgt.  If there were, this would violate the lack of flow to src.*)
      case (ag_ex_flow_dec E P src) as [[e [HinE Hflow]] | Hflow];
        [ contradict Pxtgt; eapply ex_intro; split; eauto
          | solution_1 Hwksub H0 Heq Hmax H Seq.transfer_write].

      (* send *)
      preamble H1 x Hin Px.

      (* if src = tgt, then we are writing to ourself, and the edge we write is already in A placing it in P *)
         
      case (Ref.eq_dec src tgt); intros Hcase1; 
        [rewrite Hcase1 in *;eapply HwksubPx; eapply AGFacts.In_eq_iff; [apply Edge.eq_sym; apply Heq | auto]|].
      (* We know src <> tgt *)

      (* place (src tgt read) in P *)

      eapply Hwksub in H; [|
        rewrite ag_confined_iff_ag_confined'; unfold ag_confined'; predicate_simpl Heq;
          split; [eauto | solve [intuition discriminate]]].

      (* if src = tgt', then we are creating a reflexive edge. 
         By H, this edge must be in P, and so too must (tgt tgt' rgt) *)

      case (Ref.eq_dec src tgt'); intros Hcase2.
      rewrite Hcase2 in *.

      eapply Hmax;
        [ eapply Seq.transfer_send;
          [ apply H
            | eapply Hmax;
              [eapply Seq.transfer_self_src;
                [ apply H
                  | apply AGProps.Add_add]
                | apply AGProps.Add_add; eauto]
            | apply AGProps.Add_add]
          | apply AGProps.Add_add; eauto].
      

      (* src <> tgt' *)

      (* By cases on access right.  If it is not weak, (tgt tgt' rgt) in P*)
      case (AccessRight.eq_dec rgt wk); intros HcaseRight;
        [rewrite HcaseRight in *;
          destruct Px2 as [Px2 | Px2]; try solve [contradict Px2; apply AccessRight.eq_refl] |
            solution_1 Hwksub H0 Heq Hmax H Seq.transfer_send].

      (* rgt = wk *)
      destruct Px2 as [Pxtgt Pxtgt'].

      (* there must also not be a flow from E to tgt.  If there were, this would violate the lack of flow to src.*)
      case (ag_ex_flow_dec E P src) as [[e [HinE Hflow]] | Hflow];
        [ contradict Pxtgt; eapply ex_intro; split; eauto
          | solution_1 Hwksub H0 Heq Hmax H Seq.transfer_send].
 
      (* send self *)
      preamble H0 x Hin Px.

      (* if src = tgt, then we are writing to ourself, and the edge we write is already in A placing it in P *)
         
      case (Ref.eq_dec src tgt); intros Hcase1; 
        [rewrite Hcase1 in *;eapply HwksubPx; eapply AGFacts.In_eq_iff; [apply Edge.eq_sym; apply Heq | auto]|].
      (* We know src <> tgt *)

      (* place (src tgt read) in P *)

      eapply Hwksub in H; [|
        rewrite ag_confined_iff_ag_confined'; unfold ag_confined'; predicate_simpl Heq;
          split; [eauto | solve [intuition discriminate]]].

      (* Apply maxTransfer and trans_send_self to show (src tgt' rgt) in P *)
      eapply Hmax;
        [ eapply Seq.transfer_send_reply;
          [ apply H
            | apply AGProps.Add_add]
          | apply AGProps.Add_add; eauto].

      (* weak *)

      preamble H2 x Hin Px.

      (* if tgt = tgt', we are reading from a reflexive edge, which is already in A placing it in P. *)
      case (Ref.eq_dec tgt tgt'); intros Hcase2;
        [rewrite Hcase2 in *;eapply HwksubPx; eapply AGFacts.In_eq_iff; [apply Edge.eq_sym; apply Heq | auto]|].

      (* tgt [<>] tgt' *)

      (* eliminate nonsensical case. *)
      destruct Px2 as [Px2 | [Pxsrc Pxtgt']]; [contradict Px2; apply AccessRight.eq_refl|].


      (* first by cases on (ag_ex_flow E P tgt) *)

      case (ag_ex_flow_dec E P tgt); intros HflowTgt.
      (* we can show a flow contradiction if src [=] tgt *)
      case (Ref.eq_dec src tgt); intros Hcase1; [rewrite Hcase1 in *; contradict Pxsrc; eauto|].

      (* This places (src tgt weak) In P. *)
      eapply Hwksub in H; [|
        rewrite ag_confined_iff_ag_confined'; unfold ag_confined'; predicate_simpl Heq;
          split; [eauto | solve [intuition discriminate]]].

      (* we now have a flow contradiction.  There is a flow to src in P, which can not happen *)
      destruct HflowTgt as [e [HinE Hflow]]; contradict Pxsrc; eapply ex_intro; eauto.

      (* ~ ag_ex_flow E P tgt *)

      (* we can place (tgt tgt' rgt) In P *)
      eapply Hwksub in H0; [|
        rewrite ag_confined_iff_ag_confined'; unfold ag_confined'; predicate_simpl Heq;
          split; [eauto | solve [intuition discriminate]]].

      (* However this forms another flow contradiction, because there is a flow to tgt' *)
      destruct Pxtgt' as [e [HinE Hflow]].
      contradict HflowTgt.
      destruct H1; rewrite H1 in *;
        (eapply ex_intro; split; [apply HinE| eapply maxTransfer_ag_flow_trans; [auto| apply Hflow| eauto]]).
    Qed.


  (* The trouble with subset_eq_ag_confined_potTrans_func is, while it identifies
     the element that we can potTrans to, we do not yet know that that value is maximal. 
     This covers the other half of the problem. *)

  Theorem subset_eq_ag_confined_potTransfer_max:
    forall B D, Seq.potTransfer B D ->
    forall P, Seq.maxPotTransfer P ->
    forall E, subset_eq_ag_confined E P B ->
      subset_eq_ag_confined E P D.
  Proof.
    intros B D Htrans P Hmax E Hwkeq.
    induction Htrans as [C Heq | D C Htrans IH Htrans'].
    (* base *)
    eapply subset_eq_ag_confined_eq;
      [ eapply RefSet.eq_refl
        | eapply AG.eq_refl
        | eapply AG.eq_sym; apply Heq
        | auto].
    (* step *)
    clear Hwkeq Htrans B.
    eapply Seq.maxTransfer_maxPotTransfer in Hmax.

    eapply subset_eq_ag_confined_trans_max; eauto.
  Qed.
    
  (* 
     Here, D is the maximally authorized access graph, and D' is the 
     union of the confined access graph and the maximal one.
     *)
  Theorem dirAcc_confined : 
    forall E D D', subset_eq_ag_simply_confined E D D' ->
    forall P, Seq.potAcc D P ->
    forall P', Seq.potAcc D' P' ->
    forall M, mutable_spec P E M ->
    forall M', mutable_spec P' E M' ->
    RefSet.eq M M'.
  Proof.
    intros E D D' Hsc P Hp P' Hp' M Hm M' Hm'.
    (* Apply subset_eq_ag_confined_mutable to reduce the problem to potential access *)
    eapply RefSet.eq_sym.
    eapply subset_eq_ag_confined_mutable; [| eauto | eauto].
    (* Break apart the potential access definitions*)
    destruct Hp as [HpTrans HpMax]; destruct Hp' as [Hp'Trans Hp'Max].
    (* use Hsc to show that D [<=] D', and introduce I as an intermediate to P' using potTransfer_subset_lub *)

    generalize Hsc; intros [Hd'Eq _];
      generalize (subset_potTransfer_fn_union_diff _ _ Hd'Eq); intros Hd'Fadd;
      eapply AGAddEq.subset_union_diff in Hd'Eq;  set (Dx := (AG.diff D' D)) in *.
    generalize HpTrans; intros HpEq; eapply Seq.potTransfer_subset in HpEq;
      generalize (subset_potTransfer_fn_union_diff _ _ HpEq); intros HpFadd;
      eapply AGAddEq.subset_union_diff in HpEq; set (Px := (AG.diff P D)) in *.
    set (I := AG.union (AG.union D Px) Dx).



    (* use subset_eq_ag_confined_potTransfer_max to reduce from P' to I *)
    apply subset_eq_ag_confined_potTransfer_max with (B:=I); [|eauto|].

    eapply Seq.potTransfer_lub with (a:=I) in Hp'Trans. 


      destruct Hp'Trans as [P'2 [Hp'2TransP Hp'2TransI]];
        eapply Hp'Max in Hp'2TransP;
          eapply Seq.potTransfer_eq;
            [apply AG.eq_refl
              | apply AG.eq_sym; eauto
              | eauto].

      unfold I; eapply Seq.potTransfer_eq;
      [ apply AG.eq_sym; apply Hd'Eq
        | apply AG.eq_refl
        | eapply (Seq.potTransfer_commute_monotonic Hd'Fadd); eapply Seq.potTransfer_eq; eauto
      ].

    (* Reduce the complexity to ag_simply_confined *)
    Ltac respectful_covariant_ag_simply_confined :=
      do 2 (eapply Proper_irrel_subst_covariant; eapply Proper_irrel_ignore_covariant); eauto;
        eapply Proper_ag_simply_confined_eq; apply RefSet.eq_refl.
    Ltac respectful_contravariant_ag_simply_confined :=
      do 2 (eapply Proper_irrel_subst_contravariant; eapply Proper_irrel_ignore_contravariant); eauto;
        eapply Proper_ag_simply_confined_eq; apply RefSet.eq_refl.

    eapply subset_eq_ag_simply_confined_ag_confined.
    unfold I.
    eapply subset_eq_pred_eq; 
      [ respectful_covariant_ag_simply_confined
        | eapply HpEq
        | rewrite AGProps.union_assoc; rewrite (AGProps.union_sym Px); 
          rewrite <- AGProps.union_assoc; apply AG.eq_refl
        | 
      ].

    eapply subset_eq_pred_add_commute with (Fadd := (fun Z => AG.union Z Px));
      [eapply HpFadd
        | eapply HpFadd
        | do 2 (eapply Proper_irrel_subst_contravariant; eapply Proper_irrel_ignore_contravariant); eauto;
          unfold Proper; unfold respectful; unfold impl; intros;
            eapply Proper_ag_simply_confined_eq;
              [ apply RefSet.eq_refl
                | apply Edge.eq_sym; apply H
                | auto]
        | ].
    
    eapply subset_eq_pred_eq; 
      [ respectful_covariant_ag_simply_confined
        | apply AG.eq_refl
        | apply AG.eq_sym; apply Hd'Eq
        | apply Hsc 
      ].
  Qed.


  (* We now turn our attention to comparing defining the notion of a fully authorized accessgraph and
     demonstrating that the union of this graph and the confined graph is simply confined over the 
     fully authorized access graph. *)

 Import CapS.

  Definition ag_authorized_src C src acc := CapSet.fold (ag_add_cap src) C acc.
  Definition ag_authorized E C := RefSet.fold (ag_authorized_src C) E AG.empty.

  Definition excluded_edge E edge := ~ RefSet.In (Edges.source edge) E /\ ~ RefSet.In (Edges.target edge) E.
  
  Theorem excluded_edge_dec: forall E edge, {excluded_edge E edge} + {~ excluded_edge E edge}.
    Proof.
      intros.
      unfold excluded_edge.
      Sumbool_decide; apply RefSetProps.In_dec.
    Qed.

    Hint Resolve excluded_edge_dec.

    Theorem Proper_excluded_edge: Proper (RefSet.eq ==> Edge.eq ==> iff) excluded_edge.
    Proof.
      unfold excluded_edge; unfold Proper; unfold respectful; intros; split; intros H';
        (rewrite H in *; rewrite (Edges.eq_source _ _ H0) in *; rewrite (Edges.eq_target _ _ H0) in *; auto).
    Qed.

  Definition ag_remainder I E := AG.filter (fun edge => true_bool_of_sumbool (excluded_edge_dec E edge)) I.

  Definition ag_fully_authorized I E C :=
    AG.union 
    (AG.union 
      (Seq.complete_ag E)
      (ag_authorized E C))
    (ag_remainder I E).

  Definition cap_edge tgt rgt cap := 
    Ref.eq (Cap.target cap) tgt /\ 
    ARSet.In rgt (Cap.rights cap).

  Definition exists_cap_edge tgt rgt C:= 
    (CapSet.Exists (cap_edge tgt rgt) C).

  Definition ag_fully_authorized_spec I E C A := forall edge,
    AG.In edge A <-> 
    ((RefSet.In (Edges.source edge) E /\ RefSet.In (Edges.target edge) E) \/ 
      (RefSet.In (Edges.source edge) E /\
        exists_cap_edge (Edges.target edge) (Edges.right edge) C) \/
      AG.In edge I /\ excluded_edge E edge ).
    
  Definition ag_authorized_spec E C A := forall edge, 
    AG.In edge A <-> 
    RefSet.In (Edges.source edge) E /\
    exists_cap_edge (Edges.target edge) (Edges.right edge) C.
  
  Definition ag_authorized_src_spec C src I A := forall edge, 
    AG.In edge A <-> 
    AG.In edge I \/
    (Ref.eq src (Edges.source edge) /\
      exists_cap_edge (Edges.target edge) (Edges.right edge) C).
      
    Theorem ag_authorized_src_spec_iff : forall C src I, 
      ag_authorized_src_spec C src I (ag_authorized_src C src I).
    Proof.
      intros C src I; unfold ag_authorized_src_spec; unfold ag_authorized_src;
        unfold exists_cap_edge; unfold cap_edge; unfold CapSet.Exists; intros edge.
      eapply CapSetProps.fold_rec_bis.
      (* equiv *)
      intros s s' a Heq H.
      eapply iff_trans; [ apply H|].
      split; (intros H'; destruct H' as [HinI | [HeqSrc [cap [HinCap [HeqTgt HinRgt]]]]];
        [left;auto
          |right; split; [auto| eapply ex_intro with cap]; intuition; rewrite Heq in *; auto]).
      (* base *)
      split; intros H; try solve [intuition].
      destruct H as [HinI | [HeqSrc [cap [HinCap [HeqTgt HinRgt]]]]]; 
        solve [intuition | apply CapSetFacts.empty_iff in HinCap; contradiction].
      (* step *)
      intros cap A' C' HcapIn HcapNin IH.
      eapply iff_trans. eapply ag_add_cap_spec. apply AG.eq_refl.
      rewrite IH; clear IH.
      split; intros H.
      Ltac ag_authorized_src_solve_cap_in_case cap := 
        split; [intuition|eapply ex_intro with cap; intuition (try solve [eapply CapSetProps.Add_add; auto])].
      destruct H as [[HeqSrc [HeqTgt HinRgt]] | [HinI | [HeqSrc [cap' [HeqTgt' HinRgt']]]]]; 
        [right ; ag_authorized_src_solve_cap_in_case cap
          |intuition|right ;  ag_authorized_src_solve_cap_in_case cap'].
      destruct H as [HinI | [HeqSrc [cap' [HinCap' [HeqTgt' HinRgt']]]]]; [intuition |].
      case (Cap.eq_dec cap cap'); intros Hcase;
       [rewrite Hcase in *; rewrite (Cap.target_eq _ _ Hcase) in *; rewrite (Cap.rights_eq _ _ Hcase) in *;
         intuition
           | do 2 right; ag_authorized_src_solve_cap_in_case cap'; apply CapSetProps.Add_add in HinCap';
             intuition].
    Qed.

  Theorem ag_authorized_spec_iff : forall E C, ag_authorized_spec E C (ag_authorized E C).
  Proof.
    unfold ag_authorized_spec; unfold ag_authorized; 
      unfold exists_cap_edge; unfold CapSet.Exists; unfold cap_edge;  
        intros E C edge.
    eapply RefSetProps.fold_rec_bis.
    (* equiv *)
    intros refset refset' acc Heq H.
    eapply iff_trans; [apply H| clear H].
    split; (intros H'; destruct H' as [HinSrc [cap [HinCap [HeqTgt HinRgt]]]];
      rewrite Heq in *; split; [auto|apply ex_intro with cap; intuition auto]).
    (* base *)
    split; intros Hnot;
    solve [apply AGFacts.empty_iff in Hnot; contradiction 
      | destruct Hnot as [Hnot _]; apply RefSetFacts.empty_iff in Hnot; contradiction].
    (* step *)
    intros src acc E' HinE HninE' IH.
    eapply iff_trans; [apply ag_authorized_src_spec_iff |].
    rewrite IH; clear IH.
    intuition; try solve [ apply RefSetProps.Add_add; auto ].
    apply RefSetProps.Add_add in H0; intuition.
  Qed.

  Definition ag_remainder_spec I E A := forall edge, AG.In edge A <->
    AG.In edge I /\ excluded_edge E edge.

  Theorem ag_remainder_spec_iff : forall I E,
    ag_remainder_spec I E (ag_remainder I E).
  Proof.
    unfold ag_remainder_spec; intros I E edge.
    unfold ag_remainder; rewrite AGFacts.filter_iff.
    intuition.
    apply true_bool_of_sumbool_l in H1; auto.
    unfold true_bool_of_sumbool; apply proof_r_true_bool_of_sumbool; auto.
    eapply compat_P_compat_bool_true_bool_of_sumbool.
    split; 
      [unfold Reflexive; eapply Edge.eq_refl
        | unfold Symmetric; eapply Edge.eq_sym
        | unfold Transitive; eapply Edge.eq_trans].
    unfold SetoidList.compat_P; unfold Proper; unfold respectful; unfold impl; intros;
      eapply Proper_excluded_edge; [| | apply H0]; try apply RefSet.eq_refl; eauto.

  Qed.

  Theorem ag_fully_authorized_spec_iff :forall I E C,
    ag_fully_authorized_spec I E C (ag_fully_authorized I E C).
  Proof.
    unfold ag_fully_authorized_spec; intros I E C edge.
    unfold ag_fully_authorized.
    AGFacts.set_iff.
    rewrite (ag_remainder_spec_iff I E edge).
    rewrite (ag_authorized_spec_iff E C edge).
    rewrite (Seq.complete_ag_spec_complete_ag E edge).
    intuition.
  Qed.


  (* 
     Like an constructive subsystem, an constructive access graph is one where
     all edges targeting E are elements of E.
     *)
     
  Definition ag_constructive_P E edge := 
    ~ RefSet.In (Edges.source edge) E /\ 
    RefSet.In (Edges.target edge) E.

  Theorem ag_constructive_P_dec : forall E edge, {ag_constructive_P E edge} + {~ ag_constructive_P E edge}.
  Proof.
    unfold ag_constructive_P; intros E edge.
    Sumbool_decide; eauto; eapply RefSetProps.In_dec.
  Qed.

  Theorem Proper_ag_constructive_P: Proper (RefSet.eq ==> Edge.eq ==> iff) ag_constructive_P.
  Proof.
    unfold Proper; unfold respectful; unfold ag_constructive_P; intros.
    split; intros;
    rewrite H in *; rewrite (Edges.eq_source _ _ H0) in *; rewrite (Edges.eq_target _ _ H0) in *;  intuition eauto.
  Qed.

  Definition ag_constructive E A : Prop := ~ AG.Exists (ag_constructive_P E) A.

  Theorem ag_constructive_dec : forall E A, {ag_constructive E A} + {~ ag_constructive E A}.
  Proof.
    unfold ag_constructive. intros E A.
    Sumbool_decide.
    edestruct AGDep.exists_ as [H|H]; [eapply ag_constructive_P_dec| left|right];
      (eapply H; unfold SetoidList.compat_P;
        unfold Proper; unfold respectful; unfold impl; intros; eapply Proper_ag_constructive_P; 
          [ apply RefSet.eq_refl | apply Edge.eq_sym; eauto | apply H1]).
Qed.

  Hint Resolve ag_constructive_dec.


  Theorem constructive_subsystem_impl_ag : 
    forall E S, Sub.constructive_subsystem E S -> 
    forall D, dirAcc_spec S D ->
      ag_constructive E D.
  Proof.
    unfold ag_constructive; unfold AG.Exists; unfold ag_constructive_P;
      unfold Sub.constructive_subsystem; unfold RefSet.For_all. 
    intros E S Hsub D Hda.
    rewrite not_exists_iff. intros edge.
    eapply Sumbool_not_and; Sumbool_decide; eauto; try apply AGProps.In_dec; try apply RefSetProps.In_dec. 
    rewrite Sumbool_not_and; Sumbool_decide; eauto; try apply RefSetProps.In_dec.
    rewrite <- (Edges.edge_rewrite edge);
    generalize (Edges.source edge) (Edges.target edge) (Edges.right edge); intros src tgt rgt; clear edge.
    rewrite Edges.source_rewrite; rewrite Edges.target_rewrite.
    case (RefSetProps.In_dec src E); intros HinSrc; [ intuition eauto|].
    case (RefSetProps.In_dec tgt E); intros HinTgt; [| intuition eauto].
    left.

    generalize (Hsub _ HinTgt); intros [Hextant Hauto]; clear Hsub.
    unfold Sub.extant_test in *.
    rewrite Sub.constructive_test_iff' in *; unfold Sub.constructive_test' in *.
    intros Hin; apply Hauto; clear Hauto.
    apply Hda in Hin.
    destruct_dirAcc Hin s' HeqS src_ref1 src1 lbl1 srcType1 srcSched1 HmapS1 
    src1' lbl1' srcType1' srcSched1' HeqP Halive ind cap HmapSrc'
    cap_obj cap_lbl cap_type cap_sched HmapScap cap_obj' cap_lbl' cap_type' cap_sched'
    HeqPcap HaliveCap rgt1 HdaR HeqEdge.
    destructEdgeEq HeqEdge (Edges.mkEdge src tgt rgt) HeqS' HeqT' HeqR'.
    apply ex_intro with src.
    
    eapply Sys_MapEquiv.exists_mapsTo_eq in HmapS1;
      [| eapply Sys.eq_sym; apply HeqS | apply HeqS'].
    destruct HmapS1 as [tuple [Heq Hmap]].
    destruct_tuple tuple src'' lbl'' typ'' sch''; simpl in *.
    destruct_tuple Heq HsrcEq HlblEq HtypEq HschEq.
    eapply Sys.MapS.find_1 in Hmap. 
    destruct_tuple HeqP HeqSrc1 HeqLbl1 HeqTyp1 HeqSch1; simpl in *.
    eapply Obj_MapEquiv.exists_mapsTo_eq in HmapSrc';
      [ |
        eapply Obj.eq_trans;
        [apply Obj.eq_sym; apply HeqSrc1 | apply HsrcEq]
        | apply Ind.eq_refl].
    destruct HmapSrc' as [cap' [HcapEq HcapMap]].



    do 2 eapply ex_intro.
    split.
    unfold SC.getCap; unfold SC.getObj;unfold SC.getObjTuple.

    erewrite Hmap; simpl.
    unfold OC.getCap.
    eapply Obj.MapS.find_1.
    apply HcapMap.

    split.
    unfold SC.is_alive; unfold SC.is_label; unfold SC.getLabel; unfold SC.getObjTuple.
    rewrite Hmap; simpl.
    rewrite <- HlblEq.
    rewrite HeqLbl1.
    rewrite <- Halive; apply ObjectLabel.eq_refl.

    split.
    auto.
    eapply Ref.eq_trans.
    eapply Ref.eq_sym; apply HeqT'.
    apply Cap.target_eq.
    auto.
Qed.


  (* TODO: Move all complete_AG_dec material to Sequential Access *)

  Definition complete_AG'_tgt A src tgt := 
    ARSet.Exists (fun rgt => ~ AG.In (Edges.mkEdge src tgt rgt) A) all_rights.

  Theorem Proper_complete_AG'_tgt : Proper (AG.eq ==> Ref.eq ==> Ref.eq ==> iff) complete_AG'_tgt.
  Proof.
    unfold Proper; unfold respectful; unfold complete_AG'_tgt; unfold ARSet.Exists; 
      intros; split; intros [z [Hin Hp]];
        (eapply ex_intro with z; split; try tauto;
          rewrite H in *; rewrite H0 in *; rewrite H1 in *; tauto).
  Qed.

  Hint Resolve Proper_complete_AG'_tgt.

  Theorem complete_AG'_tgt_dec: forall A src tgt, {complete_AG'_tgt A src tgt} + {~complete_AG'_tgt A src tgt}.
  Proof.
    intros. unfold complete_AG'_tgt.
    ecase ARSetDep.exists_; intros H; [eapply Sumbool_dec_not; eapply AGProps.In_dec | left | right];
      (eapply H; clear H;
    unfold SetoidList.compat_P; unfold Proper; unfold respectful; unfold impl; intros; rewrite H in *; tauto).
  Qed.

  Hint Resolve  complete_AG'_tgt_dec.

  Definition complete_AG'_src E A src := 
    RefSet.Exists (complete_AG'_tgt A src) E.

  Theorem Proper_complete_AG'_src : Proper (RefSet.eq ==> AG.eq ==> Ref.eq ==> iff) complete_AG'_src.
  Proof.
    unfold Proper; unfold respectful; unfold complete_AG'_src; unfold RefSet.Exists;
      intros; split; intros [z [Hin Hp]];
        (eapply ex_intro with z; rewrite H in *; split; try tauto;
          eapply Proper_complete_AG'_tgt; [| | | apply Hp];
    solve [apply H0|apply AG.eq_sym; apply H0 | apply H1|apply Ref.eq_sym; apply H1 |  apply Ref.eq_refl]).
  Qed.

  Hint Resolve Proper_complete_AG'_src.
  
  Theorem complete_AG'_src_dec: forall E A src, {complete_AG'_src E A src} + {~ complete_AG'_src E A src}.
  Proof.
    intros.
    ecase (RefSetDep.exists_ (complete_AG'_tgt_dec A src)); intros H; [left|right]; apply H; clear H;
    unfold SetoidList.compat_P; unfold Proper; unfold respectful; unfold impl; intros; rewrite H in *; intuition.
  Qed.

  Hint Resolve complete_AG'_src_dec.
      
  Definition complete_AG' E A :=
    ~ RefSet.Exists (complete_AG'_src E A) E.

  Theorem Proper_complete_AG': Proper (RefSet.eq ==> AG.eq ==> iff) complete_AG'.
  Proof.
    unfold Proper; unfold respectful; unfold complete_AG'; unfold RefSet.Exists;
      intros; split; intros Hneg [z [Hin Hp]]; apply Hneg; clear Hneg;
        (eapply ex_intro with z; split; [rewrite H in *; tauto|];
          eapply Proper_complete_AG'_src; [| | | apply Hp];
    solve [apply H0 | apply AG.eq_sym; apply H0 | apply H | apply RefSet.eq_sym; apply H | apply Ref.eq_refl]).
  Qed.

  Hint Resolve Proper_complete_AG'.

  Theorem complete_AG'_dec : forall E A, {complete_AG' E A} + {~ complete_AG' E A}.
  Proof.
    intros; unfold complete_AG'.
    Sumbool_decide; eauto.
    ecase (RefSetDep.exists_ (complete_AG'_src_dec E A)); intros H; [left|right]; eapply H; clear H;
    unfold SetoidList.compat_P; unfold Proper; unfold respectful; unfold impl; intros; rewrite H in *; intuition.
  Qed.

  Hint Resolve complete_AG'_dec.

  Theorem complete_AG_iff': forall E A, Seq.complete_AG E A <-> complete_AG' E A.
  Proof.
    intros E A; unfold complete_AG'; unfold complete_AG'_src; unfold complete_AG'_tgt;
      unfold Seq.complete_AG; unfold RefSet.Exists; unfold ARSet.Exists;
      split; intros H.
    intros [src [Hsrc [tgt [Htgt [rgt [Hrgt Hin]]]]]]; apply Hin; clear Hin.
    apply H; tauto.
    intros src tgt rgt Hsrc Htgt.
    rewrite not_exists_iff in H; generalize (H src); clear H; intros H.
    rewrite Sumbool_not_and in H; Sumbool_decide; auto.
    destruct H as [H|H]; [contradiction|].
    rewrite not_exists_iff in H; generalize (H tgt); clear H; intros H.
    rewrite Sumbool_not_and in H; Sumbool_decide; auto.
    destruct H as [H|H]; [contradiction|].
    rewrite not_exists_iff in H; generalize (H rgt); clear H; intros H.
    rewrite Sumbool_not_and in H; Sumbool_decide; auto; try apply AGProps.In_dec.
    destruct H as [H|H].
    contradiction (in_all_rights rgt).
    apply Sumbool_dec_not_not_iff in H; try apply AGProps.In_dec; auto.
  Qed.

  Theorem complete_AG_dec : forall E A, {Seq.complete_AG E A} + {~ Seq.complete_AG E A}.
  Proof.
    intros.
    eapply Sumbool_dec_iff_imp; [|apply iff_sym;  apply complete_AG_iff']; eauto.
  Qed.


  Theorem cap_edge_dec : forall tgt rgt cap, {cap_edge tgt rgt cap } + {~ cap_edge tgt rgt cap}.
  Proof.
    intros tgt rgt cap.
    unfold cap_edge; Sumbool_decide; solve [ apply Ref.eq_dec | apply ARSetProps.In_dec].
  Qed.

  Theorem Proper_cap_edge: Proper (Ref.eq ==> AccessRight.eq ==> Cap.eq ==> iff) cap_edge.
  Proof.
    unfold Proper; unfold respectful; unfold cap_edge; intros; split; intros [H'1 H'2];
      (rewrite H in *; rewrite H0 in *; 
        rewrite (Cap.rights_eq _ _ H1) in *; rewrite (Cap.target_eq _ _ H1) in *;
          intuition).
  Qed.

  Theorem Proper_exists_cap_edge : 
    Proper (Ref.eq ==> AccessRight.eq ==> CapSet.eq ==> iff) exists_cap_edge.
  Proof.
    unfold Proper; unfold respectful; intros; split; intros H';
      (destruct H' as [cap [H'1 [H'2 H'3]]]; eapply ex_intro with cap;
        rewrite H0 in *; rewrite H in *; rewrite H1 in *; unfold cap_edge; intuition).
  Qed.


  Theorem exists_cap_edge_dec : forall tgt rgt C, {exists_cap_edge tgt rgt C} + {~exists_cap_edge tgt rgt C}.
  Proof.
    unfold exists_cap_edge; intros tgt rgt C.
    ecase (CapSetDep.exists_ (cap_edge_dec tgt rgt)); intros H; [left|right]; apply H;
    (unfold SetoidList.compat_P; unfold Proper; unfold respectful; unfold impl;
      intros x y Heq Hcapedge;
        eapply Proper_cap_edge; [ apply Ref.eq_refl | apply AccessRight.eq_refl| | eapply Hcapedge]; eauto).
  Qed.

  Hint Resolve exists_cap_edge_dec.

  Theorem ag_constructive_fully_authorized : forall I E C A, ag_fully_authorized_spec I E C A -> ag_constructive E A.
  Proof.
    intros I E C A H Hnot. 
    destruct Hnot as [edge [Hin [Hsrc Htgt]]].
    eapply H in Hin; clear H.
    unfold excluded_edge in *; intuition.
  Qed.

  Theorem confined_subsystem_outward_edge_ag_simply_confined : 
    forall C E S, Sub.confined_subsystem C E S ->
      forall D, dirAcc_spec S D ->
        forall A, ag_fully_authorized_spec D E C A ->
          forall edge, ag_simply_confined E edge ->
            ~ AG.In edge A ->
            AG.In edge D -> 
            RefSet.In (Edges.source edge) E ->
            ~ RefSet.In (Edges.target edge) E ->
            False.
  Proof.
    intros C E S HsubConf D Hda A Ha edge HsimpConf HinA HinD HsrcIn HtgtIn.
    destruct HsimpConf as [Hneq Hrgt].
    do 2 (rewrite Sumbool_not_and in Hrgt; Sumbool_decide; auto; try apply AccessRight.eq_dec;
      destruct Hrgt as [Hrgt | Hrgt]; [contradiction|]).
    unfold Sub.confined_subsystem in *.
    generalize (HsubConf (Edges.source edge) HsrcIn); intros [Hextant [Hauto Hconf]]; clear HsubConf.
    rewrite Sub.confinement_test_iff' in Hconf; unfold Sub.confinement_test' in *.
      (* rewrite HinA using Ha and simplify *)
    erewrite (Ha edge) in HinA; clear Ha.
    rewrite Sumbool_not_or in HinA; Sumbool_decide; eauto.
      (* The first clause of HinA is redundant information *)
    destruct HinA as [_ HinA].
    rewrite Sumbool_not_or in HinA; Sumbool_decide; eauto.
      (* The last clause of HinA is not applicable as we are an outward edge *)
    destruct HinA as [Hauth _].
      (* simplify Hauth *)
    rewrite Sumbool_not_and in Hauth; Sumbool_decide; eauto.
    destruct Hauth as [Hauth | Hauth]; [contradiction|].
    unfold exists_cap_edge in Hauth; unfold CapSet.Exists in Hauth.
    rewrite not_exists_iff in Hauth; simpl in *.
    unfold cap_edge in *.
    
      (* destruct dirAcc *)
    eapply Hda in HinD.
    destruct_dirAcc HinD s'' HeqS src_ref src lbl srcType srcSched HmapS 
    src' lbl' srcType' srcSched' HeqP Halive ind cap HmapSrc'
    cap_obj cap_lbl cap_type cap_sched HmapScap cap_obj' cap_lbl' cap_type' cap_sched' 
    HeqPcap HaliveCap rgt HinR HeqEdge.
    unfold Sub.confinement_pred in *.

    generalize (Hauth cap); clear Hauth; intros Hauth.

      (* at this point, we know (source edge) [=] src_ref /\
         (target edge) [=] (target cap) /\
         getCap i src_ref S = Some cap /\
         rgt [=] (right edge) /\
         In rgt (rights cap) /\
         right edge) [<>] weak 

         instantiating o := src_ref, i := ind, cap := cap,
         
         *)


      (* Find the tuple for getcap *)
    generalize (Sys_MapEquiv.exists_mapsTo_eq _ _ (Sys.eq_sym HeqS) _ _ HmapS _ (Ref.eq_refl _));
      intros [tuple [HtupleEq HtupleMap]].
    destruct_tuple tuple src2 lbl2 typ2 sch2; simpl in *.
    destruct_tuple HtupleEq HeqObj2 HeqLbl2 HeqTyp2 HeqSch2.
    eapply Sys.MapS.find_1 in HtupleMap.
      (* find the cap for getcap *)
    destruct_tuple HeqP HeqSrc HeqLbl HeqTyp HeqSch; simpl in *.
    rewrite HeqSrc in HeqObj2.
    generalize (Obj_MapEquiv.exists_mapsTo_eq _ _ HeqObj2 _ _ HmapSrc' _ (Ind.eq_refl _));
      intros [cap' [Hcap'Eq Hcap'Map]].
    eapply Obj.MapS.find_1 in Hcap'Map.

    apply Hconf.
    eapply ex_intro with src_ref;
      eapply ex_intro with ind;
        eapply ex_intro with cap'.

    split.
    unfold SC.getCap.
    unfold SC.getObj.
    unfold SC.getObjTuple.
    unfold OC.getCap. 
    rewrite HtupleMap; simpl; rewrite Hcap'Map; simpl; auto.

    generalize (Edges.eq_source _ _ HeqEdge); rewrite Edges.source_rewrite; intros HsrcEdge.
    generalize (Edges.eq_right _ _ HeqEdge); rewrite Edges.right_rewrite; intros HedgeRgt.
    generalize (Edges.eq_target _ _ HeqEdge); rewrite Edges.target_rewrite; intros HedgeTgt.

    split; [ auto |].
    intros Hnot.
      (* This is cases on Hnot.
         (rights cap') [=] (singleton weak) /\ in (target ca') E:
           we know cap [=] cap' and In rgt (rights cap) making rgt [=] weak.
           But we have assumed ~ rgt [=] weak.
         Empty (rights cap'):
           we know cap [=] cap' and In rgt (rights cap), making this impossible.
         In (target cap') E:
           we know (target cap') [=] (target cap) and (target cap) [=] (target edge) and
           ~ RefSet.In (Edges.target edge) E, making this impossible.
         In cap' C:
           cap [=] cap' -> In cap C and
           rgt [=] (right edge) -> In (right edge) (rights cap) and
           (target cap') [=] (target cap)
           solving our 3 requirements. *)

    destruct Hnot as [HcapIn | [HtargetIn | [Hempty | [HisAlive | [HeqRights HinTgt]]]]].
    apply Hauth.
    rewrite <- Hcap'Eq in HcapIn.
    split; [auto| split; [auto|rewrite <- HedgeRgt; auto]].
    
    apply HtgtIn; rewrite <- HedgeTgt;
      rewrite (Cap.target_eq _ _ Hcap'Eq); auto.
    
    eapply Hempty; rewrite <- (Cap.rights_eq _ _ Hcap'Eq); apply HinR.

    apply HisAlive.
    eapply SC.isLabel_eq.
    eapply Cap.target_eq; eapply Hcap'Eq.
    eapply ObjectLabel.eq_sym; eapply ObjectLabel.eq_trans;
      [eapply HaliveCap 
        | destruct_tuple HeqPcap HeqPcapObj HeqPcapLbl HeqPcapTyp HeqPcapSch; simpl in *;
          eapply ObjectLabel.eq_sym; eapply HeqPcapLbl].
    eapply Sys.eq_sym; apply HeqS.
    eapply Sys.MapS.find_1 in HmapScap; 
      unfold SC.is_alive; unfold SC.is_label; unfold SC.getLabel; unfold SC.getObjTuple; 
        rewrite HmapScap; simpl; apply ObjectLabel.eq_refl.

    apply Hrgt.
    rewrite <- HedgeRgt.
    rewrite <- (Cap.rights_eq _ _ Hcap'Eq) in HeqRights.
    rewrite HeqRights in HinR.
    eapply ARSetFacts.singleton_iff in HinR.
    rewrite <- HinR.
    apply AccessRight.eq_refl.
  Qed.

  Hint Resolve confined_subsystem_outward_edge_ag_simply_confined.

    Theorem constructive_confined_subsystem:
      forall C E S, Sub.confined_subsystem C E S -> Sub.constructive_subsystem E S.
    Proof.
      unfold Sub.confined_subsystem; unfold Sub.constructive_subsystem; unfold RefSet.For_all; intros C E S H x Hin.
      generalize (H _ Hin); clear H; intros H.
      intuition.
    Qed.

    Hint Resolve constructive_confined_subsystem.

    Theorem inner_edge_ag_simply_confined : 
      forall D E C A, ag_fully_authorized_spec D E C A ->
        forall edge,
          RefSet.In (Edges.source edge) E ->
          RefSet.In (Edges.target edge) E ->
          AG.In edge A.
    Proof.
      intros D E C A Ha edge HsrcIn HtgtIn.
      eapply Ha; clear Ha; intuition.
    Qed.

    Hint Resolve inner_edge_ag_simply_confined.

  Theorem confined_subsystem_inward_edge_ag_simply_confined : 
    forall C E S, Sub.confined_subsystem C E S ->
      forall D, dirAcc_spec S D ->
          forall edge, AG.In edge D ->
            ~ RefSet.In (Edges.source edge) E ->
            RefSet.In (Edges.target edge) E ->
            False.
  Proof.
    intros C E S HsubConf D Hda edge HinD HsrcIn HtgtIn.
    eapply constructive_subsystem_impl_ag in Hda; [|eauto].
    unfold ag_constructive in *; unfold ag_constructive_P in *.
    apply Hda; apply ex_intro with edge; intuition.
  Qed.

  Hint Resolve confined_subsystem_inward_edge_ag_simply_confined.

  Theorem confined_subsystem_outter_edge_ag_simply_confined : 
    forall D E C A, ag_fully_authorized_spec D E C A ->
      forall edge,  AG.In edge D -> 
        ~ RefSet.In (Edges.source edge) E ->
        ~ RefSet.In (Edges.target edge) E ->
        AG.In edge A.
  Proof.
    intros D E C A Ha edge HinD Hsrc Htgt.
    eapply Ha. clear Ha.
    unfold excluded_edge; intuition.
  Qed.

  Hint Resolve confined_subsystem_outter_edge_ag_simply_confined.

  Theorem confined_subsystem_impl_ag_subset_simply_confined :
    forall C E S, Sub.confined_subsystem C E S ->
    forall D, dirAcc_spec S D ->
    forall A, ag_fully_authorized_spec D E C A ->
    subset_eq_ag_simply_confined E A (AG.union D A).
  Proof.
    intros C E S HsubConf D Hda A Ha.
    unfold subset_eq_ag_simply_confined. unfold subset_eq_pred.
    split.
    unfold AG.Subset; intros.
    AGFacts.set_iff; intuition.
    unfold subset_pred; simpl; intros edge Hconf.
    AGFacts.set_iff. 
    case (AGProps.In_dec edge A); intros HinA; try solve [intuition].
    intros [Hin|Hin]; try solve [intuition].
    (* At this point, we break the proof into 4 cases based on:
       (In_dec (source edge) E) and (In_dec (target edge) E).
       Inner   : by Ha being complete.
       Outward : Main Proof: Confinement test
       Inward  : A and D are ag_constructive over E, no such edge exists.
       Outter  : By Ha preserving remainder.
       *)

    case (RefSetProps.In_dec (Edges.source edge) E); intros Hsrc;
      (case (RefSetProps.In_dec (Edges.target edge) E); intros Htgt);
      [eauto | assert False; [eauto | contradiction] | assert False; [eauto | contradiction] | eauto].

  Qed.

  Theorem confined_subsystem_mutable:
    forall C E S, Sub.confined_subsystem C E S ->
    forall D, dirAcc_spec S D ->
    forall A, ag_fully_authorized_spec D E C A ->
    forall P, Seq.potAcc D P ->
    forall P', Seq.potAcc A P' ->
    forall M, mutable_spec P E M ->
    forall M', mutable_spec P' E M' ->
    RefSet.Subset M M'.
  Proof.
    intros C E S HsubConf D Hda A Ha P Hpa P' Hpa' M Hm M' Hm'.
    generalize (Seq.exists_potAcc (AG.union D A)); intros [P2 Hpa2].
    generalize (confined_subsystem_impl_ag_subset_simply_confined _ _ _ HsubConf _ Hda _ Ha); intros HsimpConf.
    generalize (mutable_spec_mutable P2 E); generalize (mutable P2 E); intros M2 Hm2.
    generalize (dirAcc_confined _ _ _ HsimpConf _ Hpa' _ Hpa2 _ Hm' _ Hm2); intros Heq2.
    rewrite Heq2.
    eapply mutable_spec_subset;
      [apply RefSetProps.subset_refl | | apply Hm2 |  apply Hm].
    eapply Seq.potAcc_monotonic;
      [ | apply Hpa | apply Hpa2].
    eapply AGProps.union_subset_1.
  Qed.

  Theorem test : forall (A B C:Prop), {A} + {~A} -> (((A /\ B) <-> (A /\ C)) <-> (~ A \/ (B <-> C))).
  Proof.
    intros; destruct H;  tauto.
  Qed.
 
  Theorem Sumbool_dec_not_iff_pos : forall A B (HdecA : {A}+{~A}) (HdecB: {B}+{~B}), (A <-> B) -> (~A <-> ~ B).
  Proof.
    intros; tauto.
  Qed.

  Theorem Sumbool_dec_not_iff_neg : forall A B (HdecA : {A}+{~A}) (HdecB: {B}+{~B}), (~A <-> ~B) -> (A <-> B).
  Proof.
    intros; tauto.
  Qed.

  Theorem Sumbool_dec_not_iff_iff : forall A B (HdecA : {A}+{~A}) (HdecB: {B}+{~B}), (A <-> B) <-> (~A <-> ~B).
  Proof.
    intros; tauto.
  Qed.


 (* 
     Finally, all fully authorized subsystems are mutably equal.
     The only difference between fully authorized subsystems of shape E are elements of E.



Theorem mutable_project_in:
forall p, Seq.maxTransfer p ->
forall objs, Seq.ag_objs_spec p objs ->
forall N, RefSet.Subset objs N ->
forall E, RefSet.Subset E N ->
forall a, RefSet.In a N ->
forall o, ~ RefSet.In o N -> 
forall p', AG_project a o p p' ->
forall m, mutable_spec p E m -> RefSet.In a m ->
forall m', mutable_spec p' m m' -> 
forall E', RefSetProps.Add o m E' ->
RefSet.Subset m' E'.

This definition of mutable_project_in may not be strong enough to prove equality.
Actually, it might.  We know: m' [<=] m + o /\ m [<=] m' 
This doesn't ensure that o is in m', only that it might be.

     The goal is to say (fully quantified):
     ag_objs_spec D N ->
     N [<=] N' ->
     ~ Empty E ->
     E [<=] N' ->
     ~ Empty E' ->
     E' [<=] N' ->
     N - E [=] N - E' ->
     ag_fully_authorized D E' C A' ->
     ag_fully_authorized D E C A ->
     potAcc A P ->
     potAcc A' P' ->
     mutable_spec P E M ->
     mutable_spec P' E' M' ->
     M - E [=] M' - E'.

     Given these constraints, we can always select N' [=] (union N (union E E')).
     
     We will probably need to show :
     forall D E C A, ag_fully_authorized D E C A -> (ag_objs A) [=] union (ag_objs D) E.

     This is what is really drinving the selection of N' as (union N (union E E').

     This proof probably wants to be in three parts.  Induction from E down to a singleton, singletone
     substitution, and then induction back to E' from that singleton.  The inductions are the same theorem,
     instantiated with different instances of Subset.  The singleton swap is proabably different.

     Both Inductions, instantiate E with any singleton:
     ag_objs_spec D N ->
     N [<=] N' ->
     E' [<=] N' ->
     E [<=] E' ->
     ~ Empty E ->
     N - E [=] N - E' ->
     ag_fully_authorized D E' C A' ->
     ag_fully_authorized D E C A ->
     potAcc A P ->
     potAcc A' P' ->
     mutable_spec P E M ->
     mutable_spec P' E' M' ->
     M - E [=] M' - E'.

     Singleton swap, initial rewrite:
     ag_objs_spec D N ->
     N [<=] N' ->
     In e N' ->
     In e' N' ->
     N - (singleton e) [=] N - (singleton e') ->
     ag_fully_authorized D (singleton e) C A' ->
     ag_fully_authorized D (singleton e') C A ->
     potAcc A P ->
     potAcc A' P' ->
     mutable_spec P E M ->
     mutable_spec P' E' M' ->
     M - (singleton e) [=] M' - (singleton e').

     forall o, In o (N - {e}) <-> In o (N - {e'})
     forall o, (In o N /\ ~ In o {e}) <-> (In o N /\ ~ In o {e'})
     forall o, (In o N /\ ~ o [=] e) <-> (In o N /\ ~ o [=] e')
     
     Because (In o N) is decidable in Set, we know the following rewrite holds
     forall o, ~ In o N \/ (~ o [=] e <-> ~ o [=] e)

     Singleton swap, final version:
     ag_objs_spec D N ->
     N [<=] N' ->
     In e N' ->
     In e' N' ->
     (forall n, ~In n N \/ (~ n [=] e <-> ~ n [=] e' )) ->
     ag_fully_authorized D (singleton e) C A' ->
     ag_fully_authorized D (singleton e') C A ->
     potAcc A P ->
     potAcc A' P' ->
     mutable_spec P E M ->
     mutable_spec P' E' M' ->
     forall m, ((In m M /\ ~ m [=] e) <-> (In m M' /\ ~ m [=] e'))

     Since all operations are symmetric, we can prove the helper function using -> and apply it twice.
     We can simplify the final goal as:
     forall m, In m M -> ~ m [=] e -> In m M' /\ ~ m [=] e'

     This breaks into two very simple proofs by (Ref.eq_dec e e')
     If e [=] e', then the proof is solved by reflexivity as all judgments are equivalence preserving.

     If ~ e [=] e, it must be the case that they are also ~ In N.  
     The only difference in the ag_objs of A and A' is e and e'.
     Therefore, when ~ m [=] e, we know there must be an edge defining a flow in P.
     The definition of ag_fully_authorized preserves all objects outside of E.
     The complete accessgraph of a singleton is covered by reflexivity of trans and may be ignored.
     This means that the difference between A' and A is a substitution of e for e'.
     This substituion is preserved by potAcc, and therefore must cause this edge to exist for e'.
     
     What we are really after is a notion of substituion for access graphs and proofs
     that this substitution is preserved for mutability and potAcc.
     
     


     
     We do not ensure that we are not projecting into the dead space as it is irrelevant for the problem.
     We only ensure that we are not expanding into already existing objs.

     The induction for this is over the elements of (E' - E).  
     For each of these, there is obviously AG_project e e' p p' forming a lineage from P to P'.
     By mutable_project, or mutable_project_in, these are clearly the same thing.

     The various setoid_* tactics will not operate on dependent instances of respectful_hetero, so there
     is little reason to attept to craft one by hand.

     *)

Theorem ag_ex_flow_iff_ag_ex_flow' : forall E P o, ag_ex_flow E P o <-> ag_ex_flow' P E o.
Proof.
  intros E P o.
  unfold ag_ex_flow; unfold ag_ex_flow'; unfold RefSet.Exists.
  generalize (mutable_spec_mutable P E); intros Hm;
  unfold mutable_spec in *; rewrite Hm in *; clear Hm.
  split; intros H.

  destruct H as [x [HinE Hflow]].
  eapply ag_flow_iff_ag_flow' in Hflow.
  unfold ag_flow' in *.
  intuition eauto;
    solve [rewrite H in *; auto | right; apply ex_intro with x; intuition].

  destruct H as [H | H].
  eapply ex_intro.
  rewrite <- ag_flow_iff_ag_flow'; unfold ag_flow'.
  split; [apply H|left; apply Ref.eq_refl].

  destruct H as [x [HinE Hedge]].
  eapply ex_intro. 
  rewrite <- ag_flow_iff_ag_flow'; unfold ag_flow'.
  split; eauto. 

Qed.

Ltac edge_destruct edge src tgt rgt:=
  rewrite <- (Edges.edge_rewrite edge) in *;
  generalize (Edges.source edge) (Edges.target edge) (Edges.right edge); intros src tgt rgt; clear edge;
  edge_simpl.


 
(* This is a more general proof of mutable maximal, which relies heavily on the pointwise notion of ag_flow *)

Theorem mutable_maximal_inclusive :
forall P', Seq.maxTransfer P' ->
forall E Me', mutable_spec P' E Me' ->
forall M, RefSet.Subset E M -> RefSet.Subset M Me' ->
forall Mm', mutable_spec P' M Mm' ->
  RefSet.eq Mm' Me'.
Proof.
  intros P' HP' E Me' HMe' M Hsub1 Hsub2 Mm' HMm'.
  intros x.

  eapply mutable_spec_eq_mutable in HMe'.
  eapply mutable_spec_eq_mutable in HMm'.

  rewrite HMe' in *; clear Me' HMe'.
  rewrite HMm' in *; clear Mm' HMm'.

  (* These are exactly ag_ex_fold', convert to ag_ex_flow *)
  eapply iff_trans; [eapply iff_sym; apply ag_ex_flow_iff_ag_ex_flow'|].
  eapply iff_trans; [| apply ag_ex_flow_iff_ag_ex_flow'].

  unfold ag_ex_flow; unfold RefSet.Exists.
  split; intros [x' [HinX' HflowX']].

  eapply Hsub2 in HinX'.
  eapply iff_sym in HinX'; [|apply iff_sym; apply ag_ex_flow_iff_ag_ex_flow'].
  unfold ag_ex_flow in *; unfold RefSet.Exists in *.
  destruct HinX' as [e [HinE HflowE]].

  eapply ex_intro; split; [apply HinE| eauto].


  eapply Hsub1 in HinX'.
  eapply ex_intro; split; [apply HinX'| eauto].

Qed.

Implicit Arguments mutable_maximal_inclusive [P' E Me' M Mm'].


(* 
   TODO: Clean this up,
   eliminate all unnecessary mutable_spec, attempt to reduce complexity and perform backchaining 
   This is a more general version of mutable_project_in_eq, but it falls out as a corrolary.
   Remember, by mutable_nondec (In a E) -> (In a M) 

   This should form the foundaiton for induciton which will allow us to grow a singleton
   subsystem E in the fully authorized access graph into any arbitrary size via AG_project
   forming a lineage for all objects in the set.

   If (mutable_spec P E M) and (AG_project a o P P') where "o is novel" and (In a M)
   then (mutable_spec P' (add o E) (add o M)).
*)
Theorem mutable_spec_project_add_eq:
forall P, Seq.maxTransfer P ->
forall objs, Seq.ag_objs_spec P objs ->
forall N, RefSet.Subset objs N ->
forall E, RefSet.Subset E N ->
forall o, ~ RefSet.In o N ->
forall M, mutable_spec P E M -> 
forall a, RefSet.In a M ->
forall P', AG_project a o P P' ->
forall oE, RefSetProps.Add o E oE ->
forall MoE', mutable_spec P' oE MoE' ->
forall oM, RefSetProps.Add o M oM ->
RefSet.eq oM MoE'.
Proof.
  intros P Hmax objs Hobjs N Hn E He o Ho M Hm a HinM P' Hproj oE Hoe MoE' Hmoe' oM Hom.

  assert (exists Me', mutable_spec P' E Me') as [Me' Hme'] by
    (eapply ex_intro; apply mutable_spec_mutable).
  assert (exists MoM', mutable_spec P' oM MoM') as [MoM' Hmom'] by
    (eapply ex_intro; apply mutable_spec_mutable).
  assert (exists Mm', mutable_spec P' M Mm') as [Mm' Hmm'] by
    (eapply ex_intro; apply mutable_spec_mutable).

  assert (RefSet.In a N) as HinN by
  (eapply mutable_subset_objs;
    [apply Hobjs
      | auto
      | apply He
      | apply Hm
      | apply HinM]).
  generalize (mutable_project_in_eq Hmax Hobjs Hn He HinN Ho Hproj Hm HinM Hmm' Hom); intros Heq_Mm'_oM.
  assert (Seq.maxTransfer P') as Hmax' by (eapply AG_project_maximal; eauto).
  assert (RefSet.Subset E M) as Hsub_E_M by (eapply mutable_nondec; eauto).
  assert (RefSet.Subset M Me') as Hsub_M_Me'.
  eapply mutable_spec_subset; 
    [ apply RefSetProps.subset_refl
      | (* defer for existentials *)
      | apply Hme'
      | apply Hm
    ]; intros edge; edge_destruct edge src tgt rgt;
        intros HinP; unfold AG_project in *; rewrite Hproj; intuition eauto.
  generalize (mutable_maximal_inclusive Hmax' Hme' Hsub_E_M Hsub_M_Me' Hmm'); intros Heq_Mm'_Me'.
  assert (RefSet.Subset M oM) as Hsub_M_oM by (intros o'; rewrite (Hom o'); intuition).
  assert (RefSet.Subset E oE) as Hsub_E_oE by (intros o'; rewrite (Hoe o'); intuition).
  assert (RefSet.Subset oE oM) as Hsub_oE_oM by (intros o'; rewrite (Hom o'); rewrite (Hoe o'); intuition).
  (* because mutable is maximal, we can show MoM [=] Mm' ([=] Me' [=] oM) *)
  generalize (RefSetProps.subset_equal (RefSet.eq_sym Heq_Mm'_oM)); intros Hsub_oM_Mm'.
  generalize (mutable_maximal_inclusive Hmax' Hmm' Hsub_M_oM Hsub_oM_Mm' Hmom'); intros Heq_MoM'_Mm'.

(* by mutable_spec_subset, oE [<=] oM -> MoE' [<=] MoM'.
   by mutable_spec_subset,  e [<=] oE -> Me' [<=] MoE'
   because Me' [=] MoM', MoE' [=] MoM'
   because MoM' [=] Mm', qed *)


  assert (RefSet.Subset MoE' MoM') as Hsub_MoE'_MoM' by
    (eapply mutable_spec_subset;
      [apply Hsub_oE_oM
        | apply AGProps.subset_refl
        | apply Hmom'
        | apply Hmoe'
    ]).
  assert (RefSet.Subset Me' MoE') as Hsub_Me'_MoE'.
  eapply mutable_spec_subset;
    [ apply Hsub_E_oE
      | apply AGProps.subset_refl
      | apply Hmoe'
      | apply Hme'
    ].

  assert (RefSet.eq Mm' MoE') as Heq_Mm'_MoE' by
    (intros o'; split;
      [rewrite Heq_Mm'_Me'; eapply Hsub_Me'_MoE'
        | rewrite <- Heq_MoM'_Mm'; eapply Hsub_MoE'_MoM']).
  
  rewrite <- Heq_Mm'_MoE'; apply RefSet.eq_sym; auto.
Qed.



  (* TODO move to sumbool_dec *)
  Theorem true_bool_of_sumbool_iff_true : forall A (SB:{A}+{~A}),
    true_bool_of_sumbool SB = true <-> A.
  Proof.
    intros; unfold true_bool_of_sumbool.
    split; [ eapply true_bool_of_sumbool_l | eapply proof_r_true_bool_of_sumbool]; eauto.
  Qed.
  Theorem true_bool_of_sumbool_iff_false : forall A (SB:{A}+{~A}),
    true_bool_of_sumbool SB = false <-> ~ A.
  Proof.
    intros; unfold true_bool_of_sumbool.
    split; [ eapply true_bool_of_sumbool_r | eapply proof_l_true_bool_of_sumbool]; eauto.
  Qed.

Definition filtered_subset_eq' E E' N :=
  forall e, ~ RefSet.In e N \/ (RefSet.In e N /\ (RefSet.In e E <-> RefSet.In e E')).

Definition filtered_subset_eq E E' N :=
  RefSet.eq 
  (RefSet.filter (fun x => true_bool_of_sumbool (RefSetProps.In_dec x N)) E)
  (RefSet.filter (fun x => true_bool_of_sumbool (RefSetProps.In_dec x N)) E').

Theorem filtered_subset_eq_iff_filtered_subset_eq' :
  forall E E' N, filtered_subset_eq E E' N <-> filtered_subset_eq' E E' N.
Proof.
  unfold filtered_subset_eq; unfold filtered_subset_eq'.
  intros; split; intros H.

  intros e; generalize (H e); clear H; intros H.
  do 2 (rewrite RefSetFacts.filter_iff in H;
    [| unfold SetoidList.compat_bool; unfold Proper; unfold respectful; intros x y Heq; rewrite Heq; auto]).
  rewrite true_bool_of_sumbool_iff_true in H.
  case (RefSetProps.In_dec e N); intros Hcase; intuition.

  intros e.
  do 2 (rewrite RefSetFacts.filter_iff;
    [| unfold SetoidList.compat_bool; unfold Proper; unfold respectful; intros x y Heq; rewrite Heq; auto]).
  rewrite true_bool_of_sumbool_iff_true.
  generalize (H e); clear H; intros H.
  case (RefSetProps.In_dec e N); intros Hcase; intuition.
  
Qed.

Theorem filtered_subset_eq_dec : forall E E' N, {filtered_subset_eq E E' N} + {~ filtered_subset_eq E E' N}.
Proof.
  intros; unfold filtered_subset_eq; eapply RefSet.eq_dec.
Qed.

Theorem filtered_subset_eq'_dec : forall E E' N, {filtered_subset_eq' E E' N} + {~ filtered_subset_eq' E E' N}.
Proof.
  intros; case (filtered_subset_eq_dec E E' N); intros Hcase;
    rewrite filtered_subset_eq_iff_filtered_subset_eq' in Hcase; 
      intuition auto.
Qed.

Theorem filtered_subset_eq'_sym: forall E E' N, filtered_subset_eq E E' N <-> filtered_subset_eq E' E N.
Proof.
  intros E E' N.
  do 2 rewrite filtered_subset_eq_iff_filtered_subset_eq'.
  unfold filtered_subset_eq'; split; intros H e; generalize (H e); intuition.
Qed.

Theorem filtered_subset_eq_Empty :
  forall E, RefSet.Empty E ->
  forall E' N, filtered_subset_eq E E' N -> 
  RefSet.For_all (fun e' => ~ RefSet.In e' N) E'.
Proof.
  intros E Hempty E' N Hfilt e HinE.
  rewrite filtered_subset_eq_iff_filtered_subset_eq' in Hfilt.
  generalize (Hempty e) (Hfilt e); clear Hempty Hfilt; intros Hempty Hfilt.
  intuition.
Qed.

(*

Fold mutable_spec_project_add_eq over an AG_lineage to produce equality,

Consider rewriting this with hypotheses
forall N', AG_lineage N P N' P' 
rewriting E' [=] (diff N' N)

The intersection of N and N' is guaranteed to be disjoint

We can't prove this with AG_lineage as we can not guarantee all elements in (N' - N) to be in E, 
only projected from N.

We will need to prove this directly.

*)

(* Theorem mutable_spec_ag_lineage_union_eq : *)
(*   forall P, Seq.maxTransfer P -> *)
(*   forall objs, Seq.ag_objs_spec P objs -> *)
(*   forall N, RefSet.Subset objs N -> *)
(*   forall E, RefSet.Subset E N -> *)
(*     ~ RefSet.Empty E -> *)
(*   forall M, mutable_spec P E M -> *)
(*   forall N' P', AG_lineage N P N' P' -> *)
(*   forall M', mutable_spec P' (RefSet.union E (RefSet.diff N' N)) M' -> *)
(*     RefSet.eq M' (RefSet.union M E'). *)
(* Proof. *)
(*   intros P Hmax objs Hobjs N Hn E HE Hnonempty E' Hdisj P' Hlin M HM M' HM' *)
(* Qed. *)





(* Note: N are the objs we do not wish to extend into *)


Definition insert_spec a o D D' := 
  forall src tgt rgt, AG.In (Edges.mkEdge src tgt rgt) D' <-> 
    (AG.In (Edges.mkEdge src tgt rgt) D \/
      Ref.eq src a /\ Ref.eq tgt o \/
      Ref.eq src o /\ Ref.eq tgt a).

Theorem Proper_insert_spec_impl : Proper (Ref.eq ==> Ref.eq ==> AG.eq ==> AG.eq ==> impl) insert_spec.
Proof.
  unfold insert_spec; unfold Proper; unfold respectful; unfold impl;
    intros; generalize (H3 src tgt rgt); clear H3; intros H3;
      rewrite H in *; rewrite H0 in*; rewrite H1 in *; rewrite H2 in *; trivial.
Qed.

Theorem insert_spec_insert : 
  forall a o D, insert_spec a o D (insert a o D).
Proof.
  unfold insert_spec; unfold insert.
  intros a o D src tgt rgt.
  rewrite ag_add_cap_spec; [| apply AG.eq_refl].
  rewrite ag_add_cap_spec; [| apply AG.eq_refl].
  edge_simpl.
  repeat progress rewrite CC.mkCap_rights.
  repeat progress rewrite CC.mkCap_target.
  intuition.
Qed.



Theorem insert_spec_eq_insert :
  forall a o D D', insert_spec a o D D' -> AG.eq D' (insert a o D).
Proof.
  unfold insert_spec.
  intros a o D D' Hinsert edge.
  edge_destruct edge src tgt rgt.
  rewrite Hinsert. clear Hinsert D'.
  eapply iff_sym.
  eapply insert_spec_insert.
Qed.

Theorem insert_spec_insert_iff :
  forall a o D D', insert_spec a o D D' <-> AG.eq D' (insert a o D).
Proof.
  intros a o D D'.
  split; intros H.
  eapply insert_spec_eq_insert; auto.
  eapply Proper_insert_spec_impl;
    [apply Ref.eq_refl
      | apply Ref.eq_refl
      | apply AG.eq_refl
      | apply AG.eq_sym; apply H
      | apply insert_spec_insert
    ].
Qed.


  Theorem ag_fully_authorized_insert_subset :
    forall D objs, Seq.ag_objs_spec D objs ->
    forall E C A, ag_fully_authorized_spec D E C A ->
    forall o, ~ RefSet.In o objs ->
    forall E', RefSetProps.Add o E E' ->
    forall A', ag_fully_authorized_spec D E' C A' ->
    forall a, RefSet.In a E ->
    forall I, AG.eq I (insert a o A) ->
      AG.Subset I A'.
    Proof.
      intros D objs Hobjs E C A Hauth o Ho E' Hadd A' Hauth' a HinE I HI i.
      (* pay attention to which theorems you use. *)
      rewrite HI. clear I HI.
      edge_destruct i src tgt rgt.
      intros HinI; eapply insert_spec_insert in HinI.
      generalize (Hauth' (Edges.mkEdge src tgt rgt)) (Hauth (Edges.mkEdge src tgt rgt)); 
        clear Hauth' Hauth; intros Hauth' Hauth.
      rewrite Hauth'; clear A' Hauth'.
      rewrite Hauth in HinI; clear A Hauth.
      unfold excluded_edge in *.
      revert HinI; edge_simpl; intros HinI.
      generalize (Hadd src) (Hadd tgt); intros HaddSrc HaddTgt; clear Hadd.
      rewrite HaddSrc; rewrite HaddTgt; clear HaddSrc HaddTgt.
      do 2 (rewrite Sumbool_not_or; Sumbool_decide; try solve [apply Ref.eq_dec| apply RefSetProps.In_dec]).
      (* Reduce to eq built-in as tactics are much faster *)
      unfold Ref.eq in *.

      Ltac HinI_solver HinI:=       
        destruct HinI as [[HinI |[HinI | HinI]] | [HinI | HinI]];
          let HeqSrc:= fresh "HeqSrc" in
            let HeqTgt := fresh "HeqTgt" in
              solve [ destruct HinI as [HeqSrc HeqTgt]; 
                try rewrite HeqSrc in *; try rewrite HeqTgt in *; intuition 
                | intuition].
      
      Ltac HinI_no_edge_solver  src tgt rgt D Ho Hobjs HinI := 
        let Hnot := fresh "Hnot" in
          let HnotIn := fresh "HnotIn" in
      try (assert (~ AG.In (Edges.mkEdge src tgt rgt) D) as HnotIn by 
        (intros Hnot; apply Ho; apply Hobjs;
          do 2 eapply ex_intro; eauto)); HinI_solver HinI.




      case (RefSetProps.In_dec src E); intros HcaseSrcE;
        (case (RefSetProps.In_dec tgt E); intros HcaseTgtE);
        solve [ HinI_no_edge_solver src tgt rgt D Ho Hobjs HinI
          | case (Ref.eq_dec o src); intros Hsrc; 
            (case (Ref.eq_dec o tgt); intros Htgt);
            unfold Ref.eq in *;  try rewrite Hsrc in *; try rewrite Htgt in *;
              HinI_no_edge_solver src tgt rgt D Ho Hobjs HinI].
    Qed.

    Implicit Arguments ag_fully_authorized_insert_subset [D objs E C A o E' A' a I].


(* TODO: Move to Set library *)
  Theorem diff_empty : forall A B, AG.Empty (AG.diff A B) -> AG.Subset A B.
  Proof.
    intros A B H x Hin.
    unfold AG.Empty in H.
    generalize (H x); clear H; intros H.
    rewrite AGFacts.diff_iff in H;
    rewrite Sumbool_not_and in H; try (Sumbool_decide; eapply AGProps.In_dec).
    destruct H; [contradiction
      |rewrite <- Sumbool_dec_not_not_iff in H; try (Sumbool_decide; eapply AGProps.In_dec); auto].
  Qed.


Theorem ag_fully_authorized_insert_def : 
  forall D E C A, ag_fully_authorized_spec D E C A ->
  forall a o I, insert_spec a o A I ->
  forall src tgt rgt, 
    (AG.In (Edges.mkEdge src tgt rgt) I <->
      (RefSet.In src E /\ RefSet.In tgt E \/
        RefSet.In src E /\ exists_cap_edge tgt rgt C \/
        AG.In (Edges.mkEdge src tgt rgt) D /\ ~ RefSet.In src E /\ ~ RefSet.In tgt E \/
        Ref.eq src a /\ Ref.eq tgt o \/
        Ref.eq src o /\ Ref.eq tgt a)).
Proof.
  intros D E C A Hauth a o I HI src' tgt' rgt'.
  unfold insert_spec in *; unfold ag_fully_authorized_spec in *;
    unfold excluded_edge in *.
  generalize (HI src' tgt' rgt'); clear HI; intros HI.
  generalize (Hauth (Edges.mkEdge src' tgt' rgt')); clear Hauth; intros Hauth.
  edge_simpl.
  rewrite Hauth in HI; clear Hauth.
  intuition.
Qed.

Implicit Arguments ag_fully_authorized_insert_def [D E C A a o I].

(* 

   This theorem is proved by induction over (AG.diff A' I). 

   This theorem will rely on sufficient conditions to cause (AG.Subset (insert a o A) A'),
   most likely from ag_fully_authorized_insert_subset.

*)

Theorem ag_fully_authorized_over_insert:
forall D E C A, ag_fully_authorized_spec D E C A ->
forall o E', RefSetProps.Add o E E' ->
forall A', ag_fully_authorized_spec D E' C A' ->
forall a, RefSet.In a E -> AG.Subset (insert a o A) A' ->
  Seq.potTransfer (insert a o A) A'.
Proof.
  intros D E C A Hauth o E' Hadd A' Hauth' a HinE HIsubA'.

  eapply Seq.potTransfer_eq.
  eapply AGProps.union_subset_equal.
  assert (forall S S', AG.Subset (AG.diff S S) S') as Hdiff by
    (intros S S' x; AGFacts.set_iff; intros; intuition);
    apply (Hdiff (AG.diff A' (insert a o A))).
  apply AG.eq_refl.

  generalize (@AGProps.subset_refl (AG.diff A' (insert a o A))).

eapply AGProps.set_induction with (P:= 
(fun S => AG.Subset S (AG.diff A' (insert a o A)) ->
     Seq.potTransfer (AG.union (AG.diff (AG.diff A' (insert a o A)) S) (insert a o A)) A')).



(* base *)

intros S Hempty Hsub.
(* This is simply that A' [=] A' *)
(* (AG.union (AG.diff (AG.diff A' (insert a o A)) S) (insert a o A)) *)
(* [=] (AG.union (AG.diff (AG.diff A' (insert a o A)) AG.empty) (insert a o A)) *)
(* [=] (AG.union (AG.diff A' (insert a o A))) (insert a o A)) *)
(* [=] A' *)

eapply Seq.potTransfer_eq;
[apply AG.eq_refl
| 
| apply Seq.potTransfer_base; apply AG.eq_refl].

rewrite (AGProps.empty_diff_2 _ Hempty).
assert (forall s s', AG.Subset s s' -> AG.eq (AG.union (AG.diff s' s) s) s') as Hdiffeq.
intros s s' Hsub'; eapply AG.eq_sym.
eapply AG.eq_trans; [ eapply AG.eq_sym; apply AGProps.diff_inter_all | ].
rewrite AGProps.inter_sym;
  rewrite AGProps.inter_subset_equal; [|apply Hsub'];
      apply AG.eq_refl.
rewrite Hdiffeq; eauto.


(*step*)
intros S S' IH edge Hedge HS' HsubS'.
(* 
   * S [<=] S' by AGProps.Add
   * AG.Subset S (AG.diff A' (insert a o A)) by AGProps.subset_trans with S'
   * Seq.potTransfer
         (AG.union (AG.diff (AG.diff A' (insert a o A)) S) (insert a o A)) A'
   * In x A' /\ ~ In x (insert a o A) by diff and A'.
   * By adding this element to A', we know that it is no longer in
       (AG.diff (AG.diff A' (insert a o A)) S')
   * To prove the goal:
        Seq.potTransfer
             (AG.union (AG.diff (AG.diff A' (insert a o A)) S') (insert a o A)) 
             A'
     We must show:
        Seq.potTransfer
             (AG.union (AG.diff (AG.diff A' (insert a o A)) S') (insert a o A))
             (AG.union (AG.diff (AG.diff A' (insert a o A)) S) (insert a o A))
   * The difference of these is only x.
   * Because potTransfer respects add_commutative functions, we can model this as:
        Seq.potTransfer
             (insert a o A)
             (AG.add x (insert a o A))
   * Every edge in A' can be resolved using a single transitive step, so we use trans.
        Seq.transfer
             (insert a o A)
             (AG.add x (insert a o A))
   * We can perform this by case analysis on the conditions of ag_fully_authorized_spec in A' and  insert_spec.
   * keep in mind that ~ In x (insert a o A), which is critical for eliminating most nonsensical cases of x.
*)


(*
   
   reduce AGProps.Add edge S S' and AG.Subset S' (AG.diff A' (insert a o A)) into parts:

   AG.In edge (AG.diff A' (insert a o A)) /\
   AG.Subset S (AG.diff A' (insert a o A))

   as they will be needed in the future.
*)

generalize HsubS'; intros HsubS;
  eapply AGProps.subset_trans in HsubS;
    [| eapply AGAddEq.Add_Subset; apply HS'].
assert (AG.In edge (AG.diff A' (insert a o A))) as HinEdge by
  (eapply HsubS'; eapply HS'; auto).

(*
   Rewrite S' as (AG.add edge S) and clear S'.
*)
generalize (AGAddEq.Add_add edge S S'); intros [Hrw _].
eapply Seq.potTransfer_eq;
  [ rewrite <- (Hrw HS'); apply AG.eq_refl
    | apply AG.eq_refl
    |rewrite <- (Hrw HS') in *; clear S' HS' Hrw HsubS'].

(* 
   start by reducing the problem to :
        Seq.potTransfer
             (AG.union (AG.diff (AG.diff A' (insert a o A)) S') (insert a o A))
             (AG.union (AG.diff (AG.diff A' (insert a o A)) S) (insert a o A)) 

*)

eapply Seq.potTransfer_transitive; [| apply IH; auto].
clear IH.

assert (forall x' s s' s2, 
  AG.In x' s2 ->
  ~ AG.In x' s ->
  AGProps.Add x' s s' -> 
  AG.eq (AG.diff s2 s) (AG.add x' (AG.diff s2 s'))) as Hunion_diff_add.
intros x' s s' s2 s3 H0 H1;
intros y'; generalize (H1 y'); clear H1; intros H1;
AGFacts.set_iff;
rewrite H1; clear H1;
generalize (Edge.eq_dec x' y'); intros [Hcase|Hcase];
intuition auto; try solve [rewrite <- Hcase in *; auto].
(*
   Use Hunion_diff_add to move edge to the outside.
   Also use AGProps.union_sym to swap the union order for the next step.
*)

eapply Seq.potTransfer_eq;
  [ eapply AG.eq_sym; apply AGProps.union_sym
    | 
    | ].
eapply AG.eq_sym; 
rewrite (Hunion_diff_add edge); try solve[auto].
rewrite AGProps.union_add; rewrite AGProps.union_sym; rewrite <- AGProps.union_add; eapply AG.eq_refl.
clear Hunion_diff_add.

(* Use potTransfer_commute_monotonic to eliminate the common union and reduce to only the (insert a o A) condition *)
eapply Seq.potTransfer_commute_monotonic with (Fa:=(fun s => AG.union s _)); try solve [eapply union_diff_fn_req].

(* eliminate S *)
clear S Hedge HsubS.

(* destruct edge *)
revert HinEdge; AGFacts.set_iff.
edge_destruct edge src tgt rgt.
intros [HedgeA' HedgeInsert].

(* simplify the properties of HedgeA' and eliminate Hauth' and A' *)
eapply Hauth' in HedgeA'; edge_simpl; clear A' Hauth' HIsubA'.

(* simplify the properties of HedgeInsert and eliminate insert over edge *)
revert HedgeInsert.
generalize (insert_spec_insert a o A).
generalize (insert a o A).
intros I HI HedgeI.

(* At this point, begin eliminating A and Hauth *)
generalize (ag_fully_authorized_insert_def Hauth HI); clear HI; intros HI.
clear A Hauth.

rewrite Sumbool_dec_not_iff_pos in HedgeI;
  [ 
    | eapply AGProps.In_dec
    | 
    | eapply HI].
(* We can't branch again, and we rely on the fourth goal to solve our existentials. 
Solve goal 2 manually now *)
2: solve [Sumbool_decide; 
  try solve 
    [apply AGProps.In_dec 
      | apply Ref.eq_dec
      | apply RefSetProps.In_dec 
      | apply exists_cap_edge_dec 
      | apply excluded_edge_dec]].
repeat progress (rewrite Sumbool_not_or in HedgeI; Sumbool_decide;
 try solve 
    [apply AGProps.In_dec 
      | apply Ref.eq_dec
      | apply RefSetProps.In_dec 
      | apply exists_cap_edge_dec 
      | apply excluded_edge_dec]).
repeat progress (rewrite Sumbool_not_and in HedgeI; Sumbool_decide; 
  try solve [apply Ref.eq_dec | apply RefSetProps.In_dec | apply exists_cap_edge_dec | apply AGProps.In_dec]).
repeat progress (rewrite <- Sumbool_dec_not_not_iff in HedgeI; try solve [apply RefSetProps.In_dec]).
destruct HedgeI as [HreflE [HoutE [HremE [HinterA HinterO]]]].
unfold excluded_edge in *; edge_simpl.

(* reduce to trans *)

eapply Seq.potTransfer_trans; [apply Seq.potTransfer_base; apply AG.eq_refl|].

(* 
   The 3 cases of HedgeA' give us the definitional cases of exclusion we are looking for.
   
   The first case examines an internal edge that isn't already an internal edge of E
   Since the subsystem is fully connected, we can use send between a and o to recover any other permission.

   The second case examines an authorized edge that wasn't authorized in E.
   Clearly src [=] o, and we can read any such edge from the parent.
   
   The last case examines all remainder edges in D that have source and target not in E'.
   This is impossible.  If the src and tgt are not in E', they are also not in E by subset properties.
   This contradicts 2 of the 3 cases of HremE, the remaining case claims that the edge was not in D.
   However, we also assumed that the edge was in D, so this third case is completely contradictory.
   
   *)

destruct HedgeA' as [HreflE' | [HoutE' | HremE']].

(* Case: fully connected edges in E' *)
destruct HreflE' as [HinSrcE' HinTgtE'].
eapply Hadd in HinSrcE'; eapply Hadd in HinTgtE'.
(* This is by case analysis on which elements are in E *)
case (RefSetProps.In_dec src E); intros HinSrcE;
  (case (RefSetProps.In_dec tgt E); intros HinTgtE);
  try solve [intuition].
(* Sub-Case:   In src E  /\ ~ In tgt E  -> o = tgt *) 
destruct HinTgtE' as [HinTgtE' | HinTgtE']; try contradiction; rewrite HinTgtE' in *; clear HinTgtE'.
eapply Seq.transfer_send.
3: eapply AGProps.Add_add.
eapply (HI a); intuition.
eapply HI; intuition.
(* Sub-Case: ~ In src E  /\   In tgt E  *) 
destruct HinSrcE' as [HinSrcE' | HinSrcE']; try contradiction; rewrite HinSrcE' in *; clear HinSrcE'.
eapply Seq.transfer_send.
3: eapply AGProps.Add_add.
eapply (HI a); intuition.
eapply HI; intuition.
(* Sub-Case: ~ In src E  /\ ~ In tgt E  *) 
destruct HinSrcE' as [HinSrcE' | HinSrcE']; try contradiction; rewrite HinSrcE' in *; clear HinSrcE'.
destruct HinTgtE' as [HinTgtE' | HinTgtE']; try contradiction; rewrite HinTgtE' in *; clear HinTgtE'.
eapply Seq.transfer_self_tgt.
2: eapply AGProps.Add_add.
eapply (HI a _ tx); intuition.

(* Case: authorized edges in E' *)
destruct HoutE' as [HinSrcE' HcapEdgeE'].
eapply Hadd in HinSrcE'.
(* This is by case analysis on which elements are in E *)
case (RefSetProps.In_dec src E); intros HinSrcE; try solve [intuition].
destruct HinSrcE' as [HinSrcE' | HinSrcE']; try contradiction; rewrite HinSrcE' in *; clear HinSrcE'.
eapply Seq.transfer_send.
3: eapply AGProps.Add_add.
eapply (HI a); intuition.
eapply HI; intuition.

(* Case: remainder edges in E', impossible *)
destruct HremE' as [HinD [HinSrcE' HinTgtE']].

eapply RefSetAddEq.Add_Subset in Hadd.
destruct HremE as [HninD | [Hin | Hin]]; try apply Hadd in Hin; contradiction.

Qed.

Implicit Arguments ag_fully_authorized_over_insert [D E C A o E' A' a].

Theorem ag_fully_authorized_insert_project:
forall D E C A, ag_fully_authorized_spec D E C A ->
forall o E', RefSetProps.Add o E E' ->
forall A', ag_fully_authorized_spec D E' C A' ->
forall a, RefSet.In a E -> AG.Subset (insert a o A) A' ->
forall P, Seq.potAcc A P ->
forall N, Seq.ag_objs_spec P N -> ~ RefSet.In o N ->
forall P', Seq.potAcc A' P' ->
  AG_project a o P P'.
Proof.
  intros D E C A HA o E' HE' A' HA' a Ha HIsubA' P HP N HN HOinN P' HP'.

  generalize (ag_fully_authorized_over_insert HA HE' HA' Ha HIsubA'); intros HinsertTrans.
  generalize HP'; intros [Htrans' Hmax'].
  generalize (Seq.potTransfer_transitive HinsertTrans Htrans'); intros HinsertPotTransfer.
  (* we need to prove that potTransfer A P -> potTransfer (insert a o A) (insert a o P) 
     I'm certain this is hiding somewhere in the commutativity laws.
     Once we know that, we can show potAcc (insert a o P) P' *)
  assert (Seq.potTransfer (insert a o A) (insert a o P)).

  unfold insert.
  do 2 (eapply Seq.potTransfer_commute_monotonic;
    [ split; [eauto
      | split; 
        [unfold ag_nondecr; eapply ag_add_cap_nondecr
          |unfold Seq.ag_equiv; intros; eapply ag_add_cap_equiv; eauto; try apply Ref.eq_refl]] | ]);
  apply HP.


  generalize (Seq.exists_potAcc (insert a o P)); intros [P'2 HP'2].
  eapply Seq.potAcc_potTransfer in H; [| apply HP'2].
  eapply Seq.potAcc_potTransfer in HinsertTrans; [| apply HP'].
  eapply potAcc_equiv in HinsertTrans; 
    [ 
      | apply AG.eq_refl
      | apply H];
    eapply AG_project_endow;
      [apply HP
        | apply HN
        | apply HOinN
        | apply AG.eq_refl
        | eapply potAcc_eq_iff;
          [apply HP'2 | apply AG.eq_refl | apply HinsertTrans]].
Qed.

Implicit Arguments ag_fully_authorized_insert_project [D E C A o E' A' a P N P'].



(* 
   At this point, please take note:
   The objs of D and the objs of A are not necessarily related.

   D may admit objs not in A because of outward weak edges to unestablished objs.
   A may admit objs not in D because of novel elements of E or C.

   For this proof to succeed, o must be novel to both D and A.
*)


Theorem ag_fully_authorized_project :
  forall D E C A, ag_fully_authorized_spec D E C A ->
  forall objs, Seq.ag_objs_spec D objs ->
  forall objs', Seq.ag_objs_spec A objs' ->
  forall a, RefSet.In a E ->
  forall o, ~ RefSet.In o objs -> ~ RefSet.In o objs' ->
  forall E', RefSetProps.Add o E E' ->
  forall A', ag_fully_authorized_spec D E' C A' ->
  forall P, Seq.potAcc A P ->
  forall P', Seq.potAcc A' P' ->
    AG_project a o P P'.
Proof.
  intros D E C A Hauth objs Hobjs objs' Hobjs' a Ha o HoInNodes HoInNodes' E' HE' A' Hauth' P Hpa P' Hpa'.
  
  eapply ag_fully_authorized_insert_project.
  apply Hauth.
  apply HE'.
  apply Hauth'.
  apply Ha.
  
  eapply ag_fully_authorized_insert_subset;
    [apply Hobjs
      | apply Hauth
      | apply HoInNodes
      | apply HE'
      | apply Hauth'
      | apply Ha
      | apply AG.eq_refl].

  apply Hpa.
  eapply ag_objs_spec_potTransfer;
    [apply Hobjs' | apply Hpa].
  apply HoInNodes'.
  apply Hpa'.
Qed.

Implicit Arguments ag_fully_authorized_project [D E C A objs objs' a o E' A' P P'].

(* TODO: Move to FSetAddEq or another set library *)

  Theorem RefSetAddEq_nonempty_exists : forall E, ~ RefSet.Empty E <-> exists a, RefSet.In a E.
  Proof.
    intros E; split; intros H.

    unfold RefSet.Empty in *.

    rewrite <- Sumbool_dec_exists_not_iff in H; simpl in *.
    eauto.
    clear H.

    assert (forall A, SetoidList.compat_P (@eq A) (fun _ => True)) as HP by
      (intros A; unfold SetoidList.compat_P; unfold Proper; unfold respectful; unfold impl; intros; auto).
    assert (forall A, let P := (fun (a:A) => True) in forall (a:A), {P a} + {~ P a}) as Hdec by
      (intros A P a; unfold P; intuition).

    ecase (RefSetDep.exists_ (Hdec Ref.t) E);
    try solve [tauto]; intros H'; eapply H' in HP; clear H'; unfold RefSet.Exists in *.
    
    left; destruct HP as [x [HP _]]; eauto.
    right; intros Hnot; eapply HP; destruct Hnot as [x Hnot]; eauto.


    destruct H as [a H]; unfold RefSet.Empty; intros Hnot; eapply Hnot; eauto.
  Qed.

  Theorem ARSetAddEq_nonempty_exists : forall E, ~ ARSet.Empty E <-> exists a, ARSet.In a E.
  Proof.
    intros E; split; intros H.

    unfold ARSet.Empty in *.

    rewrite <- Sumbool_dec_exists_not_iff in H; simpl in *.
    eauto.
    clear H.

    assert (forall A, SetoidList.compat_P (@eq A) (fun _ => True)) as HP by
      (intros A; unfold SetoidList.compat_P; unfold Proper; unfold respectful; unfold impl; intros; auto).
    assert (forall A, let P := (fun (a:A) => True) in forall (a:A), {P a} + {~ P a}) as Hdec by
      (intros A P a; unfold P; intuition).

    ecase (ARSetDep.exists_ (Hdec AccessRight.t) E);
    try solve [tauto]; intros H'; eapply H' in HP; clear H'; unfold ARSet.Exists in *.
    
    left; destruct HP as [x [HP _]]; eauto.
    right; intros Hnot; eapply HP; destruct Hnot as [x Hnot]; eauto.


    destruct H as [a H]; unfold ARSet.Empty; intros Hnot; eapply Hnot; eauto.
  Qed.

(* If we have a projection from any element of E, then by mutable_spec_project_eq, the resulting
   mutability must be increased by exactly o . *)
  Theorem ag_fully_authorized_add_mutable_eq :
    forall D objs, Seq.ag_objs_spec D objs ->
    forall N, RefSet.Subset objs N ->
    forall E, RefSet.Subset E N ->
      ~ RefSet.Empty E ->
    forall o, ~ RefSet.In o N ->
    forall E', RefSetProps.Add o E E' ->
    forall C A, ag_fully_authorized_spec D E C A ->
    forall objs', Seq.ag_objs_spec A objs' ->
      RefSet.Subset objs' N ->
    forall A', ag_fully_authorized_spec D E' C A' ->
    forall P, Seq.potAcc A P ->
    forall P', Seq.potAcc A' P' ->
    forall M, mutable_spec P E M ->
    forall M', mutable_spec P' E' M' ->
    forall oM, RefSetProps.Add o M oM ->
      RefSet.eq M' oM.
Proof.
  intros D objs Hobjs N HN E HE Hnonempty o Ho E' HaddE C A Hauth 
    objs' Hobjs' HN' A' Hauth' P HP P' HP' M HM M' HM' om HaddM.

  (* first, find a in E *)
  eapply RefSetAddEq_nonempty_exists in Hnonempty.
  destruct Hnonempty as [a Ha].

  eapply RefSet.eq_sym.
  eapply mutable_spec_project_add_eq;
    [ apply Seq.maxTransfer_maxPotTransfer; apply HP
      | eapply ag_objs_spec_potTransfer; [apply Hobjs' | apply HP]
      | apply HN'
      | apply HE
      | apply Ho
      | apply HM
      |   eapply mutable_nondec; [apply HM | apply Ha]
      | 
      | apply HaddE
      | apply HM'
      | apply HaddM].
  
  (* at this point, we must show the projection *)
  eapply ag_fully_authorized_project;
    [apply Hauth
      | apply Hobjs
      | apply Hobjs'
      | apply Ha
      | intros Hnot; apply HN in Hnot; contradiction
      | intros Hnot; apply HN' in Hnot; contradiction
      | apply HaddE
      | apply Hauth'
      | apply HP
      | apply HP'].
Qed.

Implicit Arguments ag_fully_authorized_add_mutable_eq [D objs N E o E' C A objs' A' P P' M M' oM].


Definition capset_targets C T := forall t, RefSet.In t T <->
  CapSet.Exists (fun cap => ~ ARSet.Empty (Cap.rights cap) /\ (Ref.eq (Cap.target cap) t)) C.

Theorem capset_targets_eq : forall C C', 
  CapSet.eq C C' -> 
  forall T, capset_targets C T ->
  forall T', capset_targets C' T' ->
  RefSet.eq T T'.
Proof.
  intros C C' Heq T HT T' HT' x.
  rewrite (HT x); rewrite (HT' x); clear T T' HT HT'.
  unfold CapSet.Exists.
  split; (intros [cap [Hin HeqT]];
  eapply ex_intro; intuition eauto;
  eapply Heq; eauto).
Qed.

Definition capset_targets_f C := CapSet.fold (fun cap acc => 
  if ARSet.is_empty (Cap.rights cap) 
    then acc
    else (RefSet.add (Cap.target cap) acc)
) C RefSet.empty.

Theorem capset_targets_iff_f : forall C, capset_targets C (capset_targets_f C).
Proof.
  intros C x. unfold capset_targets_f; unfold CapSet.Exists.
  eapply CapSetProps.fold_rec.
  (* base *)
  intros C1 Hempty.
  split; intros H;
    [eapply RefSetFacts.empty_iff in H; contradiction
      | destruct H as [x' [H _]]; eapply Hempty in H; contradiction].
  (* step *)
  intros cap R C1 C2 HinC HninC1 Hadd IH.
  split; intros H.
  revert H.
  generalize (ARSetFacts.is_empty_iff (Cap.rights cap)).
  case (ARSet.is_empty (Cap.rights cap)); intros Hempty H.

  eapply IH in H; destruct H as [cap' H]; apply ex_intro with cap';
    unfold CapSetProps.Add in Hadd; rewrite Hadd; intuition.
  
  assert (~ARSet.Empty (Cap.rights cap)) as Hempty' by
    (intros Hnot; eapply Hempty in Hnot; discriminate Hnot).

  case (Ref.eq_dec (Cap.target cap) x); intros Heq.
  eapply ex_intro with cap; unfold CapSetProps.Add in Hadd; rewrite Hadd; intuition.

  eapply RefSetProps.Add_add in H; destruct H as [H|H]; try contradiction.
  eapply IH in H; destruct H as [cap' H]; apply ex_intro with cap';
    unfold CapSetProps.Add in Hadd; rewrite Hadd; intuition.

  (* other side *)

  destruct H as [cap' [Hcap' [Hnonempty HeqTgt]]].

  case (Cap.eq_dec cap cap'); intros HeqCap.
  generalize (ARSetFacts.is_empty_iff (Cap.rights cap)).

  case (ARSet.is_empty (Cap.rights cap)); intros Hempty.
  rewrite Cap.rights_eq in Hnonempty; [ | apply Cap.eq_sym; apply HeqCap].
  rewrite Hempty in Hnonempty; contradict Hnonempty; tauto.

  eapply RefSetProps.Add_add; left; rewrite <- HeqTgt; eapply Cap.target_eq; auto.
  

  generalize (ARSetFacts.is_empty_iff (Cap.rights cap)).
  case (ARSet.is_empty (Cap.rights cap)); intros Hempty.

  eapply IH. eapply ex_intro with cap'. split; [ |intuition eauto].
  eapply Hadd in Hcap'; destruct Hcap' as [Hcap' | Hcap']; eauto; contradiction.

  assert (~ARSet.Empty (Cap.rights cap)) as Hempty' by
    (intros Hnot; eapply Hempty in Hnot; discriminate Hnot).

  eapply RefSetProps.Add_add.
  case (Ref.eq_dec (Cap.target cap) x); intros Heq; try solve [intuition].
  right; eapply IH.
  apply ex_intro with cap'.
  apply Hadd in Hcap'; intuition.
Qed.

Theorem Proper_capset_targets: Proper (CapSet.eq ==> RefSet.eq ==> impl) capset_targets.
Proof.
  unfold Proper; unfold respectful; unfold impl.
  intros C C' HeqC T T' HeqT HCT x.
  generalize (HCT x); clear HCT.
  rewrite HeqT.
  intros H; rewrite H; clear H.
  unfold CapSet.Exists.
  split; (intros [cap [Hin Heq]];
  eapply ex_intro; intuition eauto;
  eapply HeqC; eauto).
Qed.

(* All of this, and capset_targets* need to move to SubsystemImpl.v *)

Definition novel_capabilities_obj C e := ~ CapSet.Exists (fun cap => Ref.eq (Cap.target cap) e) C.

Theorem Proper_novel_capabilities_obj_impl: 
  Proper (CapSet.eq ==> Ref.eq ==> impl) novel_capabilities_obj.
Proof.
  unfold Proper; unfold respectful; unfold impl; unfold novel_capabilities_obj; unfold CapSet.Exists; intros.
  intros [cap [Hin Heq]]; apply H1; eapply ex_intro.
  rewrite H in *; rewrite H0 in *; eauto.
Qed.

Hint Rewrite Proper_novel_capabilities_obj_impl.

Theorem Proper_novel_capabilities_obj_iff: 
  Proper (CapSet.eq ==> Ref.eq ==> iff) novel_capabilities_obj.
Proof.
  split; eapply Proper_novel_capabilities_obj_impl; eauto.
  apply CapSet.eq_sym; auto.
  apply Ref.eq_sym; auto.
Qed.

Hint Rewrite Proper_novel_capabilities_obj_iff.

Theorem novel_capabilities_obj_dec : forall C e, {novel_capabilities_obj C e} + {~novel_capabilities_obj C e}.
Proof.
  intros C e; unfold novel_capabilities_obj.
  Sumbool_decide.
  ecase (CapSetDep.exists_); 
  [|intros H; left; eapply H |intros H; right; eapply H];
  [intros cap; case (Ref.eq_dec (Cap.target cap) e); intros Hcap; [left|right]; apply Hcap| | ];
  (unfold SetoidList.compat_P; unfold Proper; unfold respectful; unfold impl;
    intros; rewrite <- H1; apply Cap.target_eq; apply Cap.eq_sym; auto).
Qed.

Hint Rewrite novel_capabilities_obj_dec.

  Definition novel_capabilities C E := 
    RefSet.For_all (novel_capabilities_obj C) E.

Theorem Proper_novel_capabilities_impl : Proper (CapSet.eq ==> RefSet.eq ==> impl) novel_capabilities.
Proof.
  unfold Proper; unfold respectful; unfold impl; unfold novel_capabilities; unfold RefSet.For_all; intros.
  rewrite <- H0 in *. apply H1 in H2. 
  eapply Proper_novel_capabilities_obj_impl; eauto; try apply Ref.eq_refl.
Qed.

Hint Rewrite Proper_novel_capabilities_impl.

Theorem Proper_novel_capabilities_iff: 
  Proper (CapSet.eq ==> RefSet.eq ==> iff) novel_capabilities.
Proof.
  split; eapply Proper_novel_capabilities_impl; eauto.
  apply CapSet.eq_sym; auto.
  apply RefSet.eq_sym; auto.
Qed.

Hint Rewrite Proper_novel_capabilities_obj_iff.

  Theorem novel_capabilities_dec: forall C E, {novel_capabilities C E} + {~ novel_capabilities C E}.
  Proof.
    intros C E; unfold novel_capabilities.
    ecase (RefSetDep.for_all (novel_capabilities_obj_dec C)); intros H ; [left|right]; eapply H;
    unfold SetoidList.compat_P; unfold Proper; unfold respectful; unfold impl;
      intros x y Heq; rewrite Heq in *; eauto.
  Qed.

Definition extant_capabilities C S := Sub.extant_subsystem (capset_targets_f C) S.

Definition authorized_confined_subsystem C E S := 
  novel_capabilities C E /\ extant_capabilities C S /\ Sub.confined_subsystem C E S.

  Theorem novel_capabilities_inter_empty': 
    forall C E, novel_capabilities C E ->
    forall T, capset_targets C T ->
    forall x, RefSet.In x T -> ~ RefSet.In x E.
  Proof.
    intros C E HauthSet T HT x Hin Hnot.
    unfold capset_targets in *; rewrite HT in Hin; clear HT.
    eapply HauthSet; eauto.
    destruct Hin as [cap [Hin [Hnonempty Heq]]].
    eapply ex_intro; eauto.
  Qed.

  Theorem novel_capabilities_inter_empty: 
    forall C E, novel_capabilities C E ->
    forall T, capset_targets C T ->
      RefSet.Empty (RefSet.inter E T).
  Proof.
    intros C E HauthSet T HT x.
    RefSetFacts.set_iff.
    intros [HinE HinT].
    eapply novel_capabilities_inter_empty' in HauthSet; 
      [ | eauto 1 | eauto 1 ].
    apply HauthSet; auto.
  Qed.


  Theorem ag_remainder_inter_refl :
    forall D objs, Seq.ag_objs_spec D objs ->
    forall E, RefSet.Empty (RefSet.inter E objs) ->
    forall R, ag_remainder_spec D E R ->
      AG.eq D R.
  Proof.
    intros D objs Hobjs E HE R HR x.
    rewrite (HR x); clear R HR.
    intuition.
    eapply Seq.ag_objs_spec_AG_all_objs in Hobjs.
    revert H.
    edge_destruct x src tgt rgt.
    intros HinD.
    eapply Hobjs in HinD; destruct HinD as [HsrcNodes HtgtNodes].
    generalize (HE src) (HE tgt); clear HE; RefSetFacts.set_iff.
    split; edge_simpl; intuition.
  Qed.

  (* This is probably not necessary given ag_remainder_inter_refl, but
     I'm rephrasing it and keeping it for reference *)
  Theorem ag_remainder_inter_eq :
    forall D objs, Seq.ag_objs_spec D objs ->
    forall E, RefSet.Empty (RefSet.inter E objs) ->
    forall E', RefSet.Empty (RefSet.inter E' objs) ->
    forall R, ag_remainder_spec D E R ->
    forall R', ag_remainder_spec D E' R' ->
      AG.eq R R'.
  Proof.
    intros D objs Hobjs E HE E' HE' R HR R' HR'.
    eapply AG.eq_trans.
    eapply AG.eq_sym; eapply ag_remainder_inter_refl; [ | | apply HR]; eauto.
    eapply ag_remainder_inter_refl; eauto.
  Qed.


  Theorem ag_authorized_remainder:
    forall D E C A, ag_fully_authorized_spec D E C A ->
    forall A', ag_fully_authorized_spec (ag_remainder D E) E C A' ->
      AG.eq A A'.
  Proof.
    unfold ag_fully_authorized_spec.
    intros D E C A Hauth A' Hauth' x.
    rewrite Hauth; rewrite Hauth'; clear Hauth Hauth' A A'.

    generalize (ag_remainder_spec_iff D E x); intros H'.
    rewrite H'; intuition.
  Qed.

  Theorem ag_remainder_empty_inter:
    forall D E R, ag_remainder_spec D E R ->
    forall N, Seq.ag_objs_spec R N ->
      RefSet.Empty (RefSet.inter E N).
  Proof.
    intros D E R Hrem N Hobjs.
    unfold RefSet.Empty; intros a.
    RefSetFacts.set_iff.
    unfold Seq.ag_objs_spec in *; unfold ag_remainder_spec in *; unfold excluded_edge in *.
    eapply Sumbool_not_and; Sumbool_decide; try apply RefSetProps.In_dec.
    case (RefSetProps.In_dec a E); intros H; auto.
    right; rewrite Hobjs; clear N Hobjs.
    intros [obj [rgt [H'|H']]];
    eapply Hrem in H'; edge_simpl; intuition.
  Qed.    




    Theorem ag_fully_authorized_spec_eq:
      forall D D', AG.eq D D' ->
      forall E E', RefSet.eq E E' ->
      forall C C', CapSet.eq C C' ->
      forall A, ag_fully_authorized_spec D E C A ->
      forall A', ag_fully_authorized_spec D' E' C' A' ->
        AG.eq A A'.
      Proof.
        unfold ag_fully_authorized_spec.
        intros D D' HeqD E E' HeqE C C' HeqC A Hauth A' Hauth'.
        intros x.
        rewrite Hauth; rewrite Hauth'; clear A Hauth A' Hauth'.
        rewrite HeqD.
        unfold excluded_edge in *.
        rewrite HeqE.
        intuition;
          (eapply Proper_exists_cap_edge in H1;
            solve [apply Ref.eq_refl | apply AccessRight.eq_refl | apply CapSet.eq_sym; auto | eauto]).
      Qed.

    Theorem Proper_ag_fully_authorized_spec_impl:
      Proper (AG.eq ==> RefSet.eq ==> CapSet.eq ==> AG.eq ==> impl) ag_fully_authorized_spec.
    Proof.
      unfold Proper; unfold respectful; unfold impl; unfold ag_fully_authorized_spec; 
        unfold exists_cap_edge; unfold CapSet.Exists; unfold excluded_edge; unfold cap_edge; intros.
      rewrite <- H2; clear y2 H2.
      rewrite H3; clear x2 H3.
      rewrite H; clear x H.
      rewrite H0; clear x0 H0.
      intuition;
      (destruct H2 as [cap Hcap];
      right; left; split; [auto|apply ex_intro with cap; rewrite H1 in *; clear H1; auto]).
    Qed.

    Theorem Proper_ag_fully_authorized_spec:
      Proper (AG.eq ==> RefSet.eq ==> CapSet.eq ==> AG.eq ==> iff) ag_fully_authorized_spec.
    Proof.
      split.
      eapply Proper_ag_fully_authorized_spec_impl; eauto.
      eapply Proper_ag_fully_authorized_spec_impl; eauto.
      apply AG.eq_sym; auto.
      apply RefSet.eq_sym; auto.
      apply CapSet.eq_sym; auto.
      apply AG.eq_sym; auto.
    Qed.

    Theorem Proper_filtered_subset_eq'_impl : 
      Proper (RefSet.eq ==> RefSet.eq ==> RefSet.eq ==> impl) filtered_subset_eq'.
    Proof.
      unfold Proper; unfold respectful; unfold impl. intros.
      unfold filtered_subset_eq' in *.
      intros e; generalize (H2 e); clear H2; intros H2.
      rewrite H1 in *. clear x1 H1.
      rewrite H in *; clear x H.
      rewrite H0 in *; clear x0 H0.
      intuition.
    Qed.
    
    Theorem Proper_filtered_subset_eq' : 
      Proper (RefSet.eq ==> RefSet.eq ==> RefSet.eq ==> iff) filtered_subset_eq'.
    Proof.
      split; intros;  eapply Proper_filtered_subset_eq'_impl; eauto; solve [ eapply RefSet.eq_sym; eauto].
    Qed.

    Theorem ag_remainder_spec_eq: 
      forall D D', AG.eq D D' -> forall E E', RefSet.eq E E' ->
      forall R, ag_remainder_spec D E R ->
      forall R', ag_remainder_spec D' E' R' ->
        AG.eq R R'.
    Proof.
      intros D D' HeqD E E' HeqE R HR R' HR'.
      intros x; rewrite (HR x); rewrite (HR' x); clear R HR R' HR'.
      rewrite HeqD; clear D HeqD.
      unfold excluded_edge; rewrite HeqE; clear E HeqE.
      intuition.
    Qed.

  Theorem ag_objs_ag_fully_authorized :
    forall C Ctargets, capset_targets C Ctargets ->
    forall E, ~ RefSet.Empty E ->
    forall D R, ag_remainder_spec D E R ->
    forall Robjs, Seq.ag_objs_spec R Robjs ->
    forall A, ag_fully_authorized_spec D E C A ->
    forall Aobjs, Seq.ag_objs_spec A Aobjs ->
      RefSet.eq Aobjs (RefSet.union Robjs (RefSet.union E Ctargets)).
  Proof.
    intros C Ctargets HCtargets E Hnonempty D R HR Robjs HRobjs A Hauth Aobjs HAobjs n.
    RefSetFacts.set_iff.
    eapply ag_fully_authorized_spec_eq in Hauth;
      [ | apply AG.eq_refl | apply RefSet.eq_refl | apply CapSet.eq_refl | apply ag_fully_authorized_spec_iff ].
    rewrite (HAobjs n); clear Aobjs HAobjs.

    (* Let's do easy cases *)
    (* Is n in E?? *)
    case (RefSetProps.In_dec n E); intros HinE.
    split; intros; [right; left; auto|].
    apply ex_intro with n; apply ex_intro with wk; left; apply Hauth;
      unfold ag_fully_authorized; AGFacts.set_iff; do 2 left;
        apply Seq.fold_AG_complete_ag; auto.
    
    (* Is n in capset_targets ? *)
    case (RefSetProps.In_dec n Ctargets); intros HinCtargets.
    split; intros; [intuition|].
    eapply RefSetAddEq_nonempty_exists in Hnonempty.
    destruct Hnonempty as [a Ha].
    eapply HCtargets in HinCtargets.
    destruct HinCtargets as [cap [Hin [Hnonempty Heq]]].
    eapply ARSetAddEq_nonempty_exists in Hnonempty.
    destruct Hnonempty as [rgt HinRgt].
    do 2 eapply ex_intro; right.
    apply Hauth; unfold ag_fully_authorized; AGFacts.set_iff.
    left;right.
    eapply ag_authorized_spec_iff; edge_simpl.
    split; [eauto|eapply ex_intro; unfold cap_edge; intuition eauto].

    (* Is n in remainder objs ? *)
    case (RefSetProps.In_dec n Robjs); intros HinRobjs.
    split; intros H; [intuition|].
    eapply HRobjs in HinRobjs; destruct HinRobjs as [obj [rgt Hin]];
    apply ex_intro with obj; apply ex_intro with rgt.
    destruct Hin as [Hin | Hin]; [left|right];
    (rewrite <- Hauth; unfold ag_fully_authorized; AGFacts.set_iff; 
      right; eapply ag_remainder_spec_iff; eapply HR; auto).

    (* This last case must be impossible *)
    split; intros H; [|intuition].
    destruct H as [obj [rgt [Hin|Hin]]];
      (eapply Hauth in Hin; revert Hin; unfold ag_fully_authorized; AGFacts.set_iff;
        intros [[H | H] | H];
          [ eapply Seq.complete_AG_conv_complete_ag in H; destruct H; contradiction
            | eapply ag_authorized_spec_iff in H; edge_simpl; 
                solve [destruct H; contradiction 
                  | destruct H as [H [cap [Hin [H' H2]]]]; try contradiction;
                    do 2 right; eapply HCtargets;
                      eapply ex_intro; split; [eauto| split ; [intro Hnot; eapply Hnot; eauto|auto]]]
            | rewrite ag_remainder_spec_eq in H; 
              [ | apply AG.eq_refl | apply RefSet.eq_refl | apply ag_remainder_spec_iff | apply HR ];
              eapply Seq.ag_objs_spec_AG_all_objs in H; [| apply HRobjs]; destruct H; contradiction]).
  Qed.

  Theorem disjoint_helper:
    forall objs N, RefSet.Subset objs N ->
    forall E, RefSet.Subset E N -> RefSet.Empty (RefSet.inter E objs) ->
    forall E', RefSet.Subset E E' -> filtered_subset_eq' E E' N ->
    RefSet.Empty (RefSet.inter (RefSet.diff E' E) objs).
  Proof.
    intros objs N HN E HE Hdisj E' HE' Hfilter e.
    generalize (Hdisj e) (Hfilter e) (HE e) (HE' e) (HN e); RefSetFacts.set_iff.
    clear Hdisj Hfilter HE HE' HN. 
    intuition.
  Qed.

  Implicit Arguments disjoint_helper [objs N E E'].


    (* Therefore, if we perform induction on (diff E' E), we can precisely describe mutability over
       an appropriate subset. 

       Please note that we restricted E to contain only things not in objs, but still be a subset of N.
       If we have some D containig E in objs, we can use the remainder to produce a D' that is dijoint from E.
       Since this works for any N, N such that E is not empty, this will unify with a singleton.
       As long as we choose N to be large enough to include E, we should be okay.

       The expectation is that N are the off-limits objs.  Normally, we think of these objs as the
       existed objs from our set.  However, the theorems are more general.

       Our base case will simply require that two singletons have identical mutability
       if neither element are in the objs of D.  This extends to supersets of the objs of D.
       If we kick off this theorem with E = {e} and N = union objs E, we should be set.

*)
  Theorem ag_fully_authorized_subset_mutable_eq :
    forall D objs, Seq.ag_objs_spec D objs ->
    forall N, RefSet.Subset objs N ->
    forall E, ~ RefSet.Empty E ->
      RefSet.Empty (RefSet.inter E objs) ->
      RefSet.Subset E N ->
    forall E', RefSet.Subset E E' ->
      filtered_subset_eq E E' N ->

    forall C T, capset_targets C T -> 
      RefSet.Subset T N ->
    forall A, ag_fully_authorized_spec D E C A ->
    forall objs', Seq.ag_objs_spec A objs' ->
      RefSet.Subset objs' N ->
    forall A', ag_fully_authorized_spec D E' C A' ->
    forall P, Seq.potAcc A P ->
    forall P', Seq.potAcc A' P' ->
    forall M, mutable_spec P E M ->
    forall M', mutable_spec P' E' M' ->
     RefSet.eq M' (RefSet.union M (RefSet.diff E' E)).
  Proof.
    intros D objs Hobjs N HN E Hnonempty Hdisj HE E' HE' Hfilter C T HT HTsub A Hauth
      objs' Hobjs' HN' A' Hauth' P HP P' HP' M HM M' HM'.

    (* 
       We need to induct on E' from E to E'.
       Everywhere we use E', we need to rewrite it as (union E (diff E' E)).

       Next, we need to assume Subset (diff E' E) (diff E' E).
       This will unify with our induction hypothesis

      (P:= (fun S =>  
        RefSet.Subset S (RefSet.diff E' E) ->
        ... ->
        RefSet.eq M' (RefSet.union M S)

       *)

    assert (RefSet.eq E' (RefSet.union E (RefSet.diff E' E))) as Hdiff.
    intros x.
    generalize (HE' x).
    RefSetFacts.set_iff.
    case (RefSetProps.In_dec x E); intros Hcase;    
    intuition.

    eapply Proper_ag_fully_authorized_spec in Hauth';
      [ | apply AG.eq_refl
        | apply RefSet.eq_sym; apply Hdiff
        | apply CapSet.eq_refl
        | apply AG.eq_refl
      ].

    eapply Proper_mutable_spec in HM';
      [ | apply AG.eq_refl
        | apply Hdiff
        | apply RefSet.eq_refl
      ].



    rewrite filtered_subset_eq_iff_filtered_subset_eq' in Hfilter.
    assert (forall e, RefSet.In e (RefSet.diff E' E) -> ~ RefSet.In e N) as Hfiltersub by
      (intros e;
    RefSetFacts.set_iff;
    intros Hindiff HinN;
    destruct (Hfilter e) as [H | [H Heq]]; try contradiction;
    rewrite Heq in Hindiff;
    intuition contradiction).

    clear Hdiff.
    revert A' Hauth' P' HP' M' HM'.

    (* While inducting on Hfiltersub isn't strictly necessary, it should make things easier *)
    generalize (RefSetProps.subset_equal (RefSet.eq_refl (RefSet.diff E' E))) Hfiltersub.

    eapply RefSetProps.set_induction with 
      (P:= (fun S =>  
        RefSet.Subset S (RefSet.diff E' E) ->
        (forall e : RefSet.elt, RefSet.In e S -> ~ RefSet.In e N) ->
        forall A' : AG.t,
          ag_fully_authorized_spec D (RefSet.union E S) C A' ->
        forall P' : AG.t,
          Seq.potAcc A' P' ->
        forall M' : RefSet.t,
          mutable_spec P' (RefSet.union E S) M' ->
          RefSet.eq M' (RefSet.union M S)
      )).
    (* base *)
    intros S Hempty Hsub Hfiltersub' A' Hauth' P' HP' M' HM'.

    assert (RefSet.eq (RefSet.union E S) E) as HunionS by
      (rewrite RefSetProps.union_sym; rewrite (RefSetProps.empty_is_empty_1 Hempty);
        rewrite RefSetProps.union_subset_equal; [apply RefSet.eq_refl| eapply RefSetProps.subset_empty]).

    rewrite (RefSetProps.empty_is_empty_1 Hempty); rewrite RefSetProps.union_sym;
    rewrite RefSetProps.union_subset_equal; [ | apply RefSetProps.subset_empty].
    
    eapply mutable_spec_eq_iff;
      [apply HM'
        |
        | apply HunionS
        | apply HM].

    
    eapply potAcc_equiv;
      [ | apply HP'
        | apply HP].
    
    eapply ag_fully_authorized_spec_eq;
      [apply AG.eq_refl
        | apply HunionS
        | apply CapSet.eq_refl
        | apply Hauth'
        | apply Hauth].
    
  (* step *)
  intros S S' IH x HinX HaddX HsubS' HfiltersubS' A' Hauth' P' HP' M' HM'.
  (* Begin instantiating the induction hypothesis *)
  assert (RefSet.Subset S (RefSet.diff E' E)) as HsubS by
    (eapply RefSetProps.subset_trans; [eapply RefSetAddEq.Add_Subset; apply HaddX | auto]).
  assert (forall e, RefSet.In e S -> ~ RefSet.In e N) as HfiltersubS by
    (intros e HeinS; eapply HfiltersubS'; eapply RefSetAddEq.Add_Subset; eauto).
  assert (exists A2, ag_fully_authorized_spec D (RefSet.union E S) C A2) as [A2 Hauth2] by
    (eapply ex_intro; eapply ag_fully_authorized_spec_iff).
  generalize (Seq.exists_potAcc A2); intros [P2 HP2].
  assert (exists M2, mutable_spec P2 (RefSet.union E S) M2) as [M2 HM2] by
    (eapply ex_intro; eapply mutable_spec_mutable).
  generalize (IH HsubS HfiltersubS _ Hauth2 _ HP2 _ HM2); intros HeqM2. clear IH.

  (*
     remember, 
     RefSet.union E S' [=] RefSet.add x (RefSet.union E S) and
     RefSet.union M S' [=] RefSet.add x (RefSet.union M S)
     *)

  assert (forall M, RefSetProps.Add x (RefSet.union M S) (RefSet.union M S')) as HaddS' by
    (intros Q e; RefSetFacts.set_iff; rewrite (HaddX e); intuition).

  assert (exists objs2, Seq.ag_objs_spec A2 objs2) as [objs2 Hobjs2] by
    (eapply ex_intro; eapply Seq.ag_objs_spec_ag_objs).
  assert (~ RefSet.Empty (RefSet.union E S)) as Hnonemptyunion by
    (intro Hnot; apply Hnonempty; intros e HinE; apply Hnot with e; RefSetFacts.set_iff; auto).

  eapply ag_fully_authorized_add_mutable_eq.
  14: apply HM'.
  13: apply HM2.
  12: apply HP'.
  11: apply HP2.
  10: apply Hauth'.
  7: apply Hauth2.
  apply Hobjs.
  eapply RefSetProps.subset_trans; [apply HN | apply RefSetProps.union_subset_1 with (s':=S)].
  intros e; RefSetFacts.set_iff; intuition.
  auto.
  2: apply HaddS'.
  4: eapply RefSetAddEq.Add_eq_complete; 
    [ apply Ref.eq_refl | apply RefSet.eq_sym; apply HeqM2 | apply RefSet.eq_refl| apply HaddS'].
  RefSetFacts.set_iff.
  eapply Sumbool_not_or; Sumbool_decide; try apply RefSetProps.In_dec; split;
    [eapply HfiltersubS'; apply HaddX; auto | auto].
  apply Hobjs2.
  
 (* This is a statement saying that the objs of A2 grew at most by S,
     This should be obvious or we have a theorem, but it's probably buried somewhere *)
  (* In fact objs2 [=] (RefSet.union objs' S) *)
  (* We may need a general theorem about this and probably need to fold it into the IH *)


  assert (exists R, ag_remainder_spec D (RefSet.union E S) R) as [R HR] by
    (eapply ex_intro; apply ag_remainder_spec_iff).

  assert (exists Robjs, Seq.ag_objs_spec R Robjs) as [Robjs HRobjs] by
    (eapply ex_intro; apply Seq.ag_objs_spec_ag_objs).


  rewrite ag_objs_ag_fully_authorized with (Aobjs:=objs2);
    [ | apply HT | apply Hnonemptyunion | apply HR | apply HRobjs| apply Hauth2 | apply Hobjs2 ].


  (* We actually know that the objs of D contain no elements of S or E
     This makes the remainder of D simply D and allows us to substitue objs for Robjs.
     E is a subset of N and objs are a subset of N.
     However, the elements of T must also be a subset of N, which we forgot to assume.
     Do all these things, and this becimes simple subset inclusion.
     *)

  assert (RefSet.Empty (RefSet.inter S objs)) as Hdisj2.
  intros e.
  generalize (disjoint_helper HN HE Hdisj HE' Hfilter e).
  eapply RefSetAddEq.Add_Subset in HaddX.
  rewrite <- HaddX in HsubS'.
  rewrite <- HsubS'.
  auto.
  


  assert (RefSet.Empty (RefSet.inter (RefSet.union E S) objs)) as Hdisj'.
  intros e.
  generalize (Hdisj2 e) (Hdisj e).
  RefSetFacts.set_iff.
  intuition.

  assert (RefSet.eq Robjs objs) as HeqRobjs.
  eapply ag_objs_spec_equiv.
  apply HRobjs.
  apply Hobjs.
  eapply AG.eq_sym.
  eapply ag_remainder_inter_refl.
  apply Hobjs.
  apply Hdisj'.
  apply HR.
  
  rewrite HeqRobjs.
  intros e.
  generalize (Hdisj' e) (Hdisj e) (HTsub e).
  RefSetFacts.set_iff.
  intuition.
  Qed.




(* I'm taking a break for the singleton case *)

(* edge' [=] [e->e'] edge *)

Definition edge_subst_spec e e' edge edge' :=
  ( (Ref.eq (Edges.source edge) e /\ Ref.eq (Edges.source edge') e')
    \/ ~ Ref.eq (Edges.source edge) e /\ Ref.eq (Edges.source edge) (Edges.source edge') ) /\
  ( (Ref.eq (Edges.target edge) e /\ Ref.eq (Edges.target edge') e')
    \/ ~ Ref.eq (Edges.target edge) e /\ Ref.eq (Edges.target edge) (Edges.target edge') ) /\
  AccessRight.eq (Edges.right edge) (Edges.right edge').

Theorem Proper_edge_subst_spec_impl : Proper (Ref.eq ==> Ref.eq ==> Edge.eq ==> Edge.eq ==> impl) edge_subst_spec.
Proof.
  unfold Proper; unfold respectful; unfold impl; unfold edge_subst_spec.
  intros.
  rewrite H in *; rewrite H0 in *. 
  rewrite (Edges.eq_source _ _ H1) in *;  rewrite (Edges.eq_source _ _ H2) in *;
  rewrite (Edges.eq_target _ _ H1) in *;  rewrite (Edges.eq_target _ _ H2) in *;
  rewrite (Edges.eq_right _ _ H1) in *;  rewrite (Edges.eq_right _ _ H2) in *.
  intuition.
Qed.

Hint Resolve Proper_edge_subst_spec_impl.

Theorem Proper_edge_subst_spec_iff : Proper (Ref.eq ==> Ref.eq ==> Edge.eq ==> Edge.eq ==> iff) edge_subst_spec.
Proof.
  unfold Proper; unfold respectful; unfold edge_subst_spec; intros.
  split; eapply Proper_edge_subst_spec_impl; eauto; try (eapply Ref.eq_sym; auto).
Qed.

Hint Resolve Proper_edge_subst_spec_iff.

Theorem edge_subst_spec_eq : forall e e', Ref.eq e e' ->
  forall e2 e2', Ref.eq e2 e2' -> forall edge edge', Edge.eq edge edge' ->
  forall edge2, edge_subst_spec e e2 edge edge2 ->
  forall edge2', edge_subst_spec e' e2' edge' edge2' ->
    Edge.eq edge2 edge2'.
Proof.
  intros e e' He e2 e2' He2 edge edge' Hedge edge2 Hedge2 edge2'; revert Hedge2.
  unfold edge_subst_spec in *.
  generalize (Edges.eq_source _ _ Hedge).
  generalize (Edges.eq_target _ _ Hedge).
  generalize (Edges.eq_right _ _ Hedge).
  clear Hedge.
  edge_destruct edge src tgt rgt.
  edge_destruct edge' src' tgt' rgt'.
  edge_destruct edge2 src2 tgt2 rgt2.
  edge_destruct edge2' src2' tgt2' rgt2'.
  rewrite He; rewrite He2.
  do 3 (intros Heq; rewrite Heq; clear Heq); clear src tgt rgt.
  intros Hedge2 Hedge2'.
  destruct Hedge2 as [Hsrc2 [Htgt2 Hrgt2]].
  destruct Hedge2' as [Hsrc2' [Htgt2' Hrgt2']].
  rewrite <- Hrgt2; rewrite <- Hrgt2'; clear rgt2' rgt2 Hrgt2 Hrgt2'.
  unfold Ref.eq in *.
  intuition (eapply Edges.edge_equal; unfold Ref.eq; eauto; try apply AccessRight.eq_refl) .
Qed.  

Hint Resolve edge_subst_spec_eq.

Definition edge_subst e e' edge := 
  let src := if Ref.eq_dec (Edges.source edge) e then e' else Edges.source edge in
  let tgt := if Ref.eq_dec (Edges.target edge) e then e' else Edges.target edge in
  (Edges.mkEdge src tgt (Edges.right edge)).

Theorem edge_subst_spec_edge_subst : forall e e' edge, edge_subst_spec e e' edge (edge_subst e e' edge).
Proof.
  unfold edge_subst_spec; unfold edge_subst; intros e e' edge.
  case (Ref.eq_dec (Edges.source edge) e); intros HeqSrc ; [rewrite HeqSrc in *|];
    (case (Ref.eq_dec (Edges.target edge) e) ; intros HeqTgt ; [rewrite HeqTgt in *|]); edge_simpl;
  intuition (try solve [apply Ref.eq_refl | apply AccessRight.eq_refl]).
Qed.

Hint Resolve edge_subst_spec_edge_subst.

Theorem edge_subst_spec_dec: forall e e' edge edge', 
  {edge_subst_spec e e' edge edge'} + { ~ edge_subst_spec e e' edge edge'}.
Proof.
  intros.
  case (Edge.eq_dec edge' (edge_subst e e' edge)); intros Hcase; [left|right; intros Hspec; eapply Hcase].
  eapply Proper_edge_subst_spec_impl; 
    [eapply Ref.eq_refl
      | eapply Ref.eq_refl
      | eapply Edge.eq_refl
      | eapply Edge.eq_sym; apply Hcase
      | eapply edge_subst_spec_edge_subst].
  eapply edge_subst_spec_eq;
    [apply Ref.eq_refl
      | apply Ref.eq_refl
      | apply Edge.eq_refl
      | apply Hspec
      | apply edge_subst_spec_edge_subst].
Qed.

Definition ag_subst_spec e e' ag ag' :=
  forall edge', AG.In edge' ag' <-> AG.Exists (fun edge => edge_subst_spec e e' edge edge') ag.
  
Theorem Proper_ag_subst_spec_impl : Proper (Ref.eq ==> Ref.eq ==> AG.eq ==> AG.eq ==> impl) ag_subst_spec.
Proof.
  unfold Proper; unfold respectful; unfold impl; unfold ag_subst_spec; unfold AG.Exists; intros.
  rewrite H in *; rewrite H0 in *; clear x x0 H H0.
  eapply iff_trans; [eapply iff_sym; apply H2| clear H2].
  eapply iff_trans; [eapply H3| clear x2 H3].
  split; (intros [edge [H H']]; eapply ex_intro; split; [eapply H1; eauto | eapply H']).
Qed.

Hint Resolve Proper_ag_subst_spec_impl.

Theorem Proper_ag_subst_spec_iff : Proper (Ref.eq ==> Ref.eq ==> AG.eq ==> AG.eq ==> iff) ag_subst_spec.
Proof.
  unfold Proper; unfold respectful; unfold ag_subst_spec; intros.
  split; apply Proper_ag_subst_spec_impl; eauto; try (eapply Ref.eq_sym; auto); try (eapply AG.eq_sym; auto).
Qed.

Hint Resolve Proper_ag_subst_spec_iff.

Theorem ag_subst_spec_eq : forall e e', Ref.eq e e' ->
  forall e2 e2', Ref.eq e2 e2' -> forall ag ag', AG.eq ag ag' ->
  forall ag2, ag_subst_spec e e2 ag ag2 ->
  forall ag2', ag_subst_spec e' e2' ag' ag2' ->
    AG.eq ag2 ag2'.
Proof.
  intros e e' He e2 e2' He2 ag ag' Hag ag2 Hag2 ag2'; revert Hag2.
  unfold ag_subst_spec in *; unfold AG.Exists.
  rewrite He in *; clear e He.
  rewrite He2 in *; clear e2 He2.
  intros Hag2 Hag2' edge.
  eapply iff_trans; [eapply Hag2|clear Hag2].
  eapply iff_trans; [clear Hag2'|eapply iff_sym; apply Hag2'].
  split; intros [edge' [H H']]; eauto.
Qed.  

Hint Resolve ag_subst_spec_eq.

Definition ag_subst e e' ag := AG.fold (fun edge acc => AG.add (edge_subst e e' edge) acc) ag AG.empty.

Theorem ag_subst_spec_ag_subst : forall e e' ag, ag_subst_spec e e' ag (ag_subst e e' ag).
Proof.
  unfold ag_subst_spec; unfold ag_subst; unfold AG.Exists; intros e e' ag.
  eapply AGProps.fold_rec.
  (* base *)
  intros s Hempty edge.
  split.
  intros Hempty'; eapply AGFacts.empty_iff in Hempty'; contradiction.
  intros [edge' [Hempty' Hsubst]].  eapply Hempty in Hempty'; contradiction.
  (* step *)
  intros edge ag' s s' HinX HinS Hadd IH edge'.
  split; intros Hin.
  (* left *)
  eapply AGProps.Add_add in Hin.
  destruct Hin as [Hsubst | Hag'].
  eapply ex_intro; split;
    [eapply Hadd; left; eapply Edge.eq_refl
    | eapply Proper_edge_subst_spec_impl; eauto; try apply Ref.eq_refl].
  eapply IH in Hag'; destruct Hag' as [edge2 [Hin Hsubst]].
  eapply ex_intro; split; [ eapply AGAddEq.Add_Subset; [apply Hadd| apply Hin]| auto].
  (* right *)
  destruct Hin as [edge2 [Hin Hsubst]].
  eapply AGProps.Add_add.
  eapply Hadd in Hin.
  destruct Hin as [Heq | Hag']; [left|right].
  eapply edge_subst_spec_eq; eauto; try apply Ref.eq_refl.
  eapply IH; eapply ex_intro; eauto.
Qed.

Hint Resolve edge_subst_spec_edge_subst.

Theorem ag_subst_spec_dec: forall e e' ag ag',
  {ag_subst_spec e e' ag ag'} + {~ ag_subst_spec e e' ag ag'}.
Proof.
  intros e e' ag ag'.
  case (AG.eq_dec ag' (ag_subst e e' ag)); intros Hcase ;[left|right].
  eapply Proper_ag_subst_spec_impl;
    [ apply Ref.eq_refl | apply Ref.eq_refl 
      | apply AG.eq_refl | apply AG.eq_sym; apply Hcase 
      | apply ag_subst_spec_ag_subst].
  intros Hspec; apply Hcase; clear Hcase.
  eapply ag_subst_spec_eq;
    [ apply Ref.eq_refl | apply Ref.eq_refl 
      | apply AG.eq_refl | apply Hspec 
      | apply ag_subst_spec_ag_subst].  
Qed.
        Theorem exists_cap_edge_capset_targets: forall C T, capset_targets C T ->
          forall tgt, (exists rgt, exists_cap_edge tgt rgt C) <-> RefSet.In tgt T.
        Proof.
          intros C T HT tgt; split; [intros [rgt [cap [Hin [Htgt Hrgt]]]] |intros Hin].
          eapply HT; clear HT; unfold exists_cap_edge in *.
          eapply ex_intro.
          split; [eauto|split; [intro Hempty; eapply Hempty; eauto| auto]].
          eapply HT in Hin; destruct Hin as [cap [Hin [Hnonempty Heq]]].
          eapply ARSetAddEq_nonempty_exists in Hnonempty; destruct Hnonempty as [rgt HinRgt].
          do 2 eapply ex_intro; unfold cap_edge; intuition eauto.
        Qed.

        Hint Resolve exists_cap_edge_capset_targets.


      Theorem ag_fully_authorized_spec_singleton_ag_subst_spec:
        forall D objs, Seq.ag_objs_spec D objs ->
        forall C T, capset_targets C T ->
        forall e, ~ RefSet.In e objs -> ~ RefSet.In e T ->
        forall e', ~ RefSet.In e' objs -> ~ RefSet.In e' T ->
          ~ Ref.eq e e' ->
        forall A, ag_fully_authorized_spec D (RefSet.singleton e) C A ->
        forall A', ag_fully_authorized_spec D (RefSet.singleton e') C A' ->
          ag_subst_spec e e' A A'.
      Proof.
        intros D objs Hobjs C T HT e He HeT e' He' HeT' Hneq A Hauth A' Hauth' edge'.
        unfold AG.Exists.
        eapply iff_trans; [apply Hauth'|].
        unfold excluded_edge.
        edge_destruct edge' src' tgt' rgt'.
        repeat progress (rewrite RefSetFacts.singleton_iff).
        split; intros Hedge'.
        destruct Hedge' as [Hedge' | [Hedge' | Hedge']].
        (* refl case *)
        destruct Hedge' as [Hsrc' Htgt']; rewrite <- Hsrc' in *; rewrite <- Htgt' in *.
        apply ex_intro with (Edges.mkEdge e e rgt'); split.
        eapply Hauth; edge_simpl; repeat progress (rewrite RefSetFacts.singleton_iff); intuition.
        unfold edge_subst_spec; repeat progress edge_simpl; intuition.
        (* auth case *)
        destruct Hedge' as [Hsrc' Hcapedge].
        rewrite <- Hsrc'.
        apply ex_intro with (Edges.mkEdge e tgt' rgt'); split.
        eapply Hauth; repeat progress edge_simpl; repeat progress rewrite RefSetFacts.singleton_iff; intuition.
        assert (~ Ref.eq tgt' e) as HneqTgt' by 
          (intros Hnot; eapply HeT; eapply exists_cap_edge_capset_targets; 
            [eapply HT 
              | eapply ex_intro; rewrite <- Hnot; eauto]).
        unfold edge_subst_spec; repeat progress edge_simpl;
          intuition (try solve [auto | apply Ref.eq_refl | apply AccessRight.eq_refl]).
        (* remainder case *)
        destruct Hedge' as [HinD [HneqSrc HneqTgt]].
        assert (~ Ref.eq e src') as HneqSrc' by
          (intros Hnot; apply He; eapply Hobjs; do 2 eapply ex_intro; rewrite Hnot; eauto).
        assert (~ Ref.eq e tgt') as HneqTgt' by
          (intros Hnot; apply He; eapply Hobjs; do 2 eapply ex_intro; rewrite Hnot; eauto).
        apply ex_intro with (Edges.mkEdge src' tgt' rgt'); split.
        eapply Hauth; unfold excluded_edge;
          repeat progress edge_simpl; repeat progress rewrite RefSetFacts.singleton_iff; intuition.
        unfold edge_subst_spec; repeat progress edge_simpl.
        unfold Ref.eq in *; intuition (try solve [auto  | apply AccessRight.eq_refl]).
        
        (* flip *)
        destruct Hedge' as [edge [HinA Hsubst]].
        eapply Hauth in HinA.
        revert HinA Hsubst; 
        unfold excluded_edge; unfold edge_subst_spec;
          edge_destruct edge src tgt rgt;
          repeat progress edge_simpl; repeat progress rewrite RefSetFacts.singleton_iff;
            intros HinA Hsubst.
        destruct Hsubst as [Hsrc [Htgt Hrgt]].
        rewrite Hrgt in *.
        destruct HinA as [Hrefl | [Hcap | Hrem]].
        (* refl case *)
        unfold Ref.eq in *.
        destruct Hrefl as [HsrcE HtgtE]; rewrite <- HsrcE in *; rewrite <- HtgtE in *.
        destruct Hsrc as [[HsrcE2 HsrcE'] |[HsrcE2 HsrcE'2]] ;[rewrite HsrcE' | contradict HsrcE2; auto].
        destruct Htgt as [[HtgtE2 HtgtE'] |[HtgtE2 HtgtE'2]] ;[rewrite HtgtE' | contradict HtgtE2; auto].
        intuition.
        (* auth case *)
        destruct Hcap as [HeqSrc Hcapedge].
        rewrite <- HeqSrc in *.
        unfold Ref.eq in *.
        destruct Hsrc as [[HsrcE2 HsrcE'] |[HsrcE2 HsrcE'2]] ;[rewrite HsrcE' | contradict HsrcE2; auto].
        destruct Htgt as [[HtgtE2 HtgtE'] |[HtgtE2 HtgtE'2]];
          [rewrite <- HtgtE' | rewrite <- HtgtE'2 ]; intuition.
        (* rem case *)
        destruct Hrem as [HinD [HneqSrc HneqTgt]].
        unfold Ref.eq in *.
        destruct Hsrc as [[HsrcE2 HsrcE'] |[HsrcE2 HsrcE'2]];[contradict HsrcE2; auto | rewrite <- HsrcE'2 ].
        destruct Htgt as [[HtgtE2 HtgtE'] |[HtgtE2 HtgtE'2]];[contradict HtgtE2; auto | rewrite <- HtgtE'2 ].
        assert (~ Ref.eq src e') as HneqSrc' by
          (intros Hnot; eapply Ref.eq_sym in Hnot; 
            apply He'; eapply Hobjs; do 2 eapply ex_intro; rewrite Hnot; eauto).
        assert (~ Ref.eq tgt e') as HneqTgt' by
          (intros Hnot; eapply Ref.eq_sym in Hnot;
            apply He'; eapply Hobjs; do 2 eapply ex_intro; rewrite Hnot; eauto).
        intuition.
      Qed.

          Theorem edge_subst_spec_refl: forall e e', Ref.eq e e' -> 
            forall edge edge', (edge_subst_spec e e' edge edge' <-> Edge.eq edge edge').
          Proof.
            unfold edge_subst_spec.
            intros e e' Heq. 
            rewrite Heq; clear e Heq.
            intros edge edge'. 
            edge_destruct edge src tgt rgt; edge_destruct edge' src' tgt' rgt'.
            split.
            intros [Hsrc [Htgt Hrgt]].
            eapply Edges.edge_equal.
            destruct Hsrc as [[Hsrc Hsrc'] | [ _ Hsrc]]; 
              rewrite Hsrc in *; try rewrite Hsrc' in *; apply Ref.eq_refl.
            destruct Htgt as [[Htgt Htgt'] | [ _ Htgt]]; 
              rewrite Htgt in *; try rewrite Htgt' in *; apply Ref.eq_refl.
            auto.
            intros HeqEdge.
            (* stolen from destructEqEdge, consider generalizing *)
            generalize (Edges.eq_source _ _ HeqEdge); intros HeqEdgeS; 
              repeat progress rewrite Edges.source_rewrite in HeqEdgeS;
                generalize (Edges.eq_target _ _ HeqEdge); intros HeqEdgeT; 
                  repeat progress rewrite Edges.target_rewrite in HeqEdgeT;
                    generalize (Edges.eq_right _ _ HeqEdge); intros HeqEdgeR; 
                      repeat progress rewrite Edges.right_rewrite in HeqEdgeR.
            rewrite HeqEdgeS; rewrite HeqEdgeT; rewrite HeqEdgeR.
            generalize (Ref.eq_dec src' e') (Ref.eq_dec tgt' e'); intros Hcase Hcase'; intuition.
          Qed.


        Theorem ag_subst_spec_refl: forall e e', Ref.eq e e' -> forall D D', ag_subst_spec e e' D D' <->
          AG.eq D D'.
        Proof.
          unfold ag_subst_spec. 
          intros e e' Heq D D'. 
          rewrite Heq. clear e Heq.

          split; 
            [intros Hsubst edge; rewrite Hsubst; clear Hsubst | intros Heq edge ];
            (split; intros H;
              [eapply ex_intro;
                split; [eauto|eapply edge_subst_spec_refl; auto; solve [apply Ref.eq_refl]]
                | destruct H as [edge' [Hin Hsubst]];
                  eapply edge_subst_spec_refl in Hsubst; [| apply Ref.eq_refl]; rewrite <- Hsubst in *; eauto]).
        Qed.



        Definition edge_free e edge := ~ Ref.eq (Edges.source edge) e /\ ~ Ref.eq (Edges.target edge) e.

        Theorem edge_subst_spec_free:
          forall e2 edge, edge_free e2 edge ->
            forall e1 edge', edge_subst_spec e1 e2 edge edge' ->
              edge_free e1 edge'.
        Proof.
          intros e2 edge [Hneq1 Hneq2] e1 edge' Hsubst.
          unfold edge_free.
          case (Ref.eq_dec e1 e2); intros Hneq; unfold edge_subst_spec in *.
          rewrite Hneq in *.
          destruct Hsubst as [[[HsrcE1 HsrcE2] | [HsrcE1 Hsrc']] [[[HtgtE1 HtgtE2] | [HtgtE1 Htgt']] Hrgt]];
            solve [contradiction | rewrite Hsrc' in *; rewrite Htgt' in *; split; eauto].

          destruct Hsubst as [[[HsrcE1 HsrcE2] | [HsrcE1 Hsrc']] [[[HtgtE1 HtgtE2] | [HtgtE1 Htgt']] Hrgt]];
          try rewrite HsrcE1 in *; try rewrite HsrcE2 in *; try rewrite Hsrc' in *;
          try rewrite HtgtE1 in *; try rewrite HtgtE2 in *; try rewrite Htgt' in *;
          unfold Ref.eq in *; intuition eauto.
        Qed.


        (* This was writtine before edge_subst_spec_free, you may wish to alter it later *)
        Theorem ag_subst_spec_free : 
        forall D Dobjs, Seq.ag_objs_spec D Dobjs ->
        forall D' D'objs, Seq.ag_objs_spec D' D'objs ->
        forall e', ~ RefSet.In e' Dobjs ->
        forall e, ag_subst_spec e e' D D' ->
          ~ RefSet.In e D'objs.
        Proof.
          intros D Dobjs HDobjs D' D'objs HD'objs e' He' e Hsubst Hnot.
          eapply He'; clear He'; eapply HDobjs; clear Dobjs HDobjs.

          eapply HD'objs in Hnot; clear D'objs HD'objs.

          destruct Hnot as [obj [rgt' [Hnot | Hnot]]];
            (eapply Hsubst in Hnot; clear D' Hsubst;
            destruct Hnot as [edge Hin];
            revert Hin;
            edge_destruct edge src tgt rgt;
            intros [Hin [[[Hsrc HeqSrc]|[HneqSrc Hsrc]] [[[Htgt HeqTgt]|[HneqTgt Htgt]] Hrgt]]];
            repeat progress edge_simpl;
              solve [ contradiction 
                | rewrite Hsrc in Hin; try rewrite HeqSrc in Hin;
                  rewrite Htgt in Hin; try rewrite HeqTgt in Hin;
                    do 2 eapply ex_intro; eauto
               ]).
        Qed.

        Theorem ag_free_edge_free :
          forall D Dobjs, Seq.ag_objs_spec D Dobjs ->
            forall e, ~ RefSet.In e Dobjs ->
              AG.For_all (fun edge => edge_free e edge) D.
        Proof.
          unfold AG.For_all.
          intros D Dobjs HDobjs e Hfree edge.
          edge_destruct edge src tgt rgt; intros HinD.
          split; (edge_simpl; intros Heq; apply Hfree;
            apply HDobjs; rewrite Heq in *;
              do 2 eapply ex_intro; eauto 2).
        Qed.

        Theorem edge_subst_free_sym:
          forall e2 edge1, edge_free e2 edge1 ->
          forall e1 edge2, edge_subst_spec e1 e2 edge1 edge2 ->
          edge_subst_spec e2 e1 edge2 edge1.
          Proof.
            intros e2 edge1 He2Free e1 edge2 Hsubst.
            destruct He2Free as [He2FreeSrc He2FreeTgt].
            unfold edge_subst_spec in *.
            destruct Hsubst as [[[HsrcE1 HsrcE2] | [HsrcE1 Hsrc']] [[[HtgtE1 HtgtE2] | [HtgtE1 Htgt']] Hrgt]];
            unfold Ref.eq in *;
            try rewrite Hsrc' in *; try rewrite HsrcE1 in *; try rewrite HsrcE2 in *;
            try rewrite Htgt' in *; try rewrite HtgtE1 in *; try rewrite HtgtE2 in *;
              (intuition auto; try (apply AccessRight.eq_sym; auto)).
          Qed.

          Theorem Proper_edge_free_impl: Proper (Ref.eq ==> Edge.eq ==> impl) edge_free.
          Proof.
            unfold Proper; unfold respectful; unfold impl; unfold edge_free.
            intros x y H x0 y0 H0; rewrite H;
            rewrite (Edges.eq_source _ _ H0);
            rewrite (Edges.eq_target _ _ H0).
            auto.            
          Qed.



Theorem edge_subst_spec_eq_l : 
  forall e e2 edge edge2, edge_subst_spec e e2 edge edge2 ->
    edge_free e2 edge -> 
  forall edge', edge_subst_spec e e2 edge' edge2 ->
    edge_free e2 edge' ->
    Edge.eq edge edge'.
Proof.
  intros e e2 edge edge2 Hsubst [HneqSrc HneqTgt] edge';
    revert Hsubst HneqSrc HneqTgt.
  unfold edge_subst_spec in *;   unfold edge_free.
  edge_destruct edge src tgt rgt.
  edge_destruct edge' src' tgt' rgt'.
  edge_destruct edge2 src2 tgt2 rgt2.
  intros [Hsrc [Htgt Hrgt]] HneqSrc HneqTgt [Hsrc' [Htgt' Hrgt']] [HneqSrc' HneqTgt'].
  rewrite Hrgt; rewrite Hrgt'. clear rgt' rgt Hrgt Hrgt'.
  unfold Ref.eq in *.
  intuition; try solve [repeat progress ( try rewrite He in *; try rewrite He2 in *;
    try rewrite H0 in *; try rewrite H1 in *; try rewrite H2 in *; try rewrite H3 in *;
      try rewrite H4 in *; try rewrite H5 in *; try rewrite H6 in *; try rewrite H7 in *);
  solve [contradiction HneqSrc; eauto 2
| contradiction HneqTgt; eauto 2
| contradiction HneqSrc'; eauto 2 
| contradiction HneqTgt'; eauto 2 ]
| eapply Edges.edge_equal; unfold Ref.eq; eauto 2; try apply AccessRight.eq_refl].
Qed.  

Hint Resolve edge_subst_spec_eq_l.


      Theorem ag_subst_free_sym:
        forall A Aobjs, Seq.ag_objs_spec A Aobjs ->
        forall e2, ~ RefSet.In e2 Aobjs ->
        forall e1 B, ag_subst_spec e1 e2 A B ->
          ag_subst_spec e2 e1 B A.
      Proof.
        intros A Aobjs HAobjs e2 He2Free e1 B Hsubst.
        generalize (Seq.ag_objs_spec_ag_objs B) He2Free; generalize (Seq.ag_objs B);
          intros Bobjs HBobjs He1Free.
        eapply ag_subst_spec_free in He1Free;
          [ | apply HAobjs | apply HBobjs | apply Hsubst ].
        intros edge.

        split; [intros Hin| intros [edge' [HinB Hexcluded]]].
        eapply ex_intro.
        split; [|
          eapply edge_subst_free_sym;
            [eapply ag_free_edge_free with (Dobjs:=Aobjs); eauto 1 | eauto 1]].
        eapply Hsubst; eapply ex_intro; split; eauto.

        generalize HinB; intros HedgeFree.
        eapply ag_free_edge_free in HedgeFree;
           [ | apply HBobjs |  apply He1Free].
        eapply edge_subst_spec_free in HedgeFree; [| eapply Hexcluded].

        eapply edge_subst_free_sym in Hexcluded; 
          [ | eapply ag_free_edge_free with (Dobjs:=Bobjs); eauto 1].
        generalize HinB; intros HinA; eapply Hsubst in HinA.
        destruct HinA as [edge2 [HinA Hedge_subst2]].

        rewrite edge_subst_spec_eq_l.
        apply HinA.
        eauto 1.
        eauto 1.
        eauto 1.
        eapply ag_free_edge_free; [apply HAobjs | apply He2Free | apply HinA].
      Qed.

      

      (* Now show that an ag_subst has the same mutability for free objs*)
      Theorem mutable_ag_subst_spec :
        forall D Dobjs, Seq.ag_objs_spec D Dobjs ->
        forall D' D'objs, Seq.ag_objs_spec D' D'objs ->
        forall e', ~ RefSet.In e' Dobjs ->
        forall e, ag_subst_spec e e' D D' ->
        forall M, mutable_spec D (RefSet.singleton e) M ->
        forall M', mutable_spec D' (RefSet.singleton e') M' ->
          RefSet.eq M' (RefSet.add e' (RefSet.remove e M)).
      Proof.
        intros D Dobjs HDobjs D' D'objs HD'objs e' He'Free e Hsubst M HM M' HM'.
        case (Ref.eq_dec e e'); intros Hcase.
        rewrite <- Hcase.
        rewrite RefSetProps.add_remove; 
          [| eapply mutable_nondec; [apply HM| eapply RefSetFacts.singleton_iff; auto]].
        eapply mutable_spec_eq_iff;
          [eapply HM'
            | 
            | apply RefSet.eq_refl
            | eapply Proper_mutable_spec; 
              [apply AG.eq_refl | rewrite <- Hcase; apply RefSet.eq_refl | apply RefSet.eq_refl| apply HM]].
        eapply AG.eq_sym; eapply ag_subst_spec_refl; eauto.

        (* now e <> e' *)
        intros m'.
        RefSetFacts.set_iff.
        rewrite (HM' m'); rewrite (HM m'); clear M M' HM HM'.
        repeat progress rewrite RefSetFacts.singleton_iff.
        case (Ref.eq_dec e' m'); intros Hcase'; try solve [intuition].
        split; intros Hiff.
        destruct Hiff as [Heq | [e0 [Heq Hin]]]; try contradiction.
        rewrite RefSetFacts.singleton_iff in Heq; rewrite <- Heq in *; clear e0 Heq.
        (* we know that e [<>] m', as ~ In e D'objs and In m' D'objs *)
        generalize He'Free; intros HeFree.
        eapply ag_subst_spec_free in HeFree; [
          | eauto 1
          | apply HD'objs
          | eauto 1].
        assert (~ Ref.eq e m') as Hneq by
          (intros Hnot; rewrite Hnot in *; apply HeFree; apply HD'objs; 
            destruct Hin as [Hin | [Hin | [Hin | Hin]]]; do 2 eapply ex_intro; eauto).
        unfold Ref.eq in *.
        right; split; [right|auto].
        apply ex_intro with e.
        split ; [apply RefSetFacts.singleton_iff; auto|].

        Ltac assert_neq_helper He'Free HDobjs :=
          let Hnot := fresh "Hnot" in
          intros Hnot; rewrite Hnot in *; apply He'Free; apply HDobjs; do 2 eapply ex_intro; eauto.

        Ltac case_neq_helper H :=
          destruct H as [[_ H] | H];
            [apply Ref.eq_sym in H; contradiction H |intuition].

        Ltac case_D'_impl_D Hsubst Hin e' He'Free HDobjs:=
        eapply Hsubst in Hin;
        destruct Hin as [edge Hin];
        revert Hin;
        let src := fresh "src" in let tgt := fresh "tgt" in let rgt := fresh "rgt" in
        edge_destruct edge src tgt rgt;
        let Hin := fresh "Hin" in let Hsrc := fresh "Hsrc" in
        let Htgt := fresh "Htgt" in let Hrgt := fresh "Hrgt" in 
        intros [Hin [Hsrc [Htgt Hrgt]]];
        repeat progress edge_simpl;
        eapply AGFacts.In_eq_iff; [| apply Hin];
        eapply Edges.edge_equal;
          solve
          [assert (~ Ref.eq src e') by (assert_neq_helper He'Free HDobjs); intuition
            | assert (~ Ref.eq tgt e') by (assert_neq_helper He'Free HDobjs); intuition
            | eapply Ref.eq_sym; solve[case_neq_helper Htgt|case_neq_helper Hsrc]
            | apply AccessRight.eq_sym; auto].

        do 3 (destruct Hin as [Hin | Hin]; [left; case_D'_impl_D Hsubst Hin e' He'Free HDobjs |right]);
          case_D'_impl_D Hsubst Hin e' He'Free HDobjs.

        (* flip *)
        destruct Hiff as [Hnot | [[Hnot | [e0 [Heq Hin]]] Hneq]]; try contradiction.
        eapply RefSetFacts.singleton_iff in Heq; rewrite <- Heq in *; clear e0 Heq.
        right; apply ex_intro with e'; split; [eapply RefSetFacts.singleton_iff; auto |].

        Ltac case_D_impl_D' Hsubst:= 
        eapply Hsubst;
        eapply ex_intro; split; try solve [eauto];
        split; repeat progress edge_simpl; [|split;[|apply AccessRight.eq_refl]]; try solve [intuition].

        do 3 (destruct Hin as [Hin | Hin]; [left; case_D_impl_D' Hsubst |right]); case_D_impl_D' Hsubst.
      Qed.

      Theorem mutable_subset_objs :
        forall D objs,  Seq.ag_objs_spec D objs ->
          forall E M, mutable_spec D E M ->
            RefSet.Subset M (RefSet.union E objs).
      Proof.
        intros D objs Hobjs E M HM x Hin.
        apply HM in Hin.
        RefSetFacts.set_iff.
        destruct Hin as [Hin | Hin]; [left;auto|right].
        destruct Hin as [e [HinE HinD]].
        apply Hobjs.
        destruct HinD as [HinD | [HinD | [HinD | HinD]]];
        do 2 eapply ex_intro; eauto.
      Qed.
        



      Theorem ag_subst_split:
        forall A Aobjs, Seq.ag_objs_spec A Aobjs ->
        forall e2, ~ RefSet.In e2 Aobjs ->
        forall e1 B, ag_subst_spec e1 e2 A B -> 
        forall A', AG.Subset A' A ->
        exists B', AG.Subset B' B /\
          ag_subst_spec e1 e2 A' B' /\ 
          ag_subst_spec e1 e2 (AG.diff A A') (AG.diff B B').
      Proof.
        intros A Aobjs HAobjs e2 He2Free e1 B Hsubst A' Hsub.
        eapply ex_intro.
        split;[|split;[eapply ag_subst_spec_ag_subst|]].
        intros edge. 
        edge_destruct edge src tgt rgt.
        intros HinE.
        eapply Hsubst.
        eapply ag_subst_spec_ag_subst in HinE.
        destruct HinE as [edge' HinA'].
        revert HinA'; edge_destruct edge' src' tgt' rgt'; intros [HinA' Hsubst']; 
          repeat progress edge_simpl.
        eapply Hsub in HinA'.
        eapply ex_intro; split; eauto 1.

        intros edge.
        edge_destruct edge src tgt rgt.
        split; AGFacts.set_iff; intros H.

        destruct H as [HinB HninSubst].
        eapply Hsubst in HinB.
        destruct HinB as [edge HinA].
        revert HinA; edge_destruct edge src' tgt' rgt'; intros [HinA Hsubst'].
        eapply ex_intro; AGFacts.set_iff; split;[|eauto 1].
        split; [eauto 1|].
        intros Hnot; apply HninSubst.
        eapply ag_subst_spec_ag_subst.
        eapply ex_intro; eauto.

        destruct H as [edge' HinA]; revert HinA; edge_destruct edge' src' tgt' rgt'; 
          AGFacts.set_iff; intros [[HinA HninA'] Hsubst'].
        split.
        eapply Hsubst; eapply ex_intro; eauto.
        intros Hnot; apply HninA'.
        eapply ag_subst_spec_ag_subst in Hnot.
        destruct Hnot as [edge2 Hnot]; revert Hnot; edge_destruct edge2 src2 tgt2 rgt2.
        intros [HinA' Hsubst2].

        Ltac solve_eq_edge_l He2Free HAobjs := let Hnot := fresh "Hnot" in 
          intros Hnot; apply He2Free;
            eapply HAobjs;
              do 2 eapply ex_intro; rewrite Hnot; eauto 2.

        rewrite edge_subst_spec_eq_l;
          [apply HinA'
            | eauto 1
            | eapply ag_free_edge_free; [apply HAobjs | apply He2Free | apply HinA]
            | eauto 1
            | eapply ag_free_edge_free; [apply HAobjs | apply He2Free | apply Hsub; apply HinA']].
      Qed.




      Theorem ag_subst_union:
        forall e1 e2 A B, ag_subst_spec e1 e2 A B -> 
        forall A' B', ag_subst_spec e1 e2 A' B' -> 
          ag_subst_spec e1 e2 (AG.union A A') (AG.union B B').
      Proof.
        intros e1 e2 A B Hsubst A' B' Hsubst'.
        intros edge.
        AGFacts.set_iff.
        split; intros H.
        destruct H as [H | H];
        [eapply Hsubst in H | eapply Hsubst' in H];
        (destruct H as [edge' [HinEdge' HsubstEdge']];
          eapply ex_intro; AGFacts.set_iff; eauto).

        destruct H as [edge' [HinEdge' HsubstEdge']]; 
          revert HinEdge'; AGFacts.set_iff; intros [HinEdge' | HinEdge'];
            [left; eapply Hsubst |right; eapply Hsubst'];
            (eapply ex_intro; eauto).
      Qed.

        Theorem edge_subst_ag_subst_singleton:
          forall e1 e2 a b, edge_subst_spec e1 e2 a b <-> ag_subst_spec e1 e2 (AG.singleton a) (AG.singleton b).
        Proof.
          intros e1 e2 a b.
          split; intros H.
          intros edge; split; intros H'.
          eapply AGFacts.singleton_iff in H'.
          eapply ex_intro.
          split; [eapply AGFacts.singleton_iff; apply Edge.eq_refl|].
          eapply Proper_edge_subst_spec_iff;
            [ apply Ref.eq_refl | apply Ref.eq_refl | apply Edge.eq_refl | apply Edge.eq_sym; apply H' | apply H].
          destruct H' as [edge' [HinA Hedge']].
          eapply AGFacts.singleton_iff in HinA.
          rewrite AGFacts.singleton_iff.
          eapply edge_subst_spec_eq;
            [eapply Ref.eq_refl | apply Ref.eq_refl | apply HinA | apply H | apply Hedge'].

          generalize (H b); clear H; intros [H _].
          rewrite AGFacts.singleton_iff in H.
          generalize (H (Edge.eq_refl _)); clear H; intros [edge [HinA Hedge]].
          rewrite AGFacts.singleton_iff in HinA.
          eapply Proper_edge_subst_spec_iff;
            [ apply Ref.eq_refl | apply Ref.eq_refl | apply HinA | apply Edge.eq_refl | apply Hedge ].
        Qed.

        Hint Resolve edge_subst_ag_subst_singleton.

      Theorem ag_subst_add:
        forall e1 e2 A B, ag_subst_spec e1 e2 A B -> 
        forall a b, edge_subst_spec e1 e2 a b ->
          ag_subst_spec e1 e2 (AG.add a A) (AG.add b B).
      Proof.
        intros e1 e2 A B Hsubst a b Hedge.
        eapply Proper_ag_subst_spec_impl;
          [apply Ref.eq_refl | apply Ref.eq_refl |
            apply AG.eq_sym; eapply AGProps.add_union_singleton |
              apply AG.eq_sym; eapply AGProps.add_union_singleton | ].
        eapply ag_subst_union; eauto.
        eapply edge_subst_ag_subst_singleton; auto.
      Qed.

      (* This combines the previous theorem and equality to help for trans *)
      Theorem ag_subst_Add_eq:
        forall e1 e2 A B, ag_subst_spec e1 e2 A B -> 
        forall a b, edge_subst_spec e1 e2 a b ->
        forall A', AGProps.Add a A A' ->
        forall B', ag_subst_spec e1 e2 A' B' ->
          AGProps.Add b B B'.
      Proof.
        intros e1 e2 A B Hsubst a b Hedge A' HaddA' B' Hsubst'.
        eapply ag_subst_add in Hsubst; [|eauto 1].
        eapply ag_subst_spec_eq in Hsubst;
          [ | apply Ref.eq_refl | apply Ref.eq_refl | | apply Hsubst'].
        eapply AGAddEq.Add_eq_complete;
          [apply Edge.eq_refl |  apply AG.eq_refl | apply AG.eq_sym; apply Hsubst | apply AGProps.Add_add ].
        apply AG.eq_sym;
        eapply AGAddEq.Eq_Add_complete;
          [apply Edge.eq_refl |  apply AG.eq_refl | apply AGProps.Add_add | apply HaddA'].
      Qed.

      Theorem trans_ag_subst :
        forall D Dobjs, Seq.ag_objs_spec D Dobjs ->
        forall e', ~ RefSet.In e' Dobjs ->
        forall e D', ag_subst_spec e e' D D' ->
        forall D2, Seq.transfer D D2 ->
        forall D2', ag_subst_spec e e' D2 D2' ->
          Seq.transfer D' D2'.
      Proof.
        intros D Dobjs HDobjs e' He'free e D' Hsubst D2 Htrans D2' Hsubst2.
        destruct Htrans.
        (* self src *)
        generalize H0; intros H0'.
        eapply ag_subst_Add_eq in H0';
          [ | apply Hsubst | apply edge_subst_spec_edge_subst | apply Hsubst2 ].
        eapply Seq.transfer_self_src.
        eapply Hsubst.
        eapply ex_intro; split; [ apply H|].
        eapply edge_subst_spec_edge_subst.
        edge_simpl.
        eapply H0'.
        (* self tgt *)
        generalize H0; intros H0'.
        eapply ag_subst_Add_eq in H0;
          [ | apply Hsubst | apply edge_subst_spec_edge_subst | apply Hsubst2 ].
        eapply Seq.transfer_self_tgt.
        eapply Hsubst.
        eapply ex_intro; split; [ apply H|].
        eapply edge_subst_spec_edge_subst.
        edge_simpl.
        eapply H0.
        (* read *)
        Ltac generalize_ag_subst_Add HAdd HAdd' Hsubst Hsubst2:=
        generalize HAdd; intros HAdd';
        eapply ag_subst_Add_eq in HAdd';
          [ | apply Hsubst | apply edge_subst_spec_edge_subst | apply Hsubst2 ].
        generalize_ag_subst_Add H1 HAdd' Hsubst Hsubst2.
        Ltac solve_with_edge_subst Hsubst HinD :=
        eapply Hsubst; eapply ex_intro; split; [ eapply HinD|eapply edge_subst_spec_edge_subst].
        eapply Seq.transfer_read;
          [ solve_with_edge_subst Hsubst H 
            | solve_with_edge_subst Hsubst H0
            | eapply HAdd'].
        (* write *)
        generalize_ag_subst_Add H1 HAdd' Hsubst Hsubst2.
        eapply Seq.transfer_write.
        solve_with_edge_subst Hsubst H .
        2: eapply HAdd'.
        solve_with_edge_subst Hsubst H0.
        (* send *)
        generalize_ag_subst_Add H1 HAdd' Hsubst Hsubst2.
        eapply Seq.transfer_send.
        3: eapply HAdd'.
        solve_with_edge_subst Hsubst H .
        solve_with_edge_subst Hsubst H0.
        (* reply *)
        generalize_ag_subst_Add H0 HAdd' Hsubst Hsubst2.
        eapply Seq.transfer_send_reply.
        2: eapply HAdd'.
        solve_with_edge_subst Hsubst H .
        (* weak *)
        generalize_ag_subst_Add H2 HAdd' Hsubst Hsubst2.
        destruct H1 as [Hrgt | Hrgt]; rewrite Hrgt in *.
        eapply Seq.transfer_weak.
        4: eapply HAdd'.
        3: intuition (eapply Hrgt).
        edge_simpl; solve_with_edge_subst Hsubst H .
        edge_simpl; solve_with_edge_subst Hsubst H0 .
        eapply Seq.transfer_weak.
        4: eapply HAdd'.
        3: right; apply Hrgt.
        edge_simpl; solve_with_edge_subst Hsubst H .
        repeat progress (edge_simpl). rewrite Hrgt. solve_with_edge_subst Hsubst H0 .
      Qed.


      (* *)

Theorem ag_subst_spec_free_eq : 
  forall A Aobjs, Seq.ag_objs_spec A Aobjs ->
  forall e2, ~ RefSet.In e2 Aobjs ->
  forall A' A'objs, Seq.ag_objs_spec A' A'objs ->
    ~ RefSet.In e2 A'objs ->
  forall e1 B, ag_subst_spec e1 e2 A B ->
  forall B', ag_subst_spec e1 e2 A' B' ->
    (AG.eq A A' <-> AG.eq B B').
Proof.
  intros A Aobjs HAobjs e2 He2Free A' A'objs HA'objs He2Free' e1 B Hsubst B' Hsubst'.
  split; intros H.
  eapply ag_subst_spec_eq; eauto; solve [apply Ref.eq_refl].

  generalize (Seq.ag_objs_spec_ag_objs B); generalize (Seq.ag_objs B); intros Bobjs HBobjs.
  generalize Hsubst; intros He1Free.
  eapply ag_subst_spec_free in He1Free; eauto 1.

  eapply ag_subst_free_sym in Hsubst; eauto 1.
  eapply ag_subst_free_sym in Hsubst'; eauto 1.

  eapply ag_subst_spec_eq; eauto; solve [apply Ref.eq_refl].
Qed.


      Theorem potTransfer_ag_subst :
        forall D Dobjs, Seq.ag_objs_spec D Dobjs ->
        forall e', ~ RefSet.In e' Dobjs ->
        forall e D', ag_subst_spec e e' D D' ->
        forall D2, Seq.potTransfer D D2 ->
        forall D2', ag_subst_spec e e' D2 D2' ->
          Seq.potTransfer D' D2'.
      Proof.
        intros D Dobjs HDobjs e' He'Free e D' Hsubst D2 HpotTransfer.
        induction HpotTransfer as [C H | C B HpotTransfer IH Htrans]; intros D2' Hsubst2. 
        eapply ag_subst_spec_eq in Hsubst;
          [eapply Seq.potTransfer_base; apply AG.eq_sym; apply Hsubst
            | apply Ref.eq_refl
            | apply Ref.eq_refl
            | apply AG.eq_sym; apply H
            | apply Hsubst2].
        generalize (IH _ (ag_subst_spec_ag_subst _ _ _)); clear IH; intros IH.
        eapply trans_ag_subst in Htrans;
          [ 
            | eapply ag_objs_spec_potTransfer; [apply HDobjs | apply HpotTransfer]
            | apply He'Free
            | eapply ag_subst_spec_ag_subst
            | eapply Hsubst2].
        eapply Seq.potTransfer_trans; eauto.
      Qed.

        Theorem maxTransfer_ag_subst_spec :
          forall P, Seq.maxTransfer P ->
          forall Pobjs, Seq.ag_objs_spec P Pobjs ->
          forall e', ~ RefSet.In e' Pobjs ->
          forall e P', ag_subst_spec e e' P P' ->
            Seq.maxTransfer P'.
          Proof.
            intros P HP Pobjs HPobjs e' He'Free e P' Hsubst D Htrans.
            generalize (Seq.ag_objs_spec_ag_objs P'); generalize (Seq.ag_objs P'); intros P'objs HP'objs.
            generalize HP'objs; intros HeFree.
            eapply ag_subst_spec_free in HeFree;
              [ | apply HPobjs | apply He'Free | apply Hsubst].
            
            generalize Htrans; intros HDobjs.
            eapply ag_objs_spec_transfer in HDobjs; [|apply HP'objs].

            generalize Hsubst; intros HsubstRev;
            eapply ag_subst_free_sym in HsubstRev; eauto 1.
            
            eapply trans_ag_subst in Htrans;
            [ | apply HP'objs | apply HeFree | apply HsubstRev | apply ag_subst_spec_ag_subst ].
            
            eapply HP in Htrans.
            eapply Proper_ag_subst_spec_impl in HsubstRev;
              [ | apply Ref.eq_refl | apply Ref.eq_refl | apply AG.eq_refl | apply Htrans].

            eapply Proper_ag_objs_spec in HPobjs;
            [ | apply AG.eq_sym; apply Htrans | apply RefSet.eq_refl].
            
            generalize (ag_subst_spec_ag_subst e' e D); intros HsubstRev'.

            eapply ag_subst_free_sym in HsubstRev; eauto 1.
            eapply ag_subst_free_sym in HsubstRev';
              [ | apply HDobjs | apply HeFree].

            eapply ag_subst_spec_eq;
              [ apply Ref.eq_refl| apply Ref.eq_refl| apply AG.eq_refl| eauto 1 | eauto 1].

          Qed.



      Theorem ag_subst_potAcc:
        forall D Dobjs, Seq.ag_objs_spec D Dobjs ->
        forall e', ~ RefSet.In e' Dobjs ->
        forall D' e, ag_subst_spec e e' D D' -> 
        forall P, Seq.potAcc D P ->
        forall P', Seq.potAcc D' P' ->
          ag_subst_spec e e' P P'.
      Proof.
        intros D Dobjs HDobjs e' He'Free D' e Hsubst P HP P' HP'.

        generalize (Seq.ag_objs_spec_ag_objs D'); generalize (Seq.ag_objs D'); intros D'objs HD'objs.
        generalize He'Free; intros HeFree;
        eapply ag_subst_spec_free in HeFree; [
          | eauto 1
          | apply HD'objs
          | eauto 1].

        destruct HP as [Htrans Hmax]; destruct HP' as [Htrans' Hmax'].


(* 
This should work.

By ag_objs_spec_potTransfer : Seq.ag_objs_spec P Dobjs /\ Seq.ag_objs_spec P' D'objs.
By ag_subst_spec_ag_subst : ag_subst_spec e e' P (ag_subst e e' P)
By potTransfer_ag_subst: potTransfer D' (ag_subst e e' P).
Therefore: Seq.maxPotTransfer P' -> Seq.potTransfer D' P' -> Seq.potTransfer D' (ag_subst e e' P) ->
    P' [=] (ag_subst e e' P)
By ag_subst_spec_eq, the goal becomes ag_subst_spec e e' P (ag_subst e e' P) which is of course
ag_subst_spec_ag_subst.

*)

        generalize Htrans; intros HPobjs; eapply ag_objs_spec_potTransfer in HPobjs; [|eapply HDobjs].
        generalize Htrans'; intros HP'objs; eapply ag_objs_spec_potTransfer in HP'objs; [|eapply HD'objs].
        generalize (ag_subst_spec_ag_subst e e' P); intros HPsubst.
        generalize HPsubst; intros HPsubst'.
        eapply maxTransfer_ag_subst_spec in HPsubst';
          [ | apply Seq.maxTransfer_maxPotTransfer; eauto | eauto |  eauto].

        eapply potTransfer_ag_subst in HPsubst;
          [ | apply HDobjs | apply He'Free | apply Hsubst | apply Htrans].
        
        eapply Proper_ag_subst_spec_impl;
          [ eapply Ref.eq_refl | eapply Ref.eq_refl | eapply AG.eq_refl | | apply ag_subst_spec_ag_subst].

        eapply potAcc_equiv;
          [apply AG.eq_refl | split; [apply HPsubst | apply Seq.maxTransfer_maxPotTransfer; eauto] | split; eauto].
      Qed.

      Theorem mutable_ag_subst_spec_diff :
        forall D Dobjs, Seq.ag_objs_spec D Dobjs ->
        forall D' D'objs, Seq.ag_objs_spec D' D'objs ->
        forall e, ~ RefSet.In e D'objs ->
        forall e', ~ RefSet.In e' Dobjs ->
          ag_subst_spec e e' D D' ->
        forall P, Seq.potAcc D P ->
        forall P', Seq.potAcc D' P' ->
        forall M, mutable_spec P (RefSet.singleton e) M ->
        forall M', mutable_spec P' (RefSet.singleton e') M' ->
          RefSet.eq (RefSet.diff M (RefSet.singleton e)) (RefSet.diff M' (RefSet.singleton e')).
      Proof.
        intros D Dobjs HDobjs D' D'objs HD'objs e HeFree e' He'Free Hsubst P HP P' HP' M HM M' HM'.
        repeat progress rewrite <- RefSetProps.remove_diff_singleton.
        rewrite mutable_ag_subst_spec with (D:=P) (D':=P') (M:=M) (M':=M');
          try solve [eapply ag_objs_spec_potTransfer; [apply HDobjs|apply HP]
            | eapply ag_objs_spec_potTransfer; [apply HD'objs|apply HP']
              | eapply ag_subst_potAcc; eauto 2
              | eauto 2].
        rewrite RefSetProps.remove_add; [apply RefSet.eq_refl|].
        RefSetFacts.set_iff.
        intros [HinM Hneq].
        eapply mutable_subset_objs in HinM;
          [ | eapply ag_objs_spec_potTransfer; [apply HDobjs|apply HP] | apply HM].
        revert HinM; RefSetFacts.set_iff; intros [HinM | HinM]; contradiction.
        eapply ag_subst_potAcc;
        [ apply HDobjs | apply He'Free | apply Hsubst | apply HP | apply HP'].
      Qed.

      Theorem mutable_ag_fully_authorized_singleton:
        forall D objs, Seq.ag_objs_spec D objs ->
        forall C T, capset_targets C T ->
        forall e, ~ RefSet.In e objs -> ~ RefSet.In e T ->
        forall e', ~ RefSet.In e' objs -> ~ RefSet.In e' T ->
        forall A, ag_fully_authorized_spec D (RefSet.singleton e) C A ->
        forall A', ag_fully_authorized_spec D (RefSet.singleton e') C A' ->
        forall P, Seq.potAcc A P ->
        forall P', Seq.potAcc A' P' ->
        forall M, mutable_spec P (RefSet.singleton e) M ->
        forall M', mutable_spec P' (RefSet.singleton e') M' ->
          RefSet.eq (RefSet.diff M (RefSet.singleton e)) (RefSet.diff M' (RefSet.singleton e')).
        Proof.
          intros D objs Hobjs C T HT e HeNodes HeTargets e' HeNodes' HeTargets' A Hauth A' Hauth'
            P HP P' HP' M HM M' HM'.
          (* first by eq_dec e e' cases *)
          case (Ref.eq_dec e e'); intros Hcase; [rewrite <- Hcase in *|].
          rewrite mutable_spec_eq_iff with (m := M');
            [apply RefSet.eq_refl
              | eauto 1
              | eapply potAcc_equiv; try solve [apply HP | apply HP'];
                eapply ag_fully_authorized_spec_eq; 
                  solve [apply AG.eq_refl | apply RefSet.eq_refl | apply CapSet.eq_refl | eauto 1]
              | apply RefSet.eq_refl
              | apply HM ].

          (* e [<>] e' *)

          Ltac not_in_ag_objs_ag_fully_authorized Hauth' HeNodes Hobjs:=
            let Hnot := fresh "Hnot" in 
          intros Hnot;
          rewrite ag_objs_ag_fully_authorized in Hnot;
            [ 
              | eauto 1
              | let Hnot := fresh "Hnot" in 
                intros Hnot; eapply Hnot; apply RefSetFacts.singleton_iff; apply Ref.eq_refl
              | apply ag_remainder_spec_iff
              | apply Seq.ag_objs_spec_ag_objs
              | apply Hauth'
              | apply Seq.ag_objs_spec_ag_objs];
           revert Hnot; RefSetFacts.set_iff; intros Hnot;
              destruct Hnot as [Hnot | [Hnot | Hnot]]; try solve [contradict Hnot; eauto];
              apply HeNodes; apply Hobjs;
              apply Seq.ag_objs_spec_ag_objs in Hnot;
              let obj := fresh "obj" in let rgt := fresh "rgt" in
              destruct Hnot as [obj [rgt [Hnot|Hnot]]];
              eapply ag_remainder_spec_iff in Hnot;
              destruct Hnot as [Hnot _];
              do 2 eapply ex_intro; eauto.

          eapply mutable_ag_subst_spec_diff;
            [ eapply Seq.ag_objs_spec_ag_objs
              | eapply Seq.ag_objs_spec_ag_objs
              | not_in_ag_objs_ag_fully_authorized Hauth' HeNodes Hobjs
              | not_in_ag_objs_ag_fully_authorized Hauth HeNodes' Hobjs
              | eapply ag_fully_authorized_spec_singleton_ag_subst_spec; eauto 1
              | eauto 1
              | eauto 1
              | eauto 1
              | eauto 1
            ]. 
        Qed.

    Theorem ag_objs_ag_remainder_subset:
      forall D Nd, Seq.ag_objs_spec D Nd ->
      forall E R, ag_remainder_spec D E R ->
      forall Nr, Seq.ag_objs_spec R Nr ->
        RefSet.Subset Nr (RefSet.diff Nd E).
    Proof.
      intros D Nd HNd E R HR Nr HNr x.
      RefSetFacts.set_iff.
      rewrite (HNr x); rewrite (HNd x); 
      intros [obj [rgt [HinR | HinR]]];
      (eapply HR in HinR;
      destruct HinR as [HinD [HninS HninT]]; edge_simpl;
      split; [do 2 eapply ex_intro; eauto | eauto]).
    Qed.



    (* Since we know M' [=] (union M (diff E' E)) ,
       Our goal is:
         (M + (E' - E)) - E' [=] M - E
         ((E' - E) + M) - E' [=] M - E)
       We know:
         E [<=] M and E [<=] E'.
       This means:
         E [<=] M -> M [=] ((M - E) + E)
       By subst, our goal is:
         ((E' - E) + M) - E' [=] M - E)
         ((E' - E) + (M - E) + E) - E' [=] M - E.
       Notice that we are unioning 3 disjoint sets: (diff E' E) (diff M E) and E, and subtracting E' from all.
       By subset replacement
         E [<=] E' -> E' [=] (E' - E) + E
       By subst:
         ((E' - E) + (M - E) + E) - ((E' - E) + E) [=] M - E.
         ((M - E) + (E' - E) + E) - ((E' - E) + E) [=] M - E.
         ((M - E) + ((E' - E) + E)) - ((E' - E) + E) [=] M - E.
       Because of disjointness, the common factors cancel out:
         ((M - E) + ((E' - E) + E)) - ((E' - E) + E) [=] M - E.
         M - E [=] M - E
         Refl.
        *)


    (* The constraint (RefSet.Empty (RefSet.inter E objs)) will evaporate by using the remainder *)
  Theorem ag_fully_authorized_mutable_subset_eq_diff :
    forall D objs, Seq.ag_objs_spec D objs ->
    forall N, RefSet.Subset objs N ->
    forall E, ~ RefSet.Empty E ->
      RefSet.Empty (RefSet.inter E objs) ->
      RefSet.Subset E N ->
    forall E', RefSet.Subset E E' ->
      filtered_subset_eq E E' N ->
    forall C T, capset_targets C T -> 
      RefSet.Subset T N ->
    forall A, ag_fully_authorized_spec D E C A ->
    forall A', ag_fully_authorized_spec D E' C A' ->
    forall P, Seq.potAcc A P ->
    forall P', Seq.potAcc A' P' ->
    forall M, mutable_spec P E M ->
    forall M', mutable_spec P' E' M' ->
    RefSet.eq (RefSet.diff M' E') (RefSet.diff M E).
  Proof.
    intros D objs Hobjs N HN E Hnonempty Hdisj HE E' HE' Hfilt 
      C T HT HsubT A Hauth A' Hauth' P HP P' HP' M HM M' HM'.
    rewrite ag_fully_authorized_subset_mutable_eq with (M':=M'). 

    2: eauto 1.
    2: eauto 1.
    2: eauto 1.
    2: eauto 1.
    2: eauto 1.
    2: eauto 1.
    2: eauto 1.
    2: eauto 1.
    2: eauto 1.
    2: eauto 1.
    2: apply Seq.ag_objs_spec_ag_objs.
    3: eauto 1.
    3: eauto 1.
    3: eauto 1.
    3: eauto 1.
    3: eauto 1.

    2: rewrite ag_objs_ag_fully_authorized.
    3: eauto 1.
    3: eauto 1.
    3: eapply ag_remainder_spec_iff.
    3: eapply Seq.ag_objs_spec_ag_objs.
    3: eauto 1.
    3: eapply Seq.ag_objs_spec_ag_objs.

    2: intros n; RefSetFacts.set_iff; intros Hn;
    destruct Hn as [Hn | [Hn | Hn]]; try solve [eauto 2];
    eapply HN; eapply Hobjs;
    eapply Seq.ag_objs_spec_ag_objs in Hn; destruct Hn as [obj [rgt [HinD | HinD]]];
    eapply ag_remainder_spec_iff in HinD; destruct HinD as [HinD _];
    do 2 eapply ex_intro; eauto 2.

    intros a.
    RefSetFacts.set_iff.
    split; intros H; [intuition|].
    destruct H as [HinM HninE].
    case (RefSetProps.In_dec a E'); intros HinE'; [| intuition].
    eapply filtered_subset_eq_iff_filtered_subset_eq' in Hfilt.
    edestruct (Hfilt a) as [H | H]; [|destruct H as [HinN Heq]; eapply Heq in HinE'; contradiction].
    (* a must be in N,
       M is a subset of (union E (ag_objs P))
       ~ In a E, so this reduces to In a (ag_objs P)
       By potAcc_objs , we can reduce to In a (ag_objs A)
       We know the objs of A, which are the objs of the remainder, E, and T.
       T is a subset of N, E is a subset of N, and objs is a subset of N.
       the remainder objs are a subset of objs, so we are good.
       *)

    contradict H.

    eapply mutable_subset_objs in HinM;
      [ | eapply ag_objs_spec_potTransfer; [eapply Seq.ag_objs_spec_ag_objs| apply HP] | eapply HM].


    rewrite ag_objs_ag_fully_authorized with (Aobjs:=(Seq.ag_objs A)) in HinM; 
      try solve [eauto 1 | eapply ag_remainder_spec_iff].

    revert HinM; RefSetFacts.set_iff.
    intros [H | [H | H]]; try solve [intuition].
    idtac.
    eapply ag_objs_ag_remainder_subset in H; try solve [eauto 1 | apply ag_remainder_spec_iff].
    revert H; RefSetFacts.set_iff; intros [H H']; auto.
Qed.



(*

   For reference, here are the current signatures:

      Theorem mutable_ag_fully_authorized_singleton:
        forall D objs, Seq.ag_objs_spec D objs ->
        forall C T, capset_targets C T ->
        forall e, ~ RefSet.In e objs -> ~ RefSet.In e T ->
        forall e', ~ RefSet.In e' objs -> ~ RefSet.In e' T ->
        forall A, ag_fully_authorized_spec D (RefSet.singleton e) C A ->
        forall A', ag_fully_authorized_spec D (RefSet.singleton e') C A' ->
        forall P, Seq.potAcc A P ->
        forall P', Seq.potAcc A' P' ->
        forall M, mutable_spec P (RefSet.singleton e) M ->
        forall M', mutable_spec P' (RefSet.singleton e') M' ->
          RefSet.eq (RefSet.diff M (RefSet.singleton e)) (RefSet.diff M' (RefSet.singleton e')).

  Theorem ag_fully_authorized_mutable_subset_eq_diff :
    forall D objs, Seq.ag_objs_spec D objs ->
    forall N, RefSet.Subset objs N ->
    forall E, ~ RefSet.Empty E ->
      RefSet.Empty (RefSet.inter E objs) ->
      RefSet.Subset E N ->
    forall E', RefSet.Subset E E' ->
      filtered_subset_eq E E' N ->
    forall C T, capset_targets C T -> 
      RefSet.Subset T N ->
    forall A, ag_fully_authorized_spec D E C A ->
    forall A', ag_fully_authorized_spec D E' C A' ->
    forall P, Seq.potAcc A P ->
    forall P', Seq.potAcc A' P' ->
    forall M, mutable_spec P E M ->
    forall M', mutable_spec P' E' M' ->
    RefSet.eq (RefSet.diff M' E') (RefSet.diff M E).

We know that:
  exists e, In e E /\ exists e', In e' E'.
By disjoint intersection,
  ~ In e objs /\ ~ In e' objs /\ ~ In e T /\ ~ In e' T.
We can instantiate mutable_ag_fully_auhorized_singleton.
  (mutable (potAcc (ag_fully_authorized D {e} C)) {e}) - {e}
    [=]
  (mutable (potAcc (ag_fully_authorized D {e'} C))) {e'}) - {e'}

Because {e} [<=] E, we can instantiate ag_fully_authorizeed_mutable_subst_eq_diff.
Please note that choosing the correct N is essential.
Choose N := (N - E + {e})
Such an N is always a superset of T, as we have assumed it E and E' are disjoint from T,
so there is no need to worry about the ~ In e T /\ ~ In e' T assumptions in earlier theorems.
This satisfies the appropriate properties and is disjoint and filtered in the correct ways.

  (mutable (potAcc (ag_fully_authorized D E C)) E) - E
    [=] 
  (mutable (potAcc (ag_fully_authorized D {e} C)) {e}) - {e}

Run this again for {e'} [<=] E':

  (mutable (potAcc (ag_fully_authorized D E C)) E') - E'
    [=] 
  (mutable (potAcc (ag_fully_authorized D {e'} C)) {e'}) - {e'}

By transitivity:

  (mutable (potAcc (ag_fully_authorized D E C)) E') - E'
    [=] 
  (mutable (potAcc (ag_fully_authorized D {e'} C)) {e'}) - {e'}
    [=]
  (mutable (potAcc (ag_fully_authorized D {e} C)) {e}) - {e}
    [=] 
  (mutable (potAcc (ag_fully_authorized D E C)) E) - E

Which yields our main result!

*)

  Theorem ag_fully_authorized_mutable_eq_diff :
    forall D objs, Seq.ag_objs_spec D objs ->
    forall N, RefSet.Subset objs N ->
    forall E, ~ RefSet.Empty E ->
      RefSet.Empty (RefSet.inter E objs) ->
    forall E', ~ RefSet.Empty E' ->
      RefSet.Empty (RefSet.inter E' objs) ->
      filtered_subset_eq E E' N ->
    forall C T, capset_targets C T -> 
      RefSet.Subset T N ->
      RefSet.Empty (RefSet.inter E T) ->
      RefSet.Empty (RefSet.inter E' T) ->
    forall A, ag_fully_authorized_spec D E C A ->
    forall A', ag_fully_authorized_spec D E' C A' ->
    forall P, Seq.potAcc A P ->
    forall P', Seq.potAcc A' P' ->
    forall M, mutable_spec P E M ->
    forall M', mutable_spec P' E' M' ->
    RefSet.eq (RefSet.diff M' E') (RefSet.diff M E).
  Proof.
    intros D objs Hobjs N HN E HE HdisjE E' HE' HdisjE' Hfilt C T HT HsubT HdisjE2 HdisjE2' A Hauth A' Hauth'
      P HP P' HP' M HM M' HM'.

    generalize HE HE'; intros HE2 HE'2;
      eapply RefSetAddEq_nonempty_exists in HE2;
        eapply RefSetAddEq_nonempty_exists in HE'2;
          destruct HE2 as [e HeinE]; destruct HE'2 as [e' He'inE].

    eapply RefSet.eq_trans.
    eapply ag_fully_authorized_mutable_subset_eq_diff with 
      (N := (RefSet.add e' (RefSet.diff N E'))) (E:= (RefSet.singleton e')).
    15: apply HM'.
    13: apply HP'.
    11: apply Hauth'.
    8: apply HT.
    11: apply mutable_spec_mutable.
    10: apply Seq.potAcc_potAcc_fun.
    9: apply ag_fully_authorized_spec_iff.
    3: intros Hnot; eapply Hnot; apply RefSetFacts.singleton_iff; apply Ref.eq_refl.
    apply Hobjs.
    intros n HinNodes; RefSetFacts.set_iff;
      right; split; [eapply HN; auto | intros Hnot; eapply HdisjE'; RefSetFacts.set_iff; eauto 2].
    intros n; RefSetFacts.set_iff;
      intros [Heq HinN]; rewrite Heq in He'inE; eapply HdisjE'; RefSetFacts.set_iff; eauto 2. 
    intros n Hin; apply RefSetFacts.singleton_iff in Hin; rewrite <- Hin;
      apply RefSetFacts.add_iff; auto.
    intros n Hin; apply RefSetFacts.singleton_iff in Hin; rewrite <- Hin; auto.

    2: intros n Hin; generalize (HsubT n) (HdisjE2 n) (HdisjE2' n); RefSetFacts.set_iff;
      do 2 (rewrite Sumbool_not_and; Sumbool_decide; try apply RefSetProps.In_dec); tauto.

    eapply filtered_subset_eq_iff_filtered_subset_eq'.
    eapply filtered_subset_eq_iff_filtered_subset_eq' in Hfilt.
    intros n; RefSetFacts.set_iff.
    case (Ref.eq_dec e' n); intros HcaseEq; [rewrite <- HcaseEq; tauto|].
    generalize (Hfilt n); intros [HninN | [HinN Hiff]];
      (rewrite Sumbool_not_or; Sumbool_decide; try solve [auto | apply RefSetProps.In_dec];
        rewrite Sumbool_not_and; Sumbool_decide; try solve [auto | apply RefSetProps.In_dec]).
    rewrite <- Sumbool_dec_not_not_iff; Sumbool_decide; try solve [auto | apply RefSetProps.In_dec].
    case (RefSetProps.In_dec n E'); intros HcaseE; try tauto.

    (* This concludes one equivdlance *)

    eapply RefSet.eq_sym; eapply RefSet.eq_trans.
    eapply ag_fully_authorized_mutable_subset_eq_diff with 
      (N := (RefSet.add e (RefSet.diff N E))) (E:= (RefSet.singleton e)).

    15: apply HM.
    13: apply HP.
    11: apply Hauth.
    8: apply HT.
    11: apply mutable_spec_mutable.
    10: apply Seq.potAcc_potAcc_fun.
    9: apply ag_fully_authorized_spec_iff.
    3: intros Hnot; eapply Hnot; apply RefSetFacts.singleton_iff; apply Ref.eq_refl.
    apply Hobjs.
    intros n HinNodes; RefSetFacts.set_iff;
      right; split; [eapply HN; auto | intros Hnot; eapply HdisjE; RefSetFacts.set_iff; eauto 2].
    intros n; RefSetFacts.set_iff;
      intros [Heq HinN]; rewrite Heq in HeinE; eapply HdisjE; RefSetFacts.set_iff; eauto 2. 
    intros n Hin; apply RefSetFacts.singleton_iff in Hin; rewrite <- Hin;
      apply RefSetFacts.add_iff; auto.
    intros n Hin; apply RefSetFacts.singleton_iff in Hin; rewrite <- Hin; auto.

    2: intros n Hin; generalize (HsubT n) (HdisjE2 n) (HdisjE2' n); RefSetFacts.set_iff;
      do 2 (rewrite Sumbool_not_and; Sumbool_decide; try apply RefSetProps.In_dec); tauto.

    eapply filtered_subset_eq_iff_filtered_subset_eq'.
    eapply filtered_subset_eq_iff_filtered_subset_eq' in Hfilt.
    intros n; RefSetFacts.set_iff.
    case (Ref.eq_dec e n); intros HcaseEq; [rewrite <- HcaseEq; tauto|].
    generalize (Hfilt n); intros [HninN | [HinN Hiff]];
      (rewrite Sumbool_not_or; Sumbool_decide; try solve [auto | apply RefSetProps.In_dec];
        rewrite Sumbool_not_and; Sumbool_decide; try solve [auto | apply RefSetProps.In_dec]).
    rewrite <- Sumbool_dec_not_not_iff; Sumbool_decide; try solve [auto | apply RefSetProps.In_dec].
    case (RefSetProps.In_dec n E); intros HcaseE; try tauto.

    (* We are now down to the singleton case *)

    eapply mutable_ag_fully_authorized_singleton.
    apply Hobjs.
    apply HT.
    intros Hnot; eapply HdisjE; RefSetFacts.set_iff; eauto.
    intros Hnot; eapply HdisjE2; RefSetFacts.set_iff; eauto.
    intros Hnot; eapply HdisjE'; RefSetFacts.set_iff; eauto.
    intros Hnot; eapply HdisjE2'; RefSetFacts.set_iff; eauto.
    eapply ag_fully_authorized_spec_iff.
    eapply ag_fully_authorized_spec_iff.
    eapply Seq.potAcc_potAcc_fun.
    eapply Seq.potAcc_potAcc_fun.
    eapply mutable_spec_mutable.
    eapply mutable_spec_mutable.
  Qed.

Theorem Proper_ag_remainder_spec_impl: Proper (AG.eq ==> RefSet.eq ==> AG.eq ==> impl) ag_remainder_spec.
Proof.
  unfold Proper; unfold respectful; unfold impl; unfold ag_remainder_spec; intros.
  eapply iff_trans.
  eapply iff_sym; eapply H1; clear H1.
  eapply iff_trans; [eapply H2|clear H2].
  rewrite (H edge); clear H.
  split; intros [Hedge Hexclude]; (split ; [apply Hedge|eapply Proper_excluded_edge; eauto;
    solve [ apply H0 |apply RefSet.eq_sym; apply H0]]).
Qed.


Theorem Proper_ag_remainder_spec_iff: Proper (AG.eq ==> RefSet.eq ==> AG.eq ==> iff) ag_remainder_spec.
Proof.
  split; eapply Proper_ag_remainder_spec_impl; eauto;
  solve [apply AG.eq_sym; auto | apply RefSet.eq_sym; auto].
Qed.

      Theorem ag_authorized_remainder_eq_simpl :
        forall D E C A, ag_fully_authorized_spec D E C A ->
          forall D', ag_remainder_spec D E D' ->
            ag_fully_authorized_spec D' E C A.
      Proof.
        intros D E C A Hauth D' Hrem.
        eapply ag_authorized_remainder in Hauth.
        2: apply ag_fully_authorized_spec_iff.
        eapply Proper_ag_fully_authorized_spec.
        4: apply Hauth.
        4: apply ag_fully_authorized_spec_iff.
        2: apply RefSet.eq_refl.
        2: apply CapSet.eq_refl.
        apply AG.eq_sym. eapply ag_remainder_spec_eq in Hrem.
        apply Hrem.
        apply AG.eq_refl.
        apply RefSet.eq_refl.
        apply ag_remainder_spec_iff.
 
      Qed.


      Theorem extant_capabilities_targets:
        forall C S, extant_capabilities C S ->
        forall T, capset_targets C T ->
        forall Ex, obj_existed Ex S ->
          RefSet.Subset T Ex.
        Proof.
          intros C S Hextant T HT Ex HEx x HinT.
          eapply HEx.
          eapply Hextant.
          eapply capset_targets_eq;
            [apply CapSet.eq_refl
              | apply capset_targets_iff_f
              | apply HT
              | apply HinT].
        Qed.

  (* 
     This isn't quite right.  ag_fully_authorized adds all caps of C to A', but we've lost the ability to know
     if they are invalid.  This doesn't invalidate the result, because the confinement is still an upper bound.
     We should restrict the confinement question to be only those capabilities that are currently valid.
     The problem with this restriction is that the test will not pass as those invalid caps are not approved.
     We can't form an equivalence of confinement, and we can't form an equivalence of fully authorized ag.
     We need to redefine one of these.
     We need to modify the confinement test to ignore the other forms of non-mutating capabilities, namely
     those referenceing objects that are not alive.
     
     *)
  Theorem confined_subsystem_mutability_subset_any_fully_authroized_mutability:
    forall E, ~ RefSet.Empty E ->
    forall C S, authorized_confined_subsystem C E S ->
    forall D, dirAcc_spec S D ->
    forall Ex, obj_existed Ex S ->
    forall E', ~ RefSet.Empty E' ->
    novel_capabilities C E' ->
    RefSet.Empty (RefSet.inter E' (RefSet.diff Ex E)) ->
    forall R, ag_remainder_spec D E R ->
    forall A', ag_fully_authorized_spec R E' C A' ->
    forall P, Seq.potAcc D P ->
    forall P', Seq.potAcc A' P' ->
    forall M, mutable_spec P E M ->
    forall M', mutable_spec P' E' M' ->
    RefSet.Subset (RefSet.diff M E) (RefSet.diff M' E').
    Proof.
      intros E Hnonempty C S [Hnovel [Hextant Hconf]] D Hda Ex HEx E' Hnonempty' Hnovel'
        Hfilter R Hrem A' Hauth' P Hpa P' Hpa' M Hmut M' Hmut'.

      generalize (ag_fully_authorized_spec_iff D E C); generalize (ag_fully_authorized D E C); intros A2 Hauth2.
      generalize (Seq.potAcc_potAcc_fun A2); generalize (Seq.potAcc_fun A2); intros P2 Hpa2.
      generalize (mutable_spec_mutable P2 E); generalize (mutable P2 E); intros M2 Hmut2.

      generalize (confined_subsystem_mutable _ _ _ Hconf _ Hda _ Hauth2 _ Hpa _ Hpa2 _ Hmut _ Hmut2 );
        intros HmutSub.

      assert (RefSet.Subset (RefSet.diff M E) (RefSet.diff M2 E)) as Hsubdiff by
      (intros x; RefSetFacts.set_iff; intros [HinM HninE]; eapply HmutSub in HinM; auto).

      eapply RefSetProps.subset_trans; [apply Hsubdiff|].

      (* At this point, we have eliminated the confinement test.  
         We're now down to discharging hypotheses of ag_fully_authorized_mutable_eq_diff 
         Take a moment to clean up the variables here *)
      clear M P Hsubdiff HmutSub Hmut Hpa Hconf.
      rename P2 into P; rename A2 into A; rename M2 into M.
      rename Hauth2 into Hauth; rename Hpa2 into Hpa; rename Hmut2 into Hmut.

      eapply ag_authorized_remainder_eq_simpl in Hauth; [|eauto 1].

      eapply RefSetProps.subset_equal.

      generalize (Seq.ag_objs_spec_ag_objs R); generalize (Seq.ag_objs R); intros Robjs HRobjs.
      generalize (capset_targets_iff_f C); generalize (capset_targets_f C); intros T HT.
      generalize (Seq.ag_objs_spec_ag_objs D); generalize (Seq.ag_objs D); intros Dobjs HDobjs.

      eapply novel_capabilities_inter_empty in Hnovel; [|apply HT].
      eapply novel_capabilities_inter_empty in Hnovel'; [|apply HT].

      generalize (ag_remainder_empty_inter _ _ _ Hrem _ HRobjs); intros HemptyRem.

      eapply ag_fully_authorized_mutable_eq_diff with (N:= (RefSet.diff Ex E)).
      apply HRobjs.
      2: auto.
      3: auto.
      5: apply HT.
      6: apply Hnovel'.
      6: apply Hnovel.
      6: apply Hauth'.
      6: apply Hauth.
      6: apply Hpa'.
      6: apply Hpa.
      6: apply Hmut'.
      6: apply Hmut.

      eapply RefSetProps.subset_trans;
        [ eapply ag_objs_ag_remainder_subset; [apply HDobjs | apply Hrem | apply HRobjs]
          | intros x; RefSetFacts.set_iff; intros [HinDobjs HninE]; split; [|auto];
            eapply ag_objs_spec_subset_existed; eauto 1].
      2: apply HemptyRem.

      3: intros x HinT; RefSetFacts.set_iff.
      3: split;
        [eapply extant_capabilities_targets; eauto 1
          | intros Hnot; eapply Hnovel; RefSetFacts.set_iff; split; eauto 1].

      2: eapply filtered_subset_eq_iff_filtered_subset_eq'; intros x;
        case (RefSetProps.In_dec x (RefSet.diff Ex E)); intros Hcase; 
          [right; split; 
            [ auto
              | generalize (Hfilter x); revert Hcase; RefSetFacts.set_iff; tauto]
            | left; auto] .

      intros x; RefSetFacts.set_iff; intros [HinE HinRobjs].
      eapply ag_objs_ag_remainder_subset in HinRobjs;
        [ | apply HDobjs | apply Hrem | apply HRobjs].
      revert HinRobjs; RefSetFacts.set_iff; intros [HinDobjs HninE].
      eapply Hfilter. RefSetFacts.set_iff.
      eapply ag_objs_spec_subset_existed in HEx;
        [ |apply Hda | apply HDobjs].
      eapply HEx in HinDobjs.
      eauto.
    Qed.
    
  (* TODO: We need to know we can instantiate all of the inputs.
     In particular, we need to know that AG.Subset (ag_objs A) (union (ag_objs D) (union E (cap_targets C))). 
     Subset (cap_targets C) (ag_objs D) /\ (Subset (ag_objs D) N) /\ (Subset E N) -> (Subset (ag_objs A) N)
     If a subsystem is confined, the first condition is true and we have already assumed the others
     This allows us to ignore the constraint that Subset (ag_objs A) N 
     This pattern matches our other assumptions about mutation.
     We can instantiate with the obj_existed Ex S to produce the other constraints.
     *)


End MakeConfinement.