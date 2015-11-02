(* type_remove *)
(*Require Import DirectAccess.*)
Require Import Semantics_Conv.
Require CapIndexListFacts.
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
Require Import RelationClasses.
Require FoldOrder.
Require Import Morphisms.
Require Import SetoidList.
Require Import AccessRights.
Require Import AccessRightSets.
Require Import ObjectLabels.
Require Import ObjectSchedules.
Require Import ObjectTypes.
Require Import SequentialAccess.
Require Import References.
Require Import Capabilities.
Require Import Indices.
Require Import Objects.
Require Import SystemState.
Require Import SemanticsDefinitions.
Require Import Semantics.
Require Import Semantics_ConvImpl.
Require Import SystemState_ConvImpl.
Require Import Sumbool.
Require Import RefSets.
(*
Require Import Semantics.
*)
Require Import AccessEdge.
Require Import AccessGraphs.

Module MakeDirectAccess (Ref:ReferenceType) (RefS: RefSetType Ref) (Edges: AccessEdgeType Ref) (AccessGraph:AccessGraphType Ref Edges) (Seq:SeqAccType Ref RefS Edges AccessGraph) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) (SemDefns: SemanticsDefinitionsType Ref Cap Ind Obj Sys) (Sem: SemanticsType Ref RefS Cap Ind Obj Sys SemDefns)  (*: DirectAccessType Ref Cap Ind Obj Sys SemDefns Sem Edges AccessGraph Seq*).
  Module SemConv := MakeSemanticsConv Ref RefS Cap Ind Obj Sys SemDefns Sem.
(*  Module Seq := SeqAcc Ref. *)
  (*Module AccessGraph := Seq.AccessGraph.*)
  Import AccessGraph.
  Export AccessGraph.
(*  Import Seq.RefSet_Mod. *)
  Import RefS.
(*  Module Edges := AccessGraph.Edges.
  Module Edge := AccessGraph.Edge. *)
  Module SC := SemDefns.SC.
  Module OC := SC.OC.
  Module CC := SC.CC.
  Module CIL_Facts := SC.CIL_Facts. 

(* see if you can import these from previous modules *)

  Module Obj_MapEquiv := OC.Obj_MapEquiv.
  Module Obj_Facts := OC.Obj_Facts.
  Module Obj_Props := OC.Obj_Props.
  Module Obj_Exists := OC.Obj_Exists.

  Module Sys_MapEquiv := SC.Sys_MapEquiv.
  Module Sys_Equiv := SC.Sys_Equiv.
  Module Sys_Facts := SC.Sys_Facts.
  Module Sys_Props := SC.Sys_Props.
  Module Sys_OrdAdd := SC.Sys_OrdAdd.

(*  Module AGProps := AccessGraph.AGProps.
  Module AGFacts := AccessGraph.AGFacts.
  Module AGAddEq := AccessGraph.AGAddEq. *)
(*  Module AGEquiv := OrderedTypeEquiv.OT_Equiv AG. *)


  (* I hope this has enough equivalences built in *)

  Ltac destruct_dirAcc Hda s' HeqS src_ref src lbl srcType srcSched HmapS 
    src' lbl' srcType' srcSched' HeqP Halive ind cap HmapSrc'
    cap_obj cap_lbl cap_type cap_sched HmapScap cap_obj' cap_lbl' cap_type' cap_sched'
    HeqPcap HaliveCap rgt HdaR HeqEdge :=
    destruct Hda as [s' Hda]; destruct Hda as [HeqS Hda];
      destruct Hda as [src_ref Hda]; destruct Hda as [src Hda];
        destruct Hda as [lbl Hda]; destruct Hda as [srcType Hda];
          destruct Hda as [srcSched Hda]; destruct Hda as [HmapS Hda];
            destruct Hda as [src' Hda]; destruct Hda as [lbl' Hda];
              destruct Hda as [srcType' Hda];  destruct Hda as [srcSched' Hda];
                destruct Hda as [HeqP Hda]; destruct Hda as [Halive Hda];
                  destruct Hda as [ind Hda]; destruct Hda as [cap Hda];
                    destruct Hda as [HmapSrc' Hda]; destruct Hda as [cap_obj Hda];
                      destruct Hda as [cap_lbl Hda]; destruct Hda as [cap_type Hda];
                        destruct Hda as [cap_sched Hda]; destruct Hda as [HmapScap Hda];
                          destruct Hda as [cap_obj' Hda]; destruct Hda as [cap_lbl' Hda];
                            destruct Hda as [cap_type' Hda]; destruct Hda as [cap_sched' Hda];
                              destruct Hda as [HeqPcap Hda]; destruct Hda as [HaliveCap Hda];
                                destruct Hda as [rgt Hda]; destruct Hda as [HdaR HeqEdge].

  Ltac apply_ex_intro_dirAcc s' s src_ref src lbl srcType srcSched
    src' lbl' srcType' srcSched' ind cap cap_obj cap_lbl cap_type cap_sched
    cap_obj' cap_lbl' cap_type' cap_sched' rgt := 
    apply ex_intro with s'; split;
      [apply Sys.eq_trans with s; auto; apply Sys.eq_sym; auto |
        apply ex_intro with src_ref; apply ex_intro with src; apply ex_intro with lbl; 
          apply ex_intro with srcType; apply ex_intro with srcSched; split;
            [ | apply ex_intro with src'; apply ex_intro with lbl'; 
              apply ex_intro with srcType'; apply ex_intro with srcSched'; split;
                [ | split;
                  [ | apply ex_intro with ind; apply ex_intro with cap; split;
                    [ | apply ex_intro with cap_obj; apply ex_intro with cap_lbl;
                      apply ex_intro with cap_type; apply ex_intro with cap_sched; split;
                        [ | apply ex_intro with cap_obj'; apply ex_intro with cap_lbl';
                          apply ex_intro with cap_type'; apply ex_intro with cap_sched'; split; 
                            [ | split;
                              [ | apply ex_intro with rgt; split; auto]]]]]]]]; auto.

  Ltac destruct_tuple tuple obj lbl obj_type sched :=
    destruct tuple as [tuple sched]; destruct tuple as [tuple obj_type];
      destruct tuple as [obj lbl].

  Ltac unfold_preReq Hpre Halive HtargetAlive HisActive :=       
    unfold SemDefns.preReq in Hpre; destruct Hpre as [Halive HtargetAlive];
      destruct Halive as [Halive HisActive];
        unfold SemDefns.target_is_alive in Halive; unfold SC.is_alive in Halive;
          unfold SC.is_label in Halive; red in Halive.


(* Section defining dirAcc_spec *)


  Definition dirAcc_spec s ag : Prop := forall edge,
    (exists s', Sys.eq s s' /\
      exists src_ref, exists src, exists lbl, exists srcType, exists srcSched,
        Sys.MapS.MapsTo src_ref (src, lbl, srcType, srcSched) s' /\
        exists  src', exists lbl', exists srcType', exists srcSched',
          Sys.P.eq (src, lbl, srcType, srcSched) (src', lbl', srcType', srcSched') /\ 
          ObjectLabel.eq ObjectLabels.alive lbl' /\
          exists ind, exists cap, 
            Obj.MapS.MapsTo ind cap src' /\ 
            exists cap_obj, exists cap_lbl, exists cap_type, exists cap_sched,
              Sys.MapS.MapsTo (Cap.target cap) (cap_obj, cap_lbl, cap_type, cap_sched) s' /\
              exists cap_obj', exists cap_lbl', exists cap_type', exists cap_sched',
                Sys.P.eq (cap_obj, cap_lbl, cap_type, cap_sched) (cap_obj', cap_lbl', cap_type', cap_sched') /\ 
                ObjectLabel.eq ObjectLabels.alive cap_lbl' /\
                exists rgt,
                  ARSet.In rgt (Cap.rights cap) /\
                  Edge.eq (Edges.mkEdge src_ref (Cap.target cap) rgt) edge) <->
    AG.In edge ag.



  Theorem dirAcc_spec_eq_1 : forall s s' ag ag' edge,
    Sys.eq s s' -> 
    dirAcc_spec s ag ->
    dirAcc_spec s' ag' ->
    AG.In edge ag ->
    AG.In edge ag'.
  Proof.
  (* begin case 1 *)
    intros s s' ag ag' edge H H0 H1 Hin.
    unfold dirAcc_spec in *.
    generalize (H0 edge); clear H0; intros H0.
    generalize (H1 edge); clear H1; intros H1.
    destruct H0 as [H0_1 H0_2].
    destruct H1 as [H1_1 H1_2].
    apply H0_2 in Hin.

    destruct_dirAcc Hin s'' HeqS src_ref src lbl srcType srcSched HmapS 
    src' lbl' srcType' srcSched' HeqP Halive ind cap HmapSrc'
    cap_obj cap_lbl cap_type cap_sched HmapScap cap_obj' cap_lbl' cap_type' cap_sched' 
    HeqPcap HaliveCap rgt HinR HeqEdge.

    apply H1_1.

    apply_ex_intro_dirAcc s'' s src_ref src lbl srcType srcSched src' lbl' srcType' srcSched'
    ind cap cap_obj cap_lbl cap_type cap_sched cap_obj' cap_lbl' cap_type' cap_sched' rgt.
  Qed.
  
  Theorem dirAcc_spec_eq : forall s s' ag ag',
    Sys.eq s s' -> 
    dirAcc_spec s ag ->
    dirAcc_spec s' ag' ->
    AG.eq ag ag'.
  Proof.
    intros.
    (* turn AG.eq into AG.Equal *)
    eapply ag_eq_Equal.
    unfold AG.Equal.
    intros edge; split; intros Hin.
    idtac.
    apply dirAcc_spec_eq_1 with s s' ag; auto.
    apply dirAcc_spec_eq_1 with s' s ag'; auto; apply Sys.eq_sym; auto.
  Qed.

  Theorem dirAcc_simpl : forall s ag,
    dirAcc_spec s ag ->
    forall src,
    SC.is_alive src s ->
    forall t cap,
    SC.getCap t src s = Some cap ->
    forall tgt,
    Ref.eq tgt (Cap.target cap) ->
    SC.is_alive tgt s ->
    forall rgt,
    CC.hasRight cap rgt ->
    AG.In (Edges.mkEdge src tgt rgt) ag.
  Proof.
    intros.
    eapply H.
    unfold SC.getCap in *.
    unfold SC.getObj in *.
    unfold SC.is_alive in *.
    unfold SC.is_label in *.
    unfold SC.getLabel in *.
    (* find the object at src by cases *)
    case (option_sumbool (SC.getObjTuple src s)); intros Hcase; [|destruct Hcase as [src_tuple Hcase]]; rewrite Hcase in *; simpl in *; try discriminate;
      destruct_tuple src_tuple src_obj src_lbl src_type src_sched; simpl in *.
    (* find the object at (Cap.target cap) by cases *)
    case (option_sumbool (SC.getObjTuple tgt s)); intros Hcase'; [|destruct Hcase' as [target_tuple Hcase']]; rewrite Hcase' in *; simpl in *; try contradiction.
      destruct_tuple target_tuple tgt_obj tgt_lbl tgt_type tgt_sched; simpl in *.
    unfold CC.hasRight in H3.
    (* turn find into MapsTo *)
    apply Sys_Facts.find_mapsto_iff in Hcase'.
    apply Sys_Facts.find_mapsto_iff in Hcase.
    apply Obj_Facts.find_mapsto_iff in H1.

    apply_ex_intro_dirAcc s s src src_obj src_lbl src_type src_sched src_obj src_lbl src_type src_sched
      t cap tgt_obj tgt_lbl tgt_type tgt_sched tgt_obj tgt_lbl tgt_type tgt_sched rgt;
    try apply Sys.eq_refl; try apply Sys.P.eq_refl; try (eapply Edges.edge_equal; auto);
    try (eapply Sys_Facts.MapsTo_iff; [apply Ref.eq_sym; apply H2 | auto]); solve [try apply Ref.eq_sym; try apply ObjectLabel.eq_sym; auto; try apply Ref.eq_refl; try apply AccessRight.eq_refl].
  Qed.


(* This section defines dirAcc as a function *)

   (* be very careful with these, all should have the signature ag_add_cap*: ... -> AG.t -> AG.t,
      so that partially applied forms have type AG.t -> AG.t .  For each operation
      do_* : ... -> Sys.t -> Sys.t, dirAcc_approx (do_* ... ) (ag_add_cap* ...). *)

  (* Adds:
     (mkEdge 
       src 
       (target cap) 
       (rights cap)) multiplying on rights *)
  Definition ag_add_cap src cap ag:=
    ARSet.fold (fun rgt acc => AG.add (Edges.mkEdge src (Cap.target cap) rgt) acc) (Cap.rights cap) ag.

  (* 
       Fc := match weaken with true => Cap.weaken | false => fun c => c end.
     above ag_add_cap_if_exists can be generalized over
       for all cases but allocate:
       Fca := andb (true_bool_of_sumbool (SC.is_alive_dec src s)) 
                   (true_bool_of_sumbool (SC.is_alive_dec (Cap.target cap) 
       for allocate:
        Fca := (true_bool_of_sumbool (SC.is_alive_dec (Cap.target cap) *)
  Definition ag_add_cap_mod src cap (Fc: Cap.t -> Cap.t) ag :=
     ag_add_cap src (Fc cap) ag.

  Definition ag_add_cap_valid src cap s Fc (Fv: Ref.t -> Cap.t -> Sys.t -> bool) ag :=
     if Fv src cap s
       then ag_add_cap_mod src cap Fc ag
       else ag.

  Definition ag_add_cap_valid_allocate (src:Ref.t) cap s := 
    (true_bool_of_sumbool (SC.is_alive_dec (Cap.target cap) s)).


  Definition ag_add_cap_valid_std src cap s := 
    andb (true_bool_of_sumbool (SC.is_alive_dec src s)) (ag_add_cap_valid_allocate src cap s).


  (* if all caps can be found and src and (target cap) are alive, adds:
     (mkEdge 
       src 
       (target (getCap i o s)) 
       (rights (getCap i o s))) multiplying on rights,
       if weaken is set true, then the cap is weakened.*)
  Definition ag_add_cap_by_obj_index src o i s Fc Fv ag:=
    option_map1 (fun cap => ag_add_cap_valid src cap s Fc Fv ag) ag (SC.getCap i o s).
  
  (* if (SC.getCap t src s) can be found, and all other caps can be found, adds:
     (mkEdge 
       src 
       (target (getCap i (Cap.target (SC.getCap t src s)) s)) 
       (rights (getCap i (Cap.target (SC.getCap t src s)) s))) multiplying on rights,
       if weaken is set true, then the cap is weakened.*)
  Definition ag_add_cap_by_indirect_index src t i s Fc Fv ag:=
    option_map1 (fun cap => ag_add_cap_by_obj_index src (Cap.target cap) i s Fc Fv ag) ag (SC.getCap t src s).

  (* for all ixi in ixi_list, if src and (target cap) are alive, adds:
     (mkEdge 
       src
       (target (getCap (fst ixi) o s)) 
       (rights (getCap (fst ixi) o s))) multiplying on rights *)
  Definition ag_add_caps_by_index_pair_list src o (ixi_list: list (Ind.t * Ind.t)) s Fc Fv ag :=
    fold_right (fun ixi ag' => ag_add_cap_by_obj_index src o (fst ixi) s Fc Fv ag') ag ixi_list.

  (* if all caps can be found, if (target (getCap i o s)) and (target (getCap i' o' s)) are alive, adds:
     (mkEdge 
       (target (getCap i o s)) 
       (target (getCap i' o' s)) 
       (rights (getCap i' o' s))) multiplying on rights *)
  Definition ag_push_cap_by_indices o i o' i' s Fc Fv ag:=
    option_map1 (fun src => ag_add_cap_by_obj_index src o' i' s Fc Fv ag) ag
    (SemDefns.option_target (SC.getCap i o s)).


  Definition ag_add_caps_reply a t s ag:=
    option_map1 (fun cap => ag_add_cap_valid (Cap.target cap) (Cap.mkCap a (ARSet.singleton tx)) s (fun c => c) ag_add_cap_valid_std ag)
    ag (SC.getCap t a s).


  Definition ag_add_caps_send a t ixi_list s ag:=
    let ag' :=  ag_add_caps_reply a t s ag in
      option_map1 (fun cap => ag_add_caps_by_index_pair_list (Cap.target cap) a ixi_list s (fun c=>c) ag_add_cap_valid_std ag') ag' (SC.getCap t a s).
   
  Definition ag_add_caps_allocate a n ixi_list s ag :=
    (ag_add_cap a (Cap.mkCap n all_rights) (ag_add_caps_by_index_pair_list n a ixi_list s (fun c=>c) ag_add_cap_valid_allocate ag)).

  Definition dirAcc_inner src_ref src_obj s ag := 
    Obj.MapS.fold (fun index cap acc_ag => ag_add_cap_valid src_ref cap s (fun c=>c) ag_add_cap_valid_std acc_ag) src_obj ag.

  Definition dirAcc_outer s ag := 
    Sys.MapS.fold (fun src_ref src_tuple acc_ag => dirAcc_inner src_ref (SC.tupleGetObj src_tuple) s acc_ag) s ag.

  Definition dirAcc s := dirAcc_outer s AG.empty.


(* Section relating dirAcc_spec and dirAcc *)

 Ltac destruct_inner H1 H2 H3 H4 H5:= destruct H1 as [H1 H2]; destruct H2 as [ind H2]; destruct H2 as [cap H2]; 
   destruct H2 as [H2 H3]; destruct H3 as [H3 H4]; destruct H4 as [rgt H4]; destruct H4 as [H4 H5].

 Ltac destruct_outer H1 H2 H3 H4 H5 H6 := destruct H1 as [src_ref H1]; destruct H1 as [H1 H2];
   destruct H2 as [src_obj H2]; destruct H2 as [H2 H3]; destruct H3 as [ind H3];
     destruct H3 as [cap H3]; destruct H3 as [H3 H4]; destruct H4 as [H4 H5]; destruct H5 as [rgt H5];
       destruct H5 as [H5 H6].

    Ltac destructEdgeEq := fun HeqEdge edge HeqEdgeS HeqEdgeT HeqEdgeR=>
      rewrite <- (Edges.edge_rewrite edge) in HeqEdge;
        generalize (Edges.eq_source _ _ HeqEdge); intros HeqEdgeS; repeat progress rewrite Edges.source_rewrite in HeqEdgeS;
          generalize (Edges.eq_target _ _ HeqEdge); intros HeqEdgeT; repeat progress rewrite Edges.target_rewrite in HeqEdgeT;
            generalize (Edges.eq_right _ _ HeqEdge); intros HeqEdgeR; repeat progress rewrite Edges.right_rewrite in HeqEdgeR;
              rewrite (Edges.edge_rewrite edge) in HeqEdge.


  Theorem ag_add_cap_nondecr : forall src cap ag ag',
    AG.Subset ag ag' -> AG.Subset ag (ag_add_cap src cap ag').
  Proof.
    intros.
    unfold ag_add_cap.
    eapply ARSetProps.fold_rec_nodep with (P:=fun AG, AG.Subset ag AG); 
      intros; [| eapply AGProps.subset_add_2]; auto.
  Qed.

  Hint Resolve ag_add_cap_nondecr.


(* we need subset properties over all of these functions, rather than equivalence *)




  Theorem ag_add_cap_subset: forall src src' cap cap' ag ag',
   Ref.eq src src' -> Cap.eq cap cap' -> AG.Subset ag ag' -> 
   AG.Subset (ag_add_cap src cap ag) (ag_add_cap src' cap' ag').
  Proof.
    intros.
    unfold ag_add_cap.
    eapply ARSetFoldOrder.fold_foldPartialOrder with (leA := AG.Subset); eauto;
      try eapply Cap.rights_eq; eauto.
    (* PartialOrder  *)
    eapply AG_PO.
    (* foldPartialOrder f f' *)
    split; [|split;[|split]].
    eapply Proper_add_mkedge.
    eapply Proper_add_mkedge.
   (* transpose *)
    unfold SetoidList.transpose; intros; eapply AGProps.add_add.
   (* subset_leA_comm *)
   unfold ARSetFoldOrder.subset_leA_comm .
   intros.
   intros x Hin.
eapply AGFacts.add_iff in Hin; 
        eapply AGFacts.add_iff.
    simpl in *.
   generalize (Cap.target_eq _ _ H0); intros.
   unfold Ref.eq in *.
   intuition. left. rewrite <- H4; rewrite <- H; rewrite <- H3. auto.
  Qed.

  Hint Resolve ag_add_cap_subset.

  (* TODO: where should foldEqual_ag_add and transpose_ag_add live? *)

    Theorem foldEqual_ag_add: forall src src' tgt tgt',
      Ref.eq src src' -> Ref.eq tgt tgt' ->
      ARSetFold.foldEqual AG.eq
       (fun rgt acc => AG.add (Edges.mkEdge src tgt rgt) acc)
       (fun rgt acc => AG.add (Edges.mkEdge src' tgt' rgt) acc).
    Proof.
    unfold ARSetFold.foldEqual; intros.
    eapply ag_eq_Equal.
    eapply AGAddEq.Eq_Add_complete; [| eapply H1| eapply AGProps.Add_add| eapply AGProps.Add_add].
    rewrite H2; rewrite H; rewrite H0; auto.
    Qed.

    Theorem transpose_ag_add: forall src tgt,
      SetoidList.transpose AG.eq (fun rgt acc => AG.add (Edges.mkEdge src tgt rgt) acc).
    Proof.
    unfold SetoidList.transpose. intros.
    eapply ag_eq_Equal.
    generalize (Edges.mkEdge src tgt x); intros X.
    generalize (Edges.mkEdge src tgt y); intros Y.
    eapply AGProps.add_add.
    Qed.


  Theorem ag_add_cap_equiv: forall src src' cap cap' ag ag',
   Ref.eq src src' -> Cap.eq cap cap' -> AG.eq ag ag' -> AG.eq (ag_add_cap src cap ag) (ag_add_cap src' cap' ag').
  Proof.
    intros.
    unfold ag_add_cap.
    eapply ARSetFold.fold_foldEqual with (eqA := AG.eq); eauto.
    (* Equal rights *)
    apply Cap.rights_eq; auto.
    (* foldequal add *)
    eapply foldEqual_ag_add; try eapply Cap.target_eq; eauto.
    (* transpose add *)
    eapply transpose_ag_add.
  Qed.

  Hint Resolve ag_add_cap_equiv.

  Theorem ag_add_cap_add_commute: forall src cap, Seq.ag_add_commute (ag_add_cap src cap).
  Proof.
    intros; red. intros ag ag' x.
    unfold ag_add_cap.
    generalize (Cap.target cap); generalize (Cap.rights cap); clear cap; intros rgts tgt.
    eapply ARSetProps.fold_rec_bis with 
      (P:= (fun rgts (a:AG.t) =>
        AGProps.Add x ag ag' ->
          AGProps.Add x a
           (ARSet.fold (fun (rgt : ARSet.elt) (acc : AG.t) =>
             AG.add (Edges.mkEdge src tgt rgt) acc) rgts ag'))).
    (* outer compat *)
    intros rgts2 rgts2' ag2 Heq Hcompat Hadd. eapply Hcompat in Hadd; clear Hcompat; rename Hadd into Hcompat.
    intros edge; generalize (Hcompat edge); clear Hcompat; intros Hcompat.
    eapply iff_trans; [| eapply Hcompat]; clear Hcompat.
    revert edge.
    eapply ARSetFold.fold_foldEqual with (eqA := AG.Equal).
    (* 5 cases, 1 per line. *)
    eapply AG_EQ.
    eapply ARSet.eq_sym; auto.
    apply AG.eq_refl.
    eapply foldEqual_ag_add; try apply Ref.eq_refl.
    eapply transpose_ag_add.
    (* outer base *)
    eapply ARSetProps.fold_rec_bis with 
      (P:= (fun rgts (a:AG.t) =>
        AGProps.Add x ag ag' ->
          AGProps.Add x ag a)); intros; eauto.
    (* inner base, by eauto *)
    (* inner step *)
    eapply ARSet.empty_1 in H; contradiction.
    (* outer step *)
    intros rgt ag_acc rgts2; intros.
    eapply H1 in H2; clear H1.
    (* begin by reducing the fold from the goal to the fold in H2 *)
    eapply AGAddEq.Add_eq.
    eapply AG.eq_sym.
    eapply ARSetProps.fold_add with (eqA:=AG.eq); auto. 
    (* compat_op eq AG.eq add *)
    unfold SetoidList.compat_op;
    unfold Proper; unfold respectful; intros.
    eapply AGAddEq.Eq_Add_complete; [eapply Edges.edge_equal; try apply Ref.eq_refl; eauto | apply H3 | apply AGProps.Add_add| try apply Ref.eq_refl; auto].
    (* transpose AG.eq add *)
    unfold SetoidList.transpose; intros; eapply AGProps.add_add.
    (* the fold in the goal now matches the fold in H2 *)
    eapply Seq.add_add_commute.
    auto.
  Qed.

  Hint Resolve ag_add_cap_add_commute.

  Theorem ag_add_cap_mod_nondecr : forall src cap ag ag' Fc,
    AG.Subset ag ag' -> AG.Subset ag (ag_add_cap_mod src cap Fc ag').
  Proof.
    intros.
    unfold ag_add_cap_mod.
    auto.
  Qed.

  Hint Resolve ag_add_cap_mod_nondecr.

  Definition Fn_cap_equiv Fc Fc' := forall c c', Cap.eq c c' -> Cap.eq (Fc c) (Fc' c').

  Theorem Fn_cap_equiv_id: Fn_cap_equiv (fun c => c) (fun c => c).
  Proof.
    unfold Fn_cap_equiv; intuition.
  Qed.
  Hint Resolve Fn_cap_equiv_id.

  Theorem Fn_cap_equiv_weaken: Fn_cap_equiv Cap.weaken Cap.weaken.
  Proof.
    red; intros; apply CC.weaken_equiv; auto.
  Qed.
  Hint Resolve Fn_cap_equiv_weaken.

  Theorem ag_add_cap_mod_subset: forall src src' cap cap' Fc Fc' ag ag',
   Ref.eq src src' -> Cap.eq cap cap' -> AG.Subset ag ag' ->
   forall (Fc_eq: Fn_cap_equiv Fc Fc'),
   AG.Subset (ag_add_cap_mod src cap Fc ag) (ag_add_cap_mod src' cap' Fc' ag').
  Proof.
   intros.
   unfold ag_add_cap_mod.
   intuition eauto.
  Qed.

  Hint Resolve ag_add_cap_mod_subset.

  Theorem ag_add_cap_mod_equiv: forall src src' cap cap' Fc Fc' ag ag',
   Ref.eq src src' -> Cap.eq cap cap' -> AG.eq ag ag' ->
   forall (Fc_eq: Fn_cap_equiv Fc Fc'),
   AG.eq (ag_add_cap_mod src cap Fc ag) (ag_add_cap_mod src' cap' Fc' ag').
  Proof.
   intros.
   unfold ag_add_cap_mod.
   intuition eauto.
  Qed.

  Hint Resolve ag_add_cap_mod_equiv.

  Theorem ag_add_cap_mod_add_commute: forall src cap Fc, Seq.ag_add_commute (ag_add_cap_mod src cap Fc).
  Proof.
    intros; eapply ag_add_cap_add_commute.
  Qed.

  Hint Resolve ag_add_cap_mod_add_commute.

  Definition Fn_valid_equiv (Fv Fv': Ref.t -> Cap.t -> Sys.t -> bool) := forall r r' c c' s s', 
   Ref.eq r r' -> Cap.eq c c' -> Sys.eq s s' -> (Fv r c s) = (Fv' r' c' s').

  Theorem ag_add_cap_valid_equiv: forall src src' cap cap' s s' Fc Fc' Fv Fv' ag ag',
   Ref.eq src src' -> Cap.eq cap cap' -> AG.eq ag ag' -> Sys.eq s s' ->
   forall (Fc_eq: Fn_cap_equiv Fc Fc') (Fv_eq: Fn_valid_equiv Fv Fv'),
   AG.eq (ag_add_cap_valid src cap s Fc Fv ag) (ag_add_cap_valid src' cap' s' Fc' Fv' ag').
  Proof.
   intros.
   unfold ag_add_cap_valid.
   rewrite <- (Fv_eq src src' cap cap' s s'); eauto.
   case Fv; simpl; eauto.
  Qed.

  Hint Resolve ag_add_cap_valid_equiv.
 
  Theorem ag_add_cap_valid_subset: forall src src' cap cap' s s' Fc Fc' Fv Fv' ag ag',
   Ref.eq src src' -> Cap.eq cap cap' -> AG.Subset ag ag' -> Sys.eq s s' ->
   forall (Fc_eq: Fn_cap_equiv Fc Fc') (Fv_eq: Fn_valid_equiv Fv Fv'),
   AG.Subset (ag_add_cap_valid src cap s Fc Fv ag) (ag_add_cap_valid src' cap' s' Fc' Fv' ag').
  Proof.
   intros.
   unfold ag_add_cap_valid.
   rewrite <- (Fv_eq src src' cap cap' s s'); auto.
   case Fv; simpl; auto.
  Qed.

  Hint Resolve ag_add_cap_valid_subset.

  Theorem ag_add_cap_valid_add_commute: forall src cap s Fc Fv, 
     Seq.ag_add_commute (ag_add_cap_valid src cap s Fc Fv).
  Proof.
    intros; unfold ag_add_cap_valid. 
    destruct (Fv src cap s); [eapply ag_add_cap_mod_add_commute | red; intuition].
  Qed.

  Hint Resolve ag_add_cap_valid_add_commute.

  Theorem ag_add_cap_valid_nondecr : forall src cap s ag ag' Fc Fv,
    AG.Subset ag ag' -> AG.Subset ag (ag_add_cap_valid src cap s Fc Fv ag').
  Proof.
    intros.
    unfold ag_add_cap_valid.
    case Fv; simpl; eauto.
  Qed.

  Hint Resolve ag_add_cap_valid_nondecr.

  Theorem ag_add_cap_by_obj_index_subset: forall src src' o o' i i' s s' Fc Fc' Fv Fv' ag ag',
  Ref.eq src src' -> Ref.eq o o' -> Ind.eq i i' -> Sys.eq s s' -> AG.Subset ag ag' ->
  forall (Fc_eq: Fn_cap_equiv Fc Fc') (Fv_eq: Fn_valid_equiv Fv Fv'),
  AG.Subset (ag_add_cap_by_obj_index src o i s Fc Fv ag) (ag_add_cap_by_obj_index src' o' i' s' Fc' Fv' ag').
  Proof.
    intros.
    unfold ag_add_cap_by_obj_index.
    generalize (SC.getCap_eq _ _ _ _ _ _ H2 H1 H0); intros Heq.
    case (option_sumbool (SC.getCap i o s)); intros Hopt; [|destruct Hopt as [cap Hopt]];
      rewrite Hopt in *; simpl in *;
    (case (option_sumbool (SC.getCap i' o' s')); intros Hopt'; [|destruct Hopt' as [cap' Hopt']];
      rewrite Hopt' in *; simpl in *; try contradiction); auto.
  Qed.

  Hint Resolve ag_add_cap_by_obj_index_subset.

  Theorem ag_add_cap_by_obj_index_equiv: forall src src' o o' i i' s s' Fc Fc' Fv Fv' ag ag',
  Ref.eq src src' -> Ref.eq o o' -> Ind.eq i i' -> Sys.eq s s' -> AG.eq ag ag' ->
  forall (Fc_eq: Fn_cap_equiv Fc Fc') (Fv_eq: Fn_valid_equiv Fv Fv'),
  AG.eq (ag_add_cap_by_obj_index src o i s Fc Fv ag) (ag_add_cap_by_obj_index src' o' i' s' Fc' Fv' ag').
  Proof.
    intros.
    unfold ag_add_cap_by_obj_index.
    generalize (SC.getCap_eq _ _ _ _ _ _ H2 H1 H0); intros Heq.
    case (option_sumbool (SC.getCap i o s)); intros Hopt; [|destruct Hopt as [cap Hopt]];
      rewrite Hopt in *; simpl in *;
    (case (option_sumbool (SC.getCap i' o' s')); intros Hopt'; [|destruct Hopt' as [cap' Hopt']];
      rewrite Hopt' in *; simpl in *; try contradiction); auto.
  Qed.

  Hint Resolve ag_add_cap_by_obj_index_equiv.


  Theorem ag_add_cap_by_obj_index_nondecr : forall src o i s ag ag' Fc Fv,
    AG.Subset ag ag' -> AG.Subset ag (ag_add_cap_by_obj_index src o i s Fc Fv ag').
  Proof.
    intros.
    unfold ag_add_cap_by_obj_index.
    case (option_sumbool (SC.getCap i o s)); intros Hopt; [|destruct Hopt as [cap Hopt]]; rewrite Hopt; 
      simpl; auto.
  Qed.

  Hint Resolve ag_add_cap_by_obj_index_nondecr.

  Theorem ag_add_cap_by_obj_index_add_commute: forall src o i s Fc Fv, 
     Seq.ag_add_commute (ag_add_cap_by_obj_index src o i s Fc Fv).
  Proof.
    intros; unfold ag_add_cap_by_obj_index.
    destruct (SC.getCap i o s); simpl; [eapply ag_add_cap_valid_add_commute | red; intuition].
  Qed.

  Hint Resolve ag_add_cap_by_obj_index_add_commute.

  Theorem ag_add_cap_by_indirect_index_equiv: forall src src' t t' i i' s s' Fc Fc' Fv Fv' ag ag',
  Ref.eq src src' -> Ind.eq t t' -> Ind.eq i i' -> Sys.eq s s' -> AG.eq ag ag' ->
forall (Fc_eq: Fn_cap_equiv Fc Fc') (Fv_eq: Fn_valid_equiv Fv Fv'),
  AG.eq (ag_add_cap_by_indirect_index src t i s Fc Fv ag) 
        (ag_add_cap_by_indirect_index src' t' i' s' Fc' Fv' ag'). 
  Proof.
    intros.
    unfold ag_add_cap_by_indirect_index.
    generalize (SC.getCap_eq _ _ _ _ _ _ H2 H0 H); intros Heq.
    case (option_sumbool (SC.getCap t src s)); intros Hopt; [|destruct Hopt as [cap Hopt]];
      rewrite Hopt in *; simpl in *;
    (case (option_sumbool (SC.getCap t' src' s')); intros Hopt'; [|destruct Hopt' as [cap' Hopt']];
      rewrite Hopt' in *; simpl in *; try contradiction); eauto.
    generalize (Cap.target_eq _ _ Heq); intros; eauto.
  Qed.
 
  Hint Resolve ag_add_cap_by_indirect_index_equiv.

  Theorem ag_add_cap_by_indirect_index_subset: forall src src' t t' i i' s s' Fc Fc' Fv Fv' ag ag',
  Ref.eq src src' -> Ind.eq t t' -> Ind.eq i i' -> Sys.eq s s' -> AG.Subset ag ag' ->
forall (Fc_eq: Fn_cap_equiv Fc Fc') (Fv_eq: Fn_valid_equiv Fv Fv'),
  AG.Subset (ag_add_cap_by_indirect_index src t i s Fc Fv ag) 
        (ag_add_cap_by_indirect_index src' t' i' s' Fc' Fv' ag'). 
  Proof.
    intros.
    unfold ag_add_cap_by_indirect_index.
    generalize (SC.getCap_eq _ _ _ _ _ _ H2 H0 H); intros Heq.
    case (option_sumbool (SC.getCap t src s)); intros Hopt; [|destruct Hopt as [cap Hopt]];
      rewrite Hopt in *; simpl in *;
    (case (option_sumbool (SC.getCap t' src' s')); intros Hopt'; [|destruct Hopt' as [cap' Hopt']];
      rewrite Hopt' in *; simpl in *; try contradiction); auto.
    generalize (Cap.target_eq _ _ Heq); intros; auto.
  Qed.
 
  Hint Resolve ag_add_cap_by_indirect_index_subset.


  Theorem ag_add_cap_by_indirect_index_nondecr: forall src t i s ag ag' Fc Fv,
    AG.Subset ag ag' -> AG.Subset ag (ag_add_cap_by_indirect_index src t i s Fc Fv ag').
  Proof.
    intros.
    unfold ag_add_cap_by_indirect_index.
    unfold option_map1.
    case (option_sumbool (SC.getCap t src s)); intros Hopt; [|destruct Hopt as [cap Hopt]]; rewrite Hopt;
      simpl; auto.
  Qed.

  Hint Resolve ag_add_cap_by_indirect_index_nondecr.

  Theorem ag_add_cap_by_indirect_index_add_commute: forall src t i s Fc Fv, 
     Seq.ag_add_commute (ag_add_cap_by_indirect_index src t i s Fc Fv).
  Proof.
    intros; unfold ag_add_cap_by_indirect_index.
    destruct (SC.getCap t src s); simpl; [eapply ag_add_cap_by_obj_index_add_commute | red; intuition].
  Qed.

  Hint Resolve ag_add_cap_by_indirect_index_add_commute.

  Theorem ag_push_cap_by_indices_equiv: forall o o' i i' o2 o2' i2 i2' s s' Fc Fc' Fv Fv' ag ag',
  Ref.eq o o' -> Ind.eq i i' -> Ref.eq o2 o2' -> Ind.eq i2 i2' -> Sys.eq s s' -> AG.eq ag ag' ->
forall (Fc_eq: Fn_cap_equiv Fc Fc') (Fv_eq: Fn_valid_equiv Fv Fv'),
  AG.eq (ag_push_cap_by_indices o i o2 i2 s Fc Fv ag)
        (ag_push_cap_by_indices o' i' o2' i2' s' Fc' Fv' ag').
  Proof.
    intros.
    unfold ag_push_cap_by_indices.
    generalize (SC.getCap_eq _ _ _ _ _ _ H3 H0 H); intros Heq.
    case (option_sumbool (SC.getCap i o s)); intros Hopt; [|destruct Hopt as [cap Hopt]];
      rewrite Hopt in *; simpl in *;
    (case (option_sumbool (SC.getCap i' o' s')); intros Hopt'; [|destruct Hopt' as [cap' Hopt']];
      rewrite Hopt' in *; simpl in *; try contradiction); eauto.
    generalize (Cap.target_eq _ _ Heq); intros; eauto.    
  Qed.

  Hint Resolve ag_push_cap_by_indices_equiv.

  Theorem ag_push_cap_by_indices_subset: forall o o' i i' o2 o2' i2 i2' s s' Fc Fc' Fv Fv' ag ag',
  Ref.eq o o' -> Ind.eq i i' -> Ref.eq o2 o2' -> Ind.eq i2 i2' -> Sys.eq s s' -> AG.Subset ag ag' ->
forall (Fc_eq: Fn_cap_equiv Fc Fc') (Fv_eq: Fn_valid_equiv Fv Fv'),
  AG.Subset (ag_push_cap_by_indices o i o2 i2 s Fc Fv ag)
        (ag_push_cap_by_indices o' i' o2' i2' s' Fc' Fv' ag').
  Proof.
    intros.
    unfold ag_push_cap_by_indices.
    generalize (SC.getCap_eq _ _ _ _ _ _ H3 H0 H); intros Heq.
    case (option_sumbool (SC.getCap i o s)); intros Hopt; [|destruct Hopt as [cap Hopt]];
      rewrite Hopt in *; simpl in *;
    (case (option_sumbool (SC.getCap i' o' s')); intros Hopt'; [|destruct Hopt' as [cap' Hopt']];
      rewrite Hopt' in *; simpl in *; try contradiction); auto.
    generalize (Cap.target_eq _ _ Heq); intros; auto.    
  Qed.

  Hint Resolve ag_push_cap_by_indices_subset.

  Theorem ag_push_cap_by_indices_nondecr : forall o i o' i' s ag ag' Fc Fv,
    AG.Subset ag ag' -> AG.Subset ag (ag_push_cap_by_indices o i o' i' s Fc Fv ag').
  Proof.
    intros.
    unfold ag_push_cap_by_indices.
    unfold option_map1.
    case (option_sumbool (SC.getCap i o s)); intros Hopt; [|destruct Hopt as [cap Hopt]]; rewrite Hopt; 
      simpl; auto. 
  Qed.

  Hint Resolve ag_push_cap_by_indices_nondecr.

  Theorem ag_push_cap_by_indices_add_commute: forall o i o' i' s Fc Fv, 
     Seq.ag_add_commute (ag_push_cap_by_indices o i o' i' s Fc Fv).
  Proof.
    intros; unfold ag_push_cap_by_indices.
    destruct (SC.getCap i o s); simpl; [eapply ag_add_cap_by_obj_index_add_commute | red; intuition].
  Qed.

  Hint Resolve ag_push_cap_by_indices_add_commute.

  Theorem ag_add_caps_by_index_pair_list_equiv:
  forall src src' o o' ixi_list ixi_list' s s' Fc Fc' Fv Fv' ag ag',
  Ref.eq src src' -> Ref.eq o o' -> Sys.eq s s' -> AG.eq ag ag' ->
forall (Fc_eq: Fn_cap_equiv Fc Fc') (Fv_eq: Fn_valid_equiv Fv Fv') 
(ixi_eq: eqlistA CIL_Facts.ci_eq ixi_list ixi_list'),
  AG.eq (ag_add_caps_by_index_pair_list src o ixi_list s Fc Fv ag)
        (ag_add_caps_by_index_pair_list src' o' ixi_list' s' Fc' Fv' ag').
  Proof.
    intros.
    unfold ag_add_caps_by_index_pair_list.
    induction ixi_eq; simpl; [|destruct H3]; eauto.
  Qed.

  Hint Resolve ag_add_caps_by_index_pair_list_equiv.

  Theorem ag_add_caps_by_index_pair_list_subset:
  forall src src' o o' ixi_list ixi_list' s s' Fc Fc' Fv Fv' ag ag',
  Ref.eq src src' -> Ref.eq o o' -> Sys.eq s s' -> AG.Subset ag ag' ->
forall (Fc_eq: Fn_cap_equiv Fc Fc') (Fv_eq: Fn_valid_equiv Fv Fv') 
(ixi_eq: eqlistA CIL_Facts.ci_eq ixi_list ixi_list'),
  AG.Subset (ag_add_caps_by_index_pair_list src o ixi_list s Fc Fv ag)
        (ag_add_caps_by_index_pair_list src' o' ixi_list' s' Fc' Fv' ag').
  Proof.
    intros.
    unfold ag_add_caps_by_index_pair_list.
    induction ixi_eq; simpl; [|destruct H3]; auto.
  Qed.

  Hint Resolve ag_add_caps_by_index_pair_list_subset.


  Theorem ag_add_caps_by_index_pair_list_nondecr: forall src o ixi_list s ag ag' Fc Fv,
    AG.Subset ag ag' -> AG.Subset ag (ag_add_caps_by_index_pair_list src o ixi_list s Fc Fv ag').
  Proof.
    intros.
    unfold ag_add_caps_by_index_pair_list.
    induction ixi_list; simpl; auto.
  Qed.
  
  Hint Resolve ag_add_caps_by_index_pair_list_nondecr.

  Theorem ag_add_caps_by_index_pair_list_add_commute: forall src o ixi_list s Fc Fv, 
     Seq.ag_add_commute (ag_add_caps_by_index_pair_list src o ixi_list s Fc Fv).
  Proof.
    intros; unfold ag_add_caps_by_index_pair_list.
    induction ixi_list; simpl; eauto; red; [intuition|].
    intros; eapply ag_add_cap_by_obj_index_add_commute; eapply IHixi_list; eauto.
  Qed.

  Hint Resolve ag_add_caps_by_index_pair_list_add_commute.

   Theorem ag_add_cap_valid_std_equiv: Fn_valid_equiv ag_add_cap_valid_std ag_add_cap_valid_std.
   Proof.
     intros.
     unfold Fn_valid_equiv.
   
     unfold ag_add_cap_valid_std; unfold ag_add_cap_valid_allocate.
     intros.
     case (SC.is_alive_dec r s); intros H3; simpl in *; case (SC.is_alive_dec r' s'); intros H3'; simpl in *; auto.
     case (SC.is_alive_dec (Cap.target c) s); intros H4; simpl in *; 
       case (SC.is_alive_dec (Cap.target c') s'); intros H4'; simpl in *; auto.
     contradict H4'; eapply SC.isAlive_eq; [apply Cap.target_eq| |]; eauto. 
     contradict H4; eapply SC.isAlive_eq; [apply Cap.target_eq; apply Cap.eq_sym| apply Sys.eq_sym|]; eauto. 
     contradict H3'; eapply SC.isAlive_eq; eauto. 
     contradict H3; eapply SC.isAlive_eq; [apply Ref.eq_sym|apply Sys.eq_sym|]; eauto. 
  Qed.
  Hint Resolve ag_add_cap_valid_std_equiv.

  (* I don't know why prevous changes have removed this from the hint db *)

  Hint Resolve ARSet.eq_refl.

  Theorem ag_add_caps_reply_equiv:
  forall a a' t t' s s' ag ag',
  Ref.eq a a' -> Ind.eq t t' -> Sys.eq s s' -> AG.eq ag ag' ->
  AG.eq (ag_add_caps_reply a t s ag) (ag_add_caps_reply a' t' s' ag').
  Proof.
   intros.
   unfold ag_add_caps_reply.

   generalize (SC.getCap_eq _ _ _ _ _ _ H1 H0 H); intros Heq.
    case (option_sumbool (SC.getCap t a s)); intros Hopt; [|destruct Hopt as [cap Hopt]];
      rewrite Hopt in *; simpl in *;
    (case (option_sumbool (SC.getCap t' a' s')); intros Hopt'; [|destruct Hopt' as [cap' Hopt']];
      rewrite Hopt' in *; simpl in *; try contradiction); eauto.
  eapply ag_add_cap_valid_equiv; eauto.
  apply Cap.target_eq; eauto.
  eapply CC.mkCap_equiv; eauto.
  Qed.

  Hint Resolve ag_add_caps_reply_equiv.

  Theorem ag_add_caps_reply_subset:
  forall a a' t t' s s' ag ag',
  Ref.eq a a' -> Ind.eq t t' -> Sys.eq s s' -> AG.Subset ag ag' ->
  AG.Subset (ag_add_caps_reply a t s ag) (ag_add_caps_reply a' t' s' ag').
  Proof.
   intros.
   unfold ag_add_caps_reply.

   generalize (SC.getCap_eq _ _ _ _ _ _ H1 H0 H); intros Heq.
    case (option_sumbool (SC.getCap t a s)); intros Hopt; [|destruct Hopt as [cap Hopt]];
      rewrite Hopt in *; simpl in *;
    (case (option_sumbool (SC.getCap t' a' s')); intros Hopt'; [|destruct Hopt' as [cap' Hopt']];
      rewrite Hopt' in *; simpl in *; try contradiction); auto.
  eapply ag_add_cap_valid_subset; auto.
  apply Cap.target_eq; auto.
  eapply CC.mkCap_equiv; auto.
  Qed.

  Hint Resolve ag_add_caps_reply_subset.


  Theorem ag_add_caps_reply_nondecr: forall a t s ag ag',
    AG.Subset ag ag' -> AG.Subset ag (ag_add_caps_reply a t s ag').
  Proof.
    intros.
    unfold ag_add_caps_reply.
    case (option_sumbool (SC.getCap t a s)); intros Heq; [| destruct Heq as [cap Heq]]; rewrite Heq; 
      simpl; auto.
  Qed.
  
  Hint Resolve ag_add_caps_reply_nondecr.
    
  Theorem ag_add_caps_reply_add_commute: forall a t s,
     Seq.ag_add_commute (ag_add_caps_reply a t s).
  Proof.
    intros; unfold ag_add_caps_reply.
    destruct (SC.getCap t a s); simpl; [eapply ag_add_cap_valid_add_commute |red;intuition].
  Qed.

  Hint Resolve ag_add_caps_reply_add_commute. 

  Theorem ag_add_caps_send_equiv:
  forall a a' t t' s s' ixi_list ixi_list' ag ag',
  Ref.eq a a' -> Ind.eq t t' -> Sys.eq s s' -> AG.eq ag ag' ->
  forall (ixi_eq: eqlistA CIL_Facts.ci_eq ixi_list ixi_list'),
  AG.eq (ag_add_caps_send a t ixi_list s ag) (ag_add_caps_send a' t' ixi_list' s' ag').
  Proof.
    intros.
    unfold ag_add_caps_send.
   generalize (SC.getCap_eq _ _ _ _ _ _ H1 H0 H); intros Heq.
    case (option_sumbool (SC.getCap t a s)); intros Hopt; [|destruct Hopt as [cap Hopt]];
      rewrite Hopt in *; simpl in *;
    (case (option_sumbool (SC.getCap t' a' s')); intros Hopt'; [|destruct Hopt' as [cap' Hopt']];
      rewrite Hopt' in *; simpl in *; try contradiction); eauto.
    induction ixi_eq; simpl; [|destruct H3]; eauto.
    eapply ag_add_cap_by_obj_index_equiv; eauto.
    apply Cap.target_eq; eauto.
  Qed.

  Hint Resolve ag_add_caps_send_equiv.

  Theorem ag_add_caps_send_subset:
  forall a a' t t' s s' ixi_list ixi_list' ag ag',
  Ref.eq a a' -> Ind.eq t t' -> Sys.eq s s' -> AG.Subset ag ag' ->
  forall (ixi_eq: eqlistA CIL_Facts.ci_eq ixi_list ixi_list'),
  AG.Subset (ag_add_caps_send a t ixi_list s ag) (ag_add_caps_send a' t' ixi_list' s' ag').
  Proof.
    intros.
    unfold ag_add_caps_send.
   generalize (SC.getCap_eq _ _ _ _ _ _ H1 H0 H); intros Heq.
    case (option_sumbool (SC.getCap t a s)); intros Hopt; [|destruct Hopt as [cap Hopt]];
      rewrite Hopt in *; simpl in *;
    (case (option_sumbool (SC.getCap t' a' s')); intros Hopt'; [|destruct Hopt' as [cap' Hopt']];
      rewrite Hopt' in *; simpl in *; try contradiction); auto.
    induction ixi_eq; simpl; [|destruct H3]; auto.
    eapply ag_add_cap_by_obj_index_subset; eauto.
    apply Cap.target_eq; eauto.
  Qed.

  Hint Resolve ag_add_caps_send_subset.

  
  Theorem ag_add_caps_send_nondecr: forall a t ixi_list s ag ag',
    AG.Subset ag ag' -> AG.Subset ag (ag_add_caps_send a t ixi_list s ag').
  Proof.
    intros.
    unfold ag_add_caps_send.
    case (option_sumbool (SC.getCap t a s)); intros Heq; [| destruct Heq as [cap Heq]]; rewrite Heq; 
      simpl; auto.
  Qed.

  Hint Resolve ag_add_caps_send_nondecr.


  Theorem ag_add_caps_send_add_commute: forall a t ixi_list s,
     Seq.ag_add_commute (ag_add_caps_send a t ixi_list s).
  Proof.
    intros; unfold ag_add_caps_send.
    destruct (SC.getCap t a s); simpl; [red; intros;
      eapply ag_add_caps_by_index_pair_list_add_commute; 
      eapply ag_add_caps_reply_add_commute; eauto
    | eapply ag_add_caps_reply_add_commute].
  Qed.

  Hint Resolve ag_add_caps_send_add_commute. 

    Theorem ag_add_cap_valid_allocate_equiv:  Fn_valid_equiv ag_add_cap_valid_allocate ag_add_cap_valid_allocate.
    Proof.
      unfold Fn_valid_equiv; unfold ag_add_cap_valid_allocate; intros.
     case (SC.is_alive_dec (Cap.target c) s); intros H4; simpl in *;
       case (SC.is_alive_dec (Cap.target c') s'); intros H4'; simpl in *; auto.
     contradict H4'; eapply SC.isAlive_eq; [apply Cap.target_eq| |]; eauto. 
     contradict H4; eapply SC.isAlive_eq; [apply Cap.target_eq; apply Cap.eq_sym| apply Sys.eq_sym|]; eauto. 
    Qed.
  Hint Resolve ag_add_cap_valid_allocate_equiv.


  Theorem ag_add_caps_allocate_equiv:  forall a a' n n' s s' ixi_list ixi_list' ag ag',
  Ref.eq a a' -> Ref.eq n n' -> Sys.eq s s' -> AG.eq ag ag' ->
  forall (ixi_eq: eqlistA CIL_Facts.ci_eq ixi_list ixi_list'),
  AG.eq (ag_add_caps_allocate a n ixi_list s ag) (ag_add_caps_allocate a' n' ixi_list' s' ag').
  Proof.
    intros.
    unfold ag_add_caps_allocate.
    eapply ag_add_cap_equiv; eauto; try (eapply CC.mkCap_equiv; eauto).
  Qed.

  Hint Resolve ag_add_caps_allocate_equiv.

  Theorem ag_add_caps_allocate_subset:  forall a a' n n' s s' ixi_list ixi_list' ag ag',
  Ref.eq a a' -> Ref.eq n n' -> Sys.eq s s' -> AG.Subset ag ag' ->
  forall (ixi_eq: eqlistA CIL_Facts.ci_eq ixi_list ixi_list'),
  AG.Subset (ag_add_caps_allocate a n ixi_list s ag) (ag_add_caps_allocate a' n' ixi_list' s' ag').
  Proof.
    intros.
    unfold ag_add_caps_allocate.
    eapply ag_add_cap_subset; auto; try (eapply CC.mkCap_equiv; auto).
   Qed.

  Hint Resolve ag_add_caps_allocate_subset.

  Theorem ag_add_caps_allocate_nondecr: forall a n ixi_list s ag ag',
    AG.Subset ag ag' -> AG.Subset ag (ag_add_caps_allocate a n ixi_list s ag').
  Proof.
    intros.
    unfold ag_add_caps_allocate.
    eapply ag_add_cap_nondecr.
    eapply ag_add_caps_by_index_pair_list_nondecr; auto.
  Qed.
  
  Hint Resolve ag_add_caps_allocate_nondecr.

  Theorem ag_add_caps_allocate_add_commute: forall a n ixi_list s,
     Seq.ag_add_commute (ag_add_caps_allocate a n ixi_list s).
  Proof.
    red; intros.
    eapply ag_add_cap_add_commute;
      eapply ag_add_caps_by_index_pair_list_add_commute; eauto.
  Qed.

  Hint Resolve ag_add_caps_allocate_add_commute.
    

   (* alright, find whever you proved that add transposes over AG.Equal and use it here *)
   (* after that, your next step is to show equiv over all of your ag_add_cap* fn *)
   (* once that is done, showing dirAcc_approx_dep over all operations should be a snap. *)
   (* from there, showing that potAcc_approx_dep over all operations should also be straightforward. *)
   (* once that is finished, you should be able to reduce them to identity transforms *)

  Theorem ag_add_cap_spec_ag_add_cap_1: forall ref  rgt cap ag,
    ARSet.In rgt (Cap.rights cap) ->
    ~ AG.In (Edges.mkEdge ref (Cap.target cap) rgt) ag ->
    AG.In (Edges.mkEdge ref (Cap.target cap) rgt) (ag_add_cap ref cap ag).
  Proof.
    intros ref rgt cap ag.
    unfold ag_add_cap.
    eapply ARSetProps.fold_rec_bis with (P:= fun rights AG => 
      ARSet.In rgt rights -> ~ AG.In (Edges.mkEdge ref (Cap.target cap) rgt) ag -> AG.In (Edges.mkEdge ref (Cap.target cap) rgt) AG).
          (* equiv of P *)
    intros arset arset' ag' H0 H1 H2; destruct (H0 rgt); auto.
          (* base case, contradiction *)
    intros H0; apply ARSet.empty_1 in H0; contradiction.
          (* step *)
    intros rgt' ag' arset H0 H1 H2 H3 H4.
    eapply AGFacts.add_iff; simpl.
    case (AccessRight.eq_dec rgt rgt'); intros H5.
          (* rgt [=] rgt' *)
    rewrite H5; auto.
          (* rgt [<>] rgt' *)
    right.
    apply H2; auto.
    eapply ARSet.add_3 with rgt'; auto.
  Qed.
  
  Theorem ag_add_cap_spec_ag_add_cap_2: forall src_ref src_ref' tgt_ref rgt cap ag,
    ARSet.In rgt (Cap.rights cap) ->
    Ref.eq tgt_ref (Cap.target cap) ->
    Ref.eq src_ref src_ref' ->
    ~ AG.In (Edges.mkEdge src_ref tgt_ref rgt) ag ->
    AG.In (Edges.mkEdge src_ref tgt_ref rgt) (ag_add_cap src_ref' cap ag).
  Proof.
    intros src_ref src_ref' tgt_ref rgt cap ag.
    unfold ag_add_cap.
    eapply ARSetProps.fold_rec_bis with (P:= fun rights AG => 
      ARSet.In rgt rights ->
      Ref.eq tgt_ref (Cap.target cap) ->
      Ref.eq src_ref src_ref' ->
      ~ AG.In (Edges.mkEdge src_ref tgt_ref rgt) ag -> 
      AG.In (Edges.mkEdge src_ref tgt_ref rgt) AG).
          (* equiv of P *)
    intros arset arset' ag' H0; destruct (H0 rgt); auto.
          (* base case, contradiction *)
    intros H0; apply ARSet.empty_1 in H0; contradiction.
          (* step *)
    intros rgt' ag' arset H0 H1 H2 H3 H4 H5 H6.
    eapply AGFacts.add_iff; simpl.
    case (AccessRight.eq_dec rgt rgt'); intros HeqRef.
          (* rgt [=] rgt' *)
    unfold Ref.eq in *.
    rewrite HeqRef; rewrite H5; rewrite H4; auto.
          (* rgt [<>] rgt' *)
    right.
    apply H2; auto.
    eapply ARSet.add_3 with rgt'; auto.
  Qed.

        (* we need to show the conditions necessary by equiv. *)
        (* basically, we need to show that 
           In (mkEdge ref (target cap) rgt) (ag_add_cap ref cap ag) <- 
           In (mkEdge ref (target cap) rgt) ag \/ In rgt (rights cap) *)
  Theorem ag_add_cap_spec_1 : forall ref rgt cap ag ag',
    AG.eq ag ag' -> 
    ARSet.In rgt (Cap.rights cap) \/ AG.In (Edges.mkEdge ref (Cap.target cap) rgt) ag ->
    AG.In (Edges.mkEdge ref (Cap.target cap) rgt) (ag_add_cap ref cap ag').
  Proof.
    intros.
    case (AGProps.In_dec (Edges.mkEdge ref (Cap.target cap) rgt) ag); intros Hin; 
      destruct H0; auto; try solve [eapply ag_add_cap_nondecr; eauto].
    apply ag_add_cap_spec_ag_add_cap_1; auto.
    intro Hnot; apply Hin; clear Hin;
      eapply ag_eq_Equal; [apply H| apply Hnot].
  Qed.
  
  Theorem ag_add_cap_spec_2 : forall src_ref src_ref' tgt_ref rgt cap ag ag',
    AG.eq ag ag' -> 
    (Ref.eq src_ref src_ref' /\ Ref.eq tgt_ref (Cap.target cap) /\ ARSet.In rgt (Cap.rights cap))
    \/ AG.In (Edges.mkEdge src_ref tgt_ref rgt) ag ->
    AG.In (Edges.mkEdge src_ref tgt_ref rgt) (ag_add_cap src_ref' cap ag').
  Proof.
    intros.
    case (AGProps.In_dec (Edges.mkEdge src_ref tgt_ref rgt) ag); intros Hin; 
      destruct H0; auto; try solve [eapply ag_add_cap_nondecr; eauto].
    destruct H0 as [H1 H0]; destruct H0; apply ag_add_cap_spec_ag_add_cap_2; auto.
    intro Hnot; apply Hin; clear Hin; eapply ag_eq_Equal; [apply H|apply Hnot].
  Qed.


  Theorem ag_add_cap_spec_a: forall edge ref cap ag ag',
    AG.eq ag ag' -> 
    Ref.eq ref (Edges.source edge) /\
    Ref.eq (Cap.target cap) (Edges.target edge) /\ 
    ARSet.In (Edges.right edge) (Cap.rights cap) \/
    AG.In edge ag -> AG.In edge (ag_add_cap ref cap ag').
  Proof.
    intros.
    case (AGProps.In_dec edge ag); intros Hin; destruct H0; auto;
      try solve [eapply ag_add_cap_nondecr; eauto].
    rewrite <- (Edges.edge_rewrite edge); eapply ag_add_cap_spec_2; intuition (try apply Ref.eq_sym; eauto).
  Qed.

  Theorem ag_add_cap_spec_ag_add_cap_3: forall src_ref src_ref' tgt_ref rgt cap ag ag',
    AG.eq ag ag' -> 
    ~ AG.In (Edges.mkEdge src_ref tgt_ref rgt) ag ->
    AG.In (Edges.mkEdge src_ref tgt_ref rgt) (ag_add_cap src_ref' cap ag') ->
    ARSet.In rgt (Cap.rights cap) /\
    Ref.eq tgt_ref (Cap.target cap) /\
    Ref.eq src_ref src_ref'.
  Proof.
    intros src_ref src_ref' tgt_ref rgt cap ag ag'.
    unfold ag_add_cap.
    eapply ARSetProps.fold_rec_bis with (P:= fun rights AG => 
      AG.eq ag ag' ->
      ~ AG.In (Edges.mkEdge src_ref tgt_ref rgt) ag -> 
      AG.In (Edges.mkEdge src_ref tgt_ref rgt) AG ->
      ARSet.In rgt rights /\
      Ref.eq tgt_ref (Cap.target cap) /\
      Ref.eq src_ref src_ref').
    (* equiv of P *)
    intros arset arset' ag'' H0 H1 H2 H3 H4. destruct (H0 rgt); intuition auto.
    (* base case, contradiction *)
    intros; eapply ag_eq_Equal in H1; [apply H0 in H1; contradiction |apply H ].  
    (* step *)
    intros rgt' ag'' arset H0 H1 H2 H3 H4 H5.
    eapply AGFacts.add_iff in H5; simpl in *.

    destruct H5 as [H5 |H5];
      [generalize (Edges.eq_source _ _ H5); intros HeqS; do 2 rewrite Edges.source_rewrite in HeqS;
        generalize (Edges.eq_target _ _ H5); intros HeqT; do 2 rewrite Edges.target_rewrite in HeqT;
          generalize (Edges.eq_right _ _ H5); intros HeqR; do 2 rewrite Edges.right_rewrite in HeqR;
            rewrite HeqS in *; rewrite HeqT in *; rewrite HeqR in *
        | generalize (H2 H3 H4 H5)];

    intuition (try solve [apply ARSetFacts.add_iff; intuition (try apply AccessRight.eq_refl)
      | apply Ref.eq_refl | apply AccessRight.eq_refl]).

  Qed.

  Theorem ag_add_cap_spec_b: forall edge ref cap ag  ag',
    AG.eq ag ag' -> 
    AG.In edge (ag_add_cap ref cap ag) ->
    Ref.eq ref (Edges.source edge) /\
    Ref.eq (Cap.target cap) (Edges.target edge) /\ 
    ARSet.In (Edges.right edge) (Cap.rights cap) \/
    AG.In edge ag'.
  Proof.
    intros.
    case (AGProps.In_dec edge ag); intros Hin; auto.
    right; eapply ag_eq_Equal; [apply AG.eq_sym in H; apply H | apply Hin].
    left.
    rewrite <- (Edges.edge_rewrite edge) in H0.
    rewrite <- (Edges.edge_rewrite edge) in Hin.
    generalize (ag_add_cap_spec_ag_add_cap_3 _ _ _ _ _ _ _ (AG.eq_refl ag) Hin H0); intuition.
  Qed.

  Theorem ag_add_cap_spec: forall edge ref cap ag ag',
    AG.eq ag ag' -> 
    (AG.In edge (ag_add_cap ref cap ag) <->
      Ref.eq ref (Edges.source edge) /\
      Ref.eq (Cap.target cap) (Edges.target edge) /\ 
      ARSet.In (Edges.right edge) (Cap.rights cap) \/
      AG.In edge ag').
  Proof.
    intros; split; solve [eapply ag_add_cap_spec_a; eauto; apply AG.eq_sym; auto |
      eapply ag_add_cap_spec_b; eauto; apply AG.eq_sym; auto].
  Qed.


  Theorem ag_add_cap_mod_spec: forall edge ref cap ag ag' Fc,
    AG.eq ag ag' ->
    (AG.In edge (ag_add_cap_mod ref cap Fc ag) <->
      AG.In edge ag' \/
          Ref.eq ref (Edges.source edge) /\
          Ref.eq (Cap.target (Fc cap)) (Edges.target edge) /\ 
          ARSet.In (Edges.right edge) (Cap.rights (Fc cap))).
  Proof.
    intros.
    unfold ag_add_cap_mod.
    generalize (ag_add_cap_spec edge ref (Fc cap) ag ag' H); intros HFc.
    destruct HFc as [HFc1 HFc2].
    intuition; eauto.
  Qed.

  Theorem ag_add_cap_valid_spec: forall edge ref cap s ag ag' Fc Fv,
    AG.eq ag ag' ->
    (AG.In edge (ag_add_cap_valid ref cap s Fc Fv ag) <->
      (AG.In edge ag' \/
        (Fv ref cap s = true/\
          Ref.eq ref (Edges.source edge) /\
          Ref.eq (Cap.target (Fc cap)) (Edges.target edge) /\ 
          ARSet.In (Edges.right edge) (Cap.rights (Fc cap))))).
  Proof.
    intros.
    unfold ag_add_cap_valid.
    generalize (ag_add_cap_mod_spec edge ref cap ag ag' Fc H); intros Hmod.
    destruct Hmod as [Hmod1 Hmod2]; case (Fv ref cap s);
    intuition; eauto; try discriminate.
  Qed.


(* The only time ag_add_cap_if_exists_spec has been used is during dirAcc <-> dirAcc_spec proofs *)
(* These use Fv := ag_add_cap_valid_st dand Fc := (fun c => c). *)
(* we therefore will specialize it *)
 Theorem ag_add_cap_valid_spec_dirAcc: forall edge ref cap s ag ag',
     AG.eq ag ag' ->
    (AG.In edge (ag_add_cap_valid ref cap s (fun c => c) ag_add_cap_valid_std ag) <->
       (AG.In edge ag' \/
        (SC.is_alive ref s /\
          SC.is_alive (Cap.target cap) s /\
          Ref.eq ref (Edges.source edge) /\
          Ref.eq (Cap.target cap) (Edges.target edge) /\ 
          ARSet.In (Edges.right edge) (Cap.rights cap)))).
  Proof.
    intros.
    generalize (ag_add_cap_valid_spec edge ref cap s ag ag' (fun c => c) ag_add_cap_valid_std H); intros Hv.
    unfold ag_add_cap_valid_std in *; unfold ag_add_cap_valid_allocate in *.
    split; intros Hyp;
    (* case 1 *)
    [eapply Hv in Hyp| eapply Hv]; clear Hv;
    (destruct Hyp as [Hin | [Hfv [Hrgt [Htgt Hin]]]]; [left|right]; intuition auto).
    case (SC.is_alive_dec ref s); intros HaliveR; simpl in *; auto.
    unfold true_bool_of_sumbool in *.
    (* I hate that rewrite won't unify simple unfolds *)
    generalize (proof_l_true_bool_of_sumbool _ (SC.is_alive_dec ref s) HaliveR); intros Hrw; unfold not in Hrw;
    rewrite Hrw in Hfv; clear Hrw; simpl in Hfv;  discriminate Hfv.
    case (SC.is_alive_dec (Cap.target cap) s); intros HaliveT; simpl in *; auto.
    unfold true_bool_of_sumbool in *.
    generalize (proof_l_true_bool_of_sumbool _ (SC.is_alive_dec (Cap.target cap) s) HaliveT); intros Hrw; 
    unfold not in Hrw; rewrite Hrw in Hfv; clear Hrw; rewrite andb_false_intro2 in *; solve [discriminate Hfv | auto].
    (* case 2 *)
    unfold true_bool_of_sumbool.
    repeat progress (rewrite proof_r_true_bool_of_sumbool); auto.
  Qed.


    (* I would like the last -> to be an <->, but we have no existenatials to quantify over *)
    Theorem ag_objs_spec_equiv: forall A A' N N',
     Seq.ag_objs_spec A N -> Seq.ag_objs_spec A' N' -> 
     AG.Equal A A' -> RefSet.Equal N N'.
    Proof.
    unfold Seq.ag_objs_spec.
    intros.
    intro.   
    eapply iff_trans; [apply H| clear H].
    eapply iff_trans; [clear H0|apply iff_sym; eapply H0].
    split; intros [obj [rgt [Hop | Hop]]]; apply ex_intro with obj; apply ex_intro with rgt;
    solve [left; eapply H1; apply Hop| right; eapply H1; apply Hop].
    Qed.


  Theorem ag_objs_spec_add_cap: forall A N, Seq.ag_objs_spec A N -> 
    forall a n r B, AG.Equal (ag_add_cap a (Cap.mkCap n r) A) B ->
    forall N', Seq.ag_objs_spec B N' ->
    forall x, RefSet.In x N' -> ~ Ref.eq x a -> ~ Ref.eq x n -> RefSet.In x N.
  Proof.
    intros A N Hspec a n r.
    unfold ag_add_cap.
    eapply ARSetProps.fold_rec_nodep; intros.
    (* base *)

    eapply ag_objs_spec_equiv; eauto.
    (* step *)
    rewrite CC.mkCap_target in H1.
    eapply H0;
      [eapply AG.eq_refl
      |eapply Seq.ag_objs_spec_ag_objs
      |eapply Seq.ag_objs_spec_add;
         [eapply Seq.ag_objs_spec_ag_objs
         |eapply AGAddEq.Add_eq_full;
            [eapply AG.eq_refl
            |eapply H1
            |eapply AGProps.Add_add]
         |apply H2
         |apply H3
         |apply H4
         |apply H5]
      |auto
      |auto].
  Qed.

  Hint Resolve ag_objs_spec_add_cap.


Theorem ag_objs_add_cap_equiv_empty: forall ag objs,
  Seq.ag_objs_spec ag objs -> 
  forall cap, ARSet.Empty (Cap.rights cap) ->
    forall src objs', 
      Seq.ag_objs_spec 
      (ag_add_cap src cap ag) objs' -> 
      RefSet.eq objs objs'.
Proof.
  intros.
  unfold Seq.ag_objs_spec in *.
  intro.
  eapply iff_trans.
  eapply H.
  eapply iff_trans; [| eapply iff_sym; eapply H1].
  clear H H1.
  
  split; intros [obj [rgt [Hx|Hx]]]; do 2 eapply ex_intro;
    try solve [left;eapply ag_add_cap_nondecr; eauto | right ; eapply ag_add_cap_nondecr; eauto

|  eapply ARSetFacts.is_empty_iff in H0;
  rewrite ARSetEqProps.is_empty_equal_empty in H0;
  eapply ARSetFacts.equal_iff in H0;

    eapply ag_add_cap_equiv in Hx;
      [ 
        | eapply Ref.eq_refl
        | eapply Cap.mkCap_eq; split; [eapply Ref.eq_refl | eapply ARSet.eq_sym; apply H0]
        | eapply AG.eq_refl
      ];
    unfold ag_add_cap in Hx;
    eapply AG.eq_sym in Hx; 
      [
        | eapply ARSetFold.fold_foldEqual with (eqA:=AG.eq) ;
          [ eapply AG_EQ
            | rewrite CC.mkCap_rights; eapply ARSet.eq_refl
            | apply AG.eq_refl
            | apply ARSetFold.foldEqual_refl;
              unfold Proper; unfold respectful; intros;
                rewrite H; eapply ag_eq_Equal;eapply AGAddEq.add_equal_complete; simpl; auto

            |unfold transpose; intros; eapply AGProps.add_add; simpl; auto
          ]
      ]; try rewrite ARSetProps.fold_empty in Hx; intuition eauto].

Qed.

Theorem ag_objs_spec_add_equiv: forall ag objs,
  Seq.ag_objs_spec ag objs ->
  forall src tgt rgt objs', Seq.ag_objs_spec (AG.add (Edges.mkEdge src tgt rgt) ag) objs' ->
    RefSet.eq objs' (RefSet.add src (RefSet.add tgt objs)).
Proof.
  intros.
  eapply RefSetEqEqual.eq_Equal.
  intro ref.
  eapply iff_trans.
  eapply H0.
  clear H0.
  split; intro.

  destruct H0 as [obj' [rgt' [H0|H0]]];
    (apply RefSetFacts.add_iff;
      case (Ref.eq_dec ref src); intros Hcase; [left;auto |right];
        apply RefSetFacts.add_iff;
          case (Ref.eq_dec ref tgt); intros Hcase'; [left;auto |right];
            eapply H; do 2 eapply ex_intro;
              eapply AGFacts.add_iff in H0; simpl in *; destruct H0 as [[H0 [H0' _]]|H0]; 
                [apply Ref.eq_sym in H0; apply Ref.eq_sym in H0'; contradiction|]; 
                solve [left; apply H0|right; apply H0]).

 eapply RefSetFacts.add_iff in H0.
 case (Ref.eq_dec ref src); intros Hcase; destruct H0;
 try apply Ref.eq_sym in H0; try contradiction;
   [  do 2 eapply ex_intro; left; apply AGFacts.add_iff; left; rewrite H0; apply Edge.eq_refl
     | do 2 eapply ex_intro; left; apply AGFacts.add_iff; left; rewrite Hcase; apply Edge.eq_refl
     |].

 eapply RefSetFacts.add_iff in H0.
 case (Ref.eq_dec ref tgt); intros Hcase2; destruct H0;
 try apply Ref.eq_sym in H0; try contradiction;
   [ do 2 eapply ex_intro; right; apply AGFacts.add_iff; left; rewrite Hcase2; apply Edge.eq_refl
     | do 2 eapply ex_intro; right; apply AGFacts.add_iff;left; rewrite Hcase2; apply Edge.eq_refl
     | ].

 eapply H in H0; destruct H0 as [obj' [rgt' [H0|H0]]];
 do 2 eapply ex_intro; [left|right];
 eapply AGFacts.add_iff; right; eauto.
  
Qed.




Theorem ag_objs_add_cap_equiv: forall ag objs,
    Seq.ag_objs_spec ag objs -> 
    forall cap src objs', 
      Seq.ag_objs_spec (ag_add_cap src cap ag) objs' ->
      RefSet.eq objs' (if (ARSet.is_empty (Cap.rights cap)) then objs else (RefSet.add src (RefSet.add (Cap.target cap) objs))).
Proof.
  (* generalize cap out of the picture *)
  unfold ag_add_cap.
  intros ag objs Hobjs cap src.
  generalize (Cap.target cap); intros tgt.
  generalize (Cap.rights cap); intros right_set.
  clear cap.
  (* carefully setup P in fold_rec_bis to have the right set type *)
  intros objs' Hobjs'.
  revert Hobjs; revert objs; revert Hobjs'; revert objs'.


  eapply ARSetProps.fold_rec_bis with 
    (P:= fun m a =>
      forall objs' : RefSet.t,
        Seq.ag_objs_spec a objs' ->
        forall objs : RefSet.t,
          Seq.ag_objs_spec ag objs ->
          RefSet.eq objs'
          (if ARSet.is_empty m
            then objs
            else RefSet.add src (RefSet.add tgt objs))); intros.



  (* compat *)
  case (sumbool_of_bool (ARSet.is_empty s)) as [Hempty|Hempty];
    (rewrite Hempty in *;
      rewrite ARSetFacts.is_empty_m in Hempty; [| apply H];
        rewrite Hempty in *; clear Hempty; eapply H0; auto).

  (* base *)
  generalize ARSet.empty_1; intros Hempty; eapply ARSetFacts.is_empty_iff in Hempty; rewrite Hempty.
  eapply ag_objs_spec_equiv; eauto.

  (* step *)

  rewrite ARSetAddEq.is_empty_add.  
  generalize (Seq.ag_objs_spec_ag_objs a); generalize (Seq.ag_objs a); intros a_objs Ha_objs.

  case (sumbool_of_bool (ARSet.is_empty s')) as [Hempty'|Hempty']; rewrite Hempty' in *;
  generalize (H1 _ Ha_objs _ H3); intros H1'; rewrite <- H1';

  (* empty s' *)

    (eapply ag_objs_spec_add_equiv in H2;[|apply Ha_objs]; auto).

  (* ~ empty s' *)

    rewrite H2; rewrite H1'.
    rewrite RefSetProps.add_add with (x:=tgt) (x':=src).
    do 2 rewrite RefSetAddEq.double_add. apply RefSet.eq_refl.
Qed.

Implicit Arguments ag_objs_add_cap_equiv [ag objs cap src objs'].

Theorem ag_objs_spec_add_cap_equiv_nonempty: forall ag objs,
  Seq.ag_objs_spec ag objs -> 
  forall cap, ~ ARSet.Empty (Cap.rights cap) ->
    forall src objs', 
      Seq.ag_objs_spec (ag_add_cap src cap ag) objs' -> 
      RefSet.eq objs' (RefSet.add src (RefSet.add (Cap.target cap) objs)).
Proof.
  intros.
  generalize (ag_objs_add_cap_equiv H H1).
  case (bool_dec (ARSet.is_empty (Cap.rights cap)) true); intros Hcase;
    [eapply ARSetFacts.is_empty_iff in Hcase; contradiction
      | eapply not_true_is_false in Hcase; rewrite Hcase in *; auto].
Qed.

Theorem ag_objs_add_cap_mod_target_equiv: forall ag objs, Seq.ag_objs_spec ag objs ->
  forall src cap add_objs, Seq.ag_objs_spec (ag_add_cap src cap ag) add_objs ->
    forall Fc mod_objs, Seq.ag_objs_spec (ag_add_cap_mod src cap Fc ag) mod_objs ->
      Ref.eq (Cap.target cap) (Cap.target (Fc cap)) ->
      ARSet.Subset (Cap.rights (Fc cap)) (Cap.rights cap) ->
      RefSet.eq mod_objs (if (ARSet.is_empty (Cap.rights (Fc cap))) then objs else add_objs).
Proof.
  intros ag objs Hag_objs src cap add_objs Hadd_objs Fc mod_objs Hmod_objs HFcTargetEq HFcRightsSub.
  unfold ag_add_cap_mod in *.
  eapply RefSetEqEqual.eq_Equal.
  generalize (ag_objs_add_cap_equiv Hag_objs Hmod_objs); intros Heq1.
  eapply RefSet.eq_trans; [apply Heq1|clear Heq1].
  case (sumbool_of_bool (ARSet.is_empty (Cap.rights (Fc cap)))); intros Hcase; 
    rewrite Hcase in *; simpl in *; try solve [apply RefSet.eq_refl].
  
  generalize (ag_objs_add_cap_equiv Hag_objs Hadd_objs); intros Heq1.
  eapply RefSet.eq_sym; eapply RefSet.eq_trans; [apply Heq1|clear Heq1].
  assert (ARSet.is_empty (Cap.rights cap) = false) as Hcase'.

  case (sumbool_of_bool (ARSet.is_empty (Cap.rights cap))); intros Hnot; auto.
  eapply ARSetEqProps.choose_mem_3 in Hcase; destruct Hcase as [x [Hcoose Hmem]].
  apply ARSetFacts.is_empty_iff in Hnot.
  eapply Hnot in HFcRightsSub; try contradiction.
  eapply ARSetFacts.mem_iff in Hmem; eapply Hmem.
  
  rewrite Hcase'. 
  unfold Ref.eq in *.
  rewrite HFcTargetEq.
  eapply RefSet.eq_refl.
Qed.

Implicit Arguments ag_objs_add_cap_mod_target_equiv [ag objs src cap add_objs Fc mod_objs].

Theorem ag_objs_ag_add_cap_valid: forall ag objs, Seq.ag_objs_spec ag objs ->
  forall src cap Fc mod_objs, Seq.ag_objs_spec (ag_add_cap_mod src cap Fc ag) mod_objs ->
    Ref.eq (Cap.target cap) (Cap.target (Fc cap)) ->
    ARSet.Subset (Cap.rights (Fc cap)) (Cap.rights cap) ->
    forall s Fv valid_objs, Seq.ag_objs_spec (ag_add_cap_valid src cap s Fc Fv ag) valid_objs ->
      RefSet.eq valid_objs (if (Fv src cap s) then mod_objs else objs).
Proof.
  intros ag objs Hag_objs src cap Fc mod_objs Hmod_objs HRefEq HARSub s Fv valid_objs Hvalid_objs.
  unfold ag_add_cap_valid in *.
  eapply RefSetEqEqual.eq_Equal.
  case (sumbool_of_bool (Fv src cap s)); intros Hcase; rewrite Hcase in *; simpl in *; 
    eapply ag_objs_spec_equiv; eauto.
Qed.



Theorem ag_objs_ag_add_cap_by_obj_index: forall ag src o i s Fc Fv new_objs, 
  Seq.ag_objs_spec (ag_add_cap_by_obj_index src o i s Fc Fv ag) new_objs ->
    forall cap, Ref.eq (Cap.target cap) (Cap.target (Fc cap)) ->
      ARSet.Subset (Cap.rights (Fc cap)) (Cap.rights cap) ->
      forall prev_objs,
        option_map1 
        (fun cap=> Seq.ag_objs_spec (ag_add_cap_valid src cap s Fc Fv ag) prev_objs)
        (Seq.ag_objs_spec ag prev_objs)
        (SC.getCap i o s) ->
  RefSet.eq new_objs prev_objs.
Proof.
  intros.
  unfold ag_add_cap_by_obj_index in *.
  case (option_sumbool (SC.getCap i o s)) as [Hcase | [cap' Hcase]]; rewrite Hcase in *; simpl in *;
    eapply ag_objs_spec_equiv; eauto.
Qed.

  Theorem dirAcc_inner_nondecr: forall src_ref src_obj s ag ag',
    AG.Subset ag ag' -> AG.Subset ag (dirAcc_inner src_ref src_obj s ag').
  Proof.
    intros.
    unfold dirAcc_inner.
    eapply Obj_Props.fold_rec_nodep; intros; auto.
  Qed.
  
  Hint Resolve dirAcc_inner_nondecr.


  Theorem dirAcc_outer_nondecr: forall s ag ag',
    AG.Subset ag ag' -> AG.Subset ag (dirAcc_outer s ag').
  Proof.
    intros.
    unfold dirAcc_outer.
    eapply Sys_Props.fold_rec_nodep; intros; auto.
  Qed.
    

  Theorem dirAcc_inner_spec_a_1: forall ag src_ref src_obj s ind cap rgt,
    SC.is_alive src_ref s -> Obj.MapS.MapsTo ind cap src_obj ->
    SC.is_alive (Cap.target cap) s -> ARSet.In rgt (Cap.rights cap) ->
    AG.In (Edges.mkEdge src_ref (Cap.target cap) rgt) (dirAcc_inner src_ref src_obj s ag).
  Proof.
    intros ag src_ref src_obj s ind cap rgt.
    unfold dirAcc_inner.
    eapply Obj_Props.fold_rec_bis with 
      (P := fun OBJ AG =>
        SC.is_alive src_ref s ->
        Obj.MapS.MapsTo ind cap OBJ ->
        SC.is_alive (Cap.target cap) s ->
        ARSet.In rgt (Cap.rights cap) ->
        AG.In (Edges.mkEdge src_ref (Cap.target cap) rgt) AG); intros; auto.
    (* equiv of p *)
    intuition; apply Obj.MapS.find_1 in H2; rewrite <- H in H2; apply Obj.MapS.find_2 in H2; apply H5 in H2; auto.
    (* base case *)
    apply Obj_Facts.empty_mapsto_iff in H0; contradiction.
    (* step *)
    apply Obj_Facts.add_mapsto_iff in H3; destruct H3;destruct H3.
    (* eq case *)
    rewrite H6 in *; clear H6 e.
    eapply ag_add_cap_valid_spec_dirAcc.
    apply AG.eq_refl.
    right; intuition eauto. rewrite Edges.source_rewrite. apply Ref.eq_refl.
    rewrite Edges.target_rewrite. apply Ref.eq_refl.
    (* neq case, use IH *)
    intuition; eapply ag_add_cap_valid_nondecr; [apply AGProps.subset_refl | auto].
  Qed.

  Theorem dirAcc_inner_spec_a: forall src_ref src_obj s ag ag' edge,
    AG.eq ag ag' -> 
    AG.In edge ag \/
    SC.is_alive src_ref s /\ 
    (exists ind, exists cap, Obj.MapS.MapsTo ind cap src_obj /\ (SC.is_alive (Cap.target cap) s) /\
      exists rgt, ARSet.In rgt (Cap.rights cap) /\ Edge.eq (Edges.mkEdge src_ref (Cap.target cap) rgt) edge) ->
        AG.In edge (dirAcc_inner src_ref src_obj s ag').
  Proof.
    intros.
    case (AGProps.In_dec edge ag); intros Hin; 
      destruct H0; auto; try solve [eapply dirAcc_inner_nondecr; eauto].
    destruct H0.
    destruct H1 as [ind H1].
    destruct H1 as [cap H1].
    destruct H1.
    destruct H2.
    destruct H3 as [rgt H3].
    destruct H3.
    (*Module AGFacts := AGFacts. *)
    eapply AGFacts.In_eq_iff; [apply Edge.eq_sym in H4; apply H4|].
    eapply dirAcc_inner_spec_a_1; eauto.
  Qed.
      

  Theorem dirAcc_inner_spec_b_1: forall src_ref src_obj s edge ag ag',
    AG.eq ag ag' ->
    ~ AG.In edge ag ->
    AG.In edge (dirAcc_inner src_ref src_obj s ag') ->
    SC.is_alive src_ref s /\
    (exists ind, exists cap ,Obj.MapS.MapsTo ind cap src_obj /\
        SC.is_alive (Cap.target cap) s /\
        (exists rgt, ARSet.In rgt (Cap.rights cap) /\
           Edges.AccessEdge.eq (Edges.mkEdge src_ref (Cap.target cap) rgt) edge)).
  Proof.
    intros src_ref src_obj s edge ag ag'.
    unfold dirAcc_inner.
    eapply Obj_Props.fold_rec_bis with (P:=  fun OBJ AG =>
      AG.eq ag ag' ->
      ~ AG.In edge ag ->
      AG.In edge AG ->
      SC.is_alive src_ref s /\
      (exists ind, exists cap ,Obj.MapS.MapsTo ind cap OBJ /\
        SC.is_alive (Cap.target cap) s /\
        (exists rgt, ARSet.In rgt (Cap.rights cap) /\
          Edges.AccessEdge.eq (Edges.mkEdge src_ref (Cap.target cap) rgt) edge))); intros; auto.
    (* equiv of P *)
    generalize (H0 H1 H2 H3); clear H0; intros H0.
    destruct_inner H0 H4 H5 H6 H7.
    split; auto; apply ex_intro with ind; auto; apply ex_intro with cap; auto;
      split; 
        [apply Obj.MapS.find_2; rewrite <- H; apply Obj.MapS.find_1; auto 
          | split; auto; apply ex_intro with rgt; auto].
    (* base case *)
    intros;  eapply ag_eq_Equal in H1 ; [apply H0 in H1 |apply H ]; contradiction.
    (* step *)
    generalize (H1 H2 H3); clear H1; intro H1.
    (* we need cases before we apply add_mapsto_iff *)
    case (AGProps.In_dec edge a); intros Hin.
    (* in case *)
    generalize (H1 Hin); clear H1; intros H1.
    destruct_inner H1 H5 H6 H7 H8.
    split; auto; apply ex_intro with ind; auto; apply ex_intro with cap; auto; split.
    (* show that MapsTo ind cap (add k e m') *)
    eapply Obj_Facts.add_mapsto_iff.
    (* ~ In k m', but In ind m', therefore ~ k [=] ind by contradiction. *)
    right; split; auto.
    (* contradiction *)
    intro.
    apply (Obj.MapS.MapsTo_1 (Ind.eq_sym H9)) in H5.
    apply H0.
    eapply ex_intro. 
    apply H5.
    (* continue breakdown *)
    split; auto.
    eapply ex_intro with rgt; split; auto.
    (* ~ in case *)
    generalize (ag_add_cap_valid_spec_dirAcc edge src_ref e s _ _ (AG.eq_refl a)); intros Hadd.
    destruct Hadd as [Hadd _].
    generalize (Hadd H4); clear Hadd; intros Hadd.
    intuition eauto.
    apply ex_intro with k; apply ex_intro with e; intuition auto.  
    eapply Obj_Facts.add_mapsto_iff; left; intuition auto.
    eapply ex_intro with (Edges.right edge); eauto.
    split; eauto.
    (* edge eq *)
    rewrite <- (Edges.edge_rewrite edge).
    apply Edges.edge_equal; eauto. rewrite Edges.right_rewrite. apply AccessRight.eq_refl.
  Qed.

  Theorem dirAcc_inner_spec_b: forall src_ref src_obj s ag ag' edge,
    AG.eq ag ag' -> 
    AG.In edge (dirAcc_inner src_ref src_obj s ag') ->
    AG.In edge ag \/
    SC.is_alive src_ref s /\ 
    (exists ind, exists cap, Obj.MapS.MapsTo ind cap src_obj /\ (SC.is_alive (Cap.target cap) s) /\
      exists rgt, ARSet.In rgt (Cap.rights cap) /\ Edge.eq (Edges.mkEdge src_ref (Cap.target cap) rgt) edge).
  Proof.
    intros.
    case (AGProps.In_dec edge ag); intros Hin; auto.
    right.
    eapply dirAcc_inner_spec_b_1; try apply H; auto.
  Qed.

  Theorem dirAcc_inner_spec :forall src_ref src_obj s ag ag' edge,
    AG.eq ag ag' ->
    (AG.In edge (dirAcc_inner src_ref src_obj s ag) <-> 
      (AG.In edge ag' \/ 
        ((SC.is_alive src_ref s) /\ 
          exists ind, exists cap, Obj.MapS.MapsTo ind cap src_obj /\ (SC.is_alive (Cap.target cap) s) /\
            exists rgt, ARSet.In rgt (Cap.rights cap) /\ Edge.eq (Edges.mkEdge src_ref (Cap.target cap) rgt) edge))).
  Proof.
    intros.
    split; intros.
    eapply dirAcc_inner_spec_b; apply AG.eq_sym in H; try apply H; auto.
    eapply dirAcc_inner_spec_a; eauto; try apply AG.eq_sym; auto.
  Qed.

    Theorem dirAcc_outer_spec_a_1: forall s ag src_ref src_obj ind cap rgt,
      SC.getObj src_ref s = Some src_obj ->
      SC.is_alive src_ref s -> Obj.MapS.MapsTo ind cap src_obj ->
      SC.is_alive (Cap.target cap) s -> ARSet.In rgt (Cap.rights cap) ->
      AG.In (Edges.mkEdge src_ref (Cap.target cap) rgt) (dirAcc_outer s ag).
    Proof.
      intros s ag src_ref src_obj ind cap rgt.
      unfold dirAcc_outer.
      eapply Sys_Props.fold_rec_bis with (P:= fun STATE AG => 
        SC.getObj src_ref STATE = Some src_obj ->
        SC.is_alive src_ref s ->  
        Obj.MapS.MapsTo ind cap src_obj -> (* we're recursing down for src_ref *)
        SC.is_alive (Cap.target cap) s -> (* we may have recursed past (target cap), so we can't recurse on this one. *)
        ARSet.In rgt (Cap.rights cap) ->
        AG.In (Edges.mkEdge src_ref (Cap.target cap) rgt) AG); intros.
    (* compat P *)
    unfold SC.is_alive in *.
    unfold SC.is_label in *.
    unfold SC.getLabel in *.
    unfold SC.getObj in *.
    unfold SC.getObjTuple in *.
    unfold option_map in *.
    unfold option_map1 in *.
    case (option_sumbool (Sys.MapS.find src_ref m')); intros Hfind; [|destruct Hfind as [x Hfind]]; rewrite Hfind in *;
      try discriminate H1.
    rewrite <- H in Hfind.
    rewrite Hfind in H0; simpl in H0.
    apply H0; auto.
    (* base case *)
    unfold SC.getObj in *.
    unfold SC.getObjTuple in *.
    rewrite Sys_Facts.empty_o in H;  simpl in *; discriminate.
    (* step *)
  (* diracc_inner_spec_a_1 :  forall ag src_ref src_obj s ind cap rgt,
     SC.is_alive src_ref s -> Obj.MapS.MapsTo ind cap src_obj ->
     SC.is_alive (Cap.target cap) s -> ARSet.In rgt (Cap.rights cap) ->
     AG.In (Edges.mkEdge src_ref (Cap.target cap) rgt) (dirAcc_inner src_ref src_obj s ag) *)
    (* the cases are defined by add_mapsto_iff.  if k[=]src_ref, then reduce to In on src_ref and
       apply dirAcc_inner_spec_a_1.  Otherwise, apply H1 as IH. *)
    unfold SC.getObj in H2.
    unfold SC.getObjTuple in H2.
    case (option_sumbool (Sys.MapS.find src_ref (Sys.MapS.add k e m'))); intros Hfind; [|destruct Hfind as [x Hfind]]; rewrite Hfind in *; try discriminate H2.
    apply Sys.MapS.find_2 in Hfind.
    simpl in H2; injection H2 as Heq.
    apply Sys_Facts.add_mapsto_iff in Hfind; destruct Hfind as [Hcase|Hcase]; destruct Hcase.
    (* case where k [=] src_ref, e = x *)
    apply AG.In_1 with (Edges.mkEdge k (Cap.target cap) rgt); rewrite H7; auto.
    eapply dirAcc_inner_spec_a_1; auto.
    (* is_alive k s *)
    unfold SC.is_alive in H3; unfold SC.is_label in H3; unfold SC.getLabel in H3; unfold SC.getObjTuple in H3; simpl in H3;
    rewrite Sys_Facts.find_o with (y:=k)in H3;  try apply Ref.eq_sym; auto.
    rewrite H8 in *.
    rewrite Heq in *; apply H4.
    (* case where k [<>] src_ref *)
    eapply dirAcc_inner_nondecr with a; auto.
    apply H1; eauto.
    unfold SC.getObj. unfold SC.getObjTuple. apply Sys.MapS.find_1 in H8. rewrite H8; auto.
    Qed.    

  Theorem dirAcc_outer_spec_a: forall s ag ag' edge,
    AG.eq ag ag' ->
    (AG.In edge ag' \/ 
      (exists src_ref, SC.is_alive src_ref s /\ 
        exists src_obj, SC.getObj src_ref s = Some src_obj /\
          exists ind, exists cap, Obj.MapS.MapsTo ind cap src_obj /\ (SC.is_alive (Cap.target cap) s) /\
            exists rgt, ARSet.In rgt (Cap.rights cap) /\ Edge.eq (Edges.mkEdge src_ref (Cap.target cap) rgt) edge)) ->
    AG.In edge (dirAcc_outer s ag).
  Proof.
    intros.
    case (AGProps.In_dec edge ag); intros Hin;
      destruct H0; auto; try solve [eapply dirAcc_outer_nondecr; eauto].
    (* blow things apart to a reduced form *)
    destruct H0 as [src_ref H0]; destruct H0 as [H0 H1].
    destruct H1 as [src_obj H1]; destruct H1 as [H1 H2].
    destruct H2 as [ind H2]; destruct H2 as [cap H2];
      destruct H2 as [H2 H3]; destruct H3 as [H3 H4].
    destruct H4 as [rgt H4]; destruct H4 as [H4 H5].
    (* rework edge to an equivalent edge *)
    eapply AGFacts.In_eq_iff;[apply Edge.eq_sym in H5; apply H5|].
    apply dirAcc_outer_spec_a_1 with (src_obj := src_obj) (ind:=ind); auto.
  Qed.
    Theorem dirAcc_outer_spec_b_1 : forall s edge ag ag',
      AG.eq ag ag' ->
      ~ AG.In edge ag ->
      AG.In edge (dirAcc_outer s ag') ->
      exists src_ref,
        SC.is_alive src_ref s /\
        (exists src_obj,
          SC.getObj src_ref s = Some src_obj /\
          (exists ind, exists cap,
            Obj.MapS.MapsTo ind cap src_obj /\
              SC.is_alive (Cap.target cap) s /\
              (exists rgt,
                ARSet.In rgt (Cap.rights cap) /\
                Edge.eq (Edges.mkEdge src_ref (Cap.target cap) rgt) edge))).
    Proof.
      intros s edge ag ag'.
      unfold dirAcc_outer.
      eapply Sys_Props.fold_rec_bis with (P:= fun STATE AG =>
        AG.eq ag ag' ->
        ~ AG.In edge ag ->
        AG.In edge AG ->
        (exists src_ref,
          SC.is_alive src_ref s /\
          (exists src_obj,
            SC.getObj src_ref STATE = Some src_obj /\
            (exists ind, exists cap,
              Obj.MapS.MapsTo ind cap src_obj /\
              SC.is_alive (Cap.target cap) s /\
              (exists rgt,
                ARSet.In rgt (Cap.rights cap) /\
                Edge.eq (Edges.mkEdge src_ref (Cap.target cap) rgt) edge))))); intros.
      (* compatP *)
      generalize (H0 H1 H2 H3); clear H0; intros H0.
      destruct_outer H0 H4 H5 H6 H7 H8.
      apply ex_intro with src_ref; auto; split; auto; apply ex_intro with src_obj; auto; split; auto.
      (* getObj src_ref m' = Some src_obj *)
      unfold SC.getObj in *; unfold SC.getObjTuple in *;
      case (option_sumbool (Sys.MapS.find src_ref m)); intros Hfind; 
        [| destruct Hfind as [tuple Hfind]]; rewrite Hfind in *; simpl in *; 
          [discriminate | injection H4; intros Heq; rewrite H in Hfind; rewrite Hfind; auto].
      apply ex_intro with ind; auto; apply ex_intro with cap; auto; split; auto; split; auto.
      apply ex_intro with rgt; auto; intuition.
      (* base *)
      eapply ag_eq_Equal in H1; [|apply H ];contradiction.
      (* step *)
      generalize (H1 H2 H3); clear H1; intro H1.
      case (AGProps.In_dec edge a); intros Hin.
      (* In case *)
      apply H1 in Hin; clear H1.
      destruct_outer Hin H5 H6 H7 H8 H9.
      apply ex_intro with src_ref; auto; split; auto; apply ex_intro with src_obj; auto; split; auto.
      (* SC.getObj src_ref (Sys.MapS.add k e m') = Some src_obj *)
      unfold SC.getObj in *.
      unfold SC.getObjTuple in *.
      (* find tuple1 *)
      case (option_sumbool (Sys.MapS.find src_ref m')); intros Hfind; [|destruct Hfind as [tuple Hfind]]; rewrite Hfind in *; simpl in *; [discriminate|injection H5; intros Heq].
      (* find tuple2 *)
      case (option_sumbool (Sys.MapS.find src_ref (Sys.MapS.add k e m'))); intros Hfind2; [|destruct Hfind2 as [tuple2 Hfind2]]; rewrite Hfind2 in *; simpl in *.
      (* none tuple2 *)
      apply Sys.MapS.find_2 in Hfind.
      assert (Sys.MapS.In src_ref (Sys.MapS.add k e m')).
      eapply Sys_Facts.add_in_iff; right; apply ex_intro with tuple; auto.
      apply Sys_Facts.in_find_iff in H1; contradiction.
      (* some tuple2 *)
      apply Sys.MapS.find_2 in Hfind2. apply Sys_Facts.add_mapsto_iff in Hfind2.
      destruct Hfind2 as [Hfind2 | Hfind2]; destruct Hfind2 as [Hfind2 Hfind2']; auto.
      apply Sys.MapS.find_2 in Hfind.
      apply Sys.MapS.MapsTo_1 with (y:=k) in Hfind; auto.
      assert (Sys.MapS.In k m'); [apply ex_intro with tuple; auto | contradiction].
      apply Sys.MapS.find_1 in Hfind2'.
      rewrite Hfind in Hfind2'.
      injection Hfind2' as HfindEq.
      rewrite <- HfindEq; auto.
      (* continue instantiation *)
      apply ex_intro with ind; auto; apply ex_intro with cap; auto; split; auto; split; auto.
      apply ex_intro with rgt; auto.
      (* ~ In case *)
      clear H1.
      generalize (dirAcc_inner_spec_b k (SC.tupleGetObj e) s _ _ edge (AG.eq_refl a) H4); intros Hinner.
      destruct Hinner as [Hinner | Hinner]; try contradiction.
      destruct_inner Hinner H5 H6 H7 H8.
      apply ex_intro with k; auto; split; auto.
      apply ex_intro with (SC.tupleGetObj e); auto; split; auto.
      unfold SC.getObj; unfold SC.getObjTuple;
        assert (Sys.MapS.find k (Sys.MapS.add k e m') = Some e) as Hfind;
          [apply Sys.MapS.find_1; eapply Sys_Facts.add_mapsto_iff; intuition 
            | rewrite Hfind; auto].
      apply ex_intro with ind; auto; apply ex_intro with cap; auto; split; auto; split; auto; apply ex_intro with rgt; auto.
    Qed.

  Theorem dirAcc_outer_spec_b: forall s ag ag' edge,
    AG.eq ag ag' -> 
    AG.In edge (dirAcc_outer s ag') ->
    AG.In edge ag \/ 
      (exists src_ref, SC.is_alive src_ref s /\ 
        exists src_obj, SC.getObj src_ref s = Some src_obj /\
          exists ind, exists cap, Obj.MapS.MapsTo ind cap src_obj /\ (SC.is_alive (Cap.target cap) s) /\
            exists rgt, ARSet.In rgt (Cap.rights cap) /\ Edge.eq (Edges.mkEdge src_ref (Cap.target cap) rgt) edge).
  Proof.
    intros.
    case (AGProps.In_dec edge ag); intros Hin; eauto.
    right.
    eapply dirAcc_outer_spec_b_1; try apply H; auto.
  Qed.
    
Theorem dirAcc_outer_spec :forall s ag ag' edge,
    AG.eq ag ag' ->
    (AG.In edge (dirAcc_outer s ag) <-> 
      (AG.In edge ag' \/ 
        (exists src_ref, SC.is_alive src_ref s /\ 
          exists src_obj, SC.getObj src_ref s = Some src_obj /\
          exists ind, exists cap, Obj.MapS.MapsTo ind cap src_obj /\ (SC.is_alive (Cap.target cap) s) /\
            exists rgt, ARSet.In rgt (Cap.rights cap) /\ Edge.eq (Edges.mkEdge src_ref (Cap.target cap) rgt) edge))).
  Proof.
    intros.
    split; intros.
    eapply dirAcc_outer_spec_b; apply AG.eq_sym in H; try apply H; auto.
    eapply dirAcc_outer_spec_a; eauto; try apply AG.eq_sym; auto.
  Qed.

  Theorem dirAcc_spec_dirAcc: forall s, dirAcc_spec s (dirAcc s).
  Proof.
    intros.
    unfold dirAcc.
    unfold dirAcc_spec.
    intros edge.
    generalize (dirAcc_outer_spec s _ _ edge (AG.eq_refl AG.empty)); intros Hda.
    destruct Hda as [Hda_1 Hda_2].
    split; intros.
    
    destruct_dirAcc H s'' HeqS src_ref src lbl type sched HmapS src' lbl' type' sched' 
    HeqP HeqL ind cap1 Hmap0 cap1_obj cap1_lbl cap1_type cap1_sched HmapScap
    cap1_obj' cap1_lbl' cap1_type' cap1_sched' HeqPcap HaliveCap rgt HinR HeqEdge.

    apply Hda_2; right.
    apply ex_intro with src_ref; auto.
    (* break apart HeqP and HeqPcap *)
    destruct_tuple HeqP HeqSrc HeqLbl HeqType HeqSched;
    simpl in HeqSrc; simpl in HeqLbl; simpl in HeqType; simpl in HeqSched.
    destruct_tuple HeqPcap HCap1 HCap2 HCap3 HCap4;
    simpl in HCap1; simpl in HCap2; simpl in HCap3; simpl in HCap4.
    (* find src_tuple *)
    generalize (Sys_MapEquiv.exists_mapsTo_eq _ _ (Sys.eq_sym HeqS) _ _ HmapS _ (Ref.eq_refl src_ref)); intros Hex_src_ref;
      destruct Hex_src_ref as [tuple' Hex_src_ref]; destruct_tuple tuple' src'' lbl'' type'' sched'';
        simpl in Hex_src_ref.
    destruct Hex_src_ref as [Hex_src_ref HmapstoS];
      destruct_tuple Hex_src_ref HeqSrc'' HeqLbl'' HeqType'' HeqSched''.
    apply Sys.MapS.find_1 in HmapstoS; fold Sys.P.t in HmapstoS.
    (* continue *)
    split; auto.
    (*  SC.is_alive src_ref s *)
    unfold SC.is_alive.
    unfold SC.is_label.
    unfold SC.getLabel.
    unfold SC.getObjTuple.
    unfold Sys.P.t in *.
    rewrite HmapstoS; simpl.
    rewrite <- HeqLbl''. 
    rewrite HeqLbl; apply ObjectLabel.eq_sym; auto.
    (* continue *)
    apply ex_intro with src''; auto; split; auto.
    (* SC.getObj src_ref s = Some src'' *)
    unfold SC.getObj; unfold SC.getObjTuple.
    unfold Sys.P.t in *.
    rewrite HmapstoS; auto.
    (* continue *)
    apply ex_intro with ind.
    (* find cap *)
    assert (Obj.eq src' src'') as HeqSrc''2; [apply Obj.eq_trans with (m2:=src); auto; apply Obj.eq_sym; auto|].
    generalize (Obj_MapEquiv.exists_mapsTo_eq _ _ HeqSrc''2 _ _ Hmap0 _ (Ind.eq_refl ind));
      intros Hex_cap''; destruct Hex_cap'' as [cap'' Hex_cap'']; destruct Hex_cap'' as [Heq_cap'' HmapCap''].
    (* continue *)
    apply ex_intro with cap''; auto; split; auto.
    (* find target tuple *)
    generalize (Cap.target_eq _ _ Heq_cap''); intros HeqTargets.
    
    generalize (Sys_MapEquiv.exists_mapsTo_eq _ _ (Sys.eq_sym HeqS) _ _ HmapScap _ HeqTargets); intros Hex_src_ref;
      destruct Hex_src_ref as [tuple' Hex_src_ref]; 
        destruct_tuple tuple' cap_src'' cap_lbl'' cap_type'' cap_sched'';
        simpl in Hex_src_ref.
    destruct Hex_src_ref as [Hex_src_ref HmapstoScap];
      destruct_tuple Hex_src_ref HeqCapSrc'' HeqCapLbl'' HeqCapType'' HeqCapSched''.
    apply Sys.MapS.find_1 in HmapstoScap; fold Sys.P.t in HmapstoScap.
    (* continue *)
    split; auto.
    (* SC.is_alive (Cap.target cap'') s *)
    unfold SC.is_alive; unfold SC.is_label; unfold SC.getLabel; unfold SC.getObjTuple.
    unfold Sys.P.t in *.
    rewrite HmapstoScap; simpl.
    rewrite <- HeqCapLbl''; rewrite HCap2; apply ObjectLabel.eq_sym; auto.
    (* continue *)
    apply ex_intro with rgt; auto; split; auto.
    (* In rgt (Cap.rights cap'') *)
    generalize(Cap.rights_eq _ _ Heq_cap''); intros Hrights1.
    unfold ARSet.eq in Hrights1.
    eapply Hrights1; auto.
    (* continue *)
    destructEdgeEq HeqEdge edge HeqEdgeS HeqEdgeT HeqEdgeRef.
    rewrite <- (Edges.edge_rewrite edge).
    apply Edges.edge_equal; auto.
    eapply Ref.eq_trans; [apply Ref.eq_sym; apply HeqTargets|auto].

  (* woot, easier case *)
  apply Hda_1 in H. clear Hda_1 Hda_2.
  destruct H; [eapply AG.empty_1 in H; contradiction|].
  destruct_outer H H1 H2 H3 H4 H5.
  (* instantiate find src_ref *)
  case (option_sumbool (SC.getObjTuple src_ref s)); intros Hfind_src_ref; 
    [|destruct Hfind_src_ref as [tuple Hfind_src_ref]];
    [unfold SC.getObj in H1; rewrite Hfind_src_ref in H1; simpl in H1; discriminate|].
  (* destruct tuple and eliminate src_obj' *)
  destruct_tuple tuple src_obj' src_lbl src_type src_sched.
  unfold SC.getObj in H1; rewrite Hfind_src_ref in H1; simpl in H1;
    injection H1 as Hsrc_obj_eq; rewrite Hsrc_obj_eq in *; clear Hsrc_obj_eq H1.
  (* instantiate find (Cap.target cap) *)
  case (option_sumbool (SC.getObjTuple (Cap.target cap) s)); intros Hfind_target; 
    [unfold SC.is_alive in H3; unfold SC.is_label in H3; unfold SC.getLabel in H3; 
      rewrite Hfind_target in H3; simpl in H3; contradiction
      |destruct Hfind_target as [tuple Hfind_target]].
  (* destruct tuple *)
  destruct_tuple tuple cap_obj cap_lbl cap_type cap_sched.
  (* convert is_alive *)
  unfold SC.is_alive in *; unfold SC.is_label in *; unfold SC.getLabel in *.
  rewrite Hfind_src_ref in *; rewrite Hfind_target in *; simpl in *.
  (* convert to MapsTo *)
  unfold SC.getObjTuple in Hfind_src_ref; apply Sys.MapS.find_2 in Hfind_src_ref.
  unfold SC.getObjTuple in Hfind_target; apply Sys.MapS.find_2 in Hfind_target.

  (* instantiate *)
  apply_ex_intro_dirAcc s s src_ref src_obj src_lbl src_type src_sched src_obj src_lbl src_type src_sched 
  ind cap cap_obj cap_lbl cap_type cap_sched cap_obj cap_lbl cap_type cap_sched rgt; 
  try apply Sys.eq_refl; try apply Sys.P.eq_refl; try apply ObjectLabel.eq_sym; auto.
  Qed.

  Theorem exists_dirAcc_spec: forall s, exists a, dirAcc_spec s a.
  Proof.
    intros.
    apply ex_intro with (dirAcc s).
    apply dirAcc_spec_dirAcc.
  Qed.


(* Section relating dirAcc_spec as proper over iff *)


 (* I will probably need more proofs about these properties, but am not yet sure what *)

  Theorem dirAcc_spec_if : forall s s' ag ag',
    Sys.eq s s' -> 
    AG.eq ag ag' ->
    dirAcc_spec s ag ->
    dirAcc_spec s' ag'.
  Proof.
    intros.
    (* turn AG.eq into AG.Equal *)
    apply ag_eq_Equal in H0.
    unfold AG.Equal in H0.
    intros edge; split; intros Hdiracc.

    destruct_dirAcc Hdiracc s'' HeqS src_ref src lbl type sched HmapS src' lbl' type' sched' 
    HeqP HeqL ind cap Hmap0 cap_obj cap_lbl cap_type cap_sched HmapScap
    cap_obj' cap_lbl' cap_type' cap_sched' HeqPcap HaliveCap rgt HinR HeqEdge.

    apply (H0 edge).
    eapply H1. 
    apply_ex_intro_dirAcc s'' s' src_ref src lbl type sched src' lbl' type' sched'
    ind cap cap_obj cap_lbl cap_type cap_sched cap_obj' cap_lbl' cap_type' cap_sched' rgt.
    
    apply (H0 edge) in Hdiracc.
    eapply H1 in Hdiracc.
    destruct_dirAcc Hdiracc s'' HeqS src_ref src lbl type sched HmapS src' lbl' type' sched' 
    HeqP HeqL ind cap Hmap0 cap_obj cap_lbl cap_type cap_sched HmapScap
    cap_obj' cap_lbl' cap_type' cap_sched' HeqPcap HaliveCap rgt HinR HeqEdge.
    apply_ex_intro_dirAcc s'' s src_ref src lbl type sched src' lbl' type' sched'
    ind cap cap_obj cap_lbl cap_type cap_sched cap_obj' cap_lbl' cap_type' cap_sched' rgt.
  Qed.

  Theorem dirAcc_spec_iff : forall s s' ag ag',
    Sys.eq s s' -> 
    AG.eq ag ag' ->
    (dirAcc_spec s ag <-> dirAcc_spec s' ag').
  Proof.
    intros.
    split; intros; eapply dirAcc_spec_if; 
      [apply H | apply H0 | auto | 
        apply Sys.eq_sym in H; apply H | apply AG.eq_sym in H0 ; apply H0 | auto ].
  Qed.

  Implicit Arguments dirAcc_spec_iff [s s' ag ag'].

    Theorem dirAcc_spec_dec: forall s ag,
      {dirAcc_spec s ag} + {~ dirAcc_spec s ag}.
    Proof.
      intros.
      generalize (dirAcc_spec_dirAcc s); intros.
      case (AG.eq_dec ag (dirAcc s)); intros Hc.
      
      left.
      eapply dirAcc_spec_iff; try apply Sys.eq_refl; try apply Hc; auto.
      
      right.
      intro.
      apply Hc.
      eapply dirAcc_spec_eq; try apply Sys.eq_refl; try apply H0; try auto.
    Qed.

End MakeDirectAccess.