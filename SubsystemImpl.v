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
(* Require Import Mutability. *)
Require Import OptionMap2.


Require Import Morphisms.
Require Import Basics.
Require Import Sumbool_dec.
Require Import RefSets.

Require Import CapSets.

(* type_remove *)
Require Import Subsystem.


Module MakeSubsystem (Ref:ReferenceType) (RefS: RefSetType Ref)(Edges: AccessEdgeType Ref) (AccessGraph:AccessGraphType Ref Edges) (Seq:SeqAccType Ref RefS Edges AccessGraph) (Cap:CapabilityType Ref) (CapS: CapSetType Ref Cap) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) (SemDefns: SemanticsDefinitionsType Ref Cap Ind Obj Sys) (Sem: SemanticsType Ref RefS Cap Ind Obj Sys SemDefns) (Exe: ExecutionType Ref RefS Cap Ind Obj Sys SemDefns Sem) : SubsystemType Ref RefS Edges AccessGraph Seq Cap CapS Ind Obj Sys SemDefns Sem Exe .

  Import Exe.SemConv.
  Import RefS.
  Import CapS.
  Import AccessGraph.



(* This module deals with various notions of subsystems and how they are built.
   A subsystem is simply any collection of objects.  We have simply been using set notation 
   to capture this concept.

   The goal of this library is to capture the other three notions of a subsystem: 
   an extant subsystem, an constructive subsystem, and a confined subsystem.

   E is a fresh subsystem in state S only when all capabilities targeting elements of E
   are also held by members of E.
   E is confined in state S over authorized capabilities C only when it is fresh and for
   each capability Cap held in E:
      1. Cap is in C
      2. Cap targets an element of E
      3. Cap conveys no authority
      4. The rights of Cap are the singleton wk, and the target of Cap is not in E.

   These 3 properties:
      * are deicdable
      * are equivalence preserving
      * may be produced using operations in the system.

   We then define a notion of an extant, constructive subsystem construction as a function.
   We further constrain such a function to produce confined subsystems.
   This demonstrates that the non-recursive confinement test is checkable.

   *)


  Definition extant_test S e := SC.is_alive e S \/ SC.is_dead e S.

  Theorem extant_test_dec : forall S e, {extant_test S e} + { ~ extant_test S e}.
  Proof.
    intros S e.
    unfold extant_test.
    Sumbool_decide; eauto; eapply SC.is_label_dec. 
  Qed.
  Hint Resolve extant_test_dec.

  Theorem Proper_extant_test : Proper (Sys.eq ==> Ref.eq ==> iff) extant_test.
  Proof.
    unfold extant_test; unfold Proper; unfold respectful; intros.
    split; intros; [rewrite <- H0| rewrite H0];
      (destruct H1 as [H1 | H1];
        eapply SC.isLabel_eq in H1;
          try apply ObjectLabel.eq_refl;
            try (apply Ref.eq_refl); eauto).
  Qed.

  Require Import SetoidList.

  Theorem compat_P_extant_test: forall S, compat_P Ref.eq (extant_test S).
  Proof.
    unfold compat_P; unfold Proper; unfold respectful; unfold impl; intros; eapply Proper_extant_test;
    rewrite H in *;  eauto;
    solve[ apply Sys.eq_refl | apply Ref.eq_refl].
  Qed.

  Definition extant_subsystem E S := RefSet.For_all (extant_test S) E.

  Theorem extant_subsystem_dec : forall E S, {extant_subsystem E S} + {~ extant_subsystem E S}.
  Proof.
    intros.
    unfold extant_subsystem.
    generalize (RefSetDep.for_all (extant_test_dec S) E); intros [H | H]; [left|right];
      (apply H; apply compat_P_extant_test).
  Qed.

  (* This test is succinct, but uses infinte quantifies.
     In truth, these quantifiers are only meaningful over elements S.
     We will use constructive_test' as a decidable finite case, and demonstrate that it is equivalent.
     *)
     
  Definition constructive_test E S e := forall o, ~ RefSet.In o E -> SC.is_alive o S ->
    forall i, option_map1 (fun cap => ~ Ref.eq e (Cap.target cap)) True (SC.getCap i o S).

  (* This form is less readable, but is decidable because its negation is decidable
     Because S is finite, we may enumerate all triples (o i cap) in S.
     For each of these, we can test if o is in E and if e [=] (Cap.target cap).
     *)
  
  Definition constructive_test' E S e := 
    ~ exists o, exists i, exists cap,
      SC.getCap i o S = Some cap /\ 
      SC.is_alive o S /\
      ~ RefSet.In o E /\ 
      Ref.eq e (Cap.target cap).


  Theorem constructive_test_iff' : forall E S e,
    constructive_test E S e <-> constructive_test' E S e.
  Proof.
    unfold constructive_test; unfold constructive_test'; split; intros.
    (* constructive -> constructive' *)
    intros [o [i [cap [Hcap [Halive [Hin Heq]]]]]].
    generalize (H o Hin Halive i); clear H; intros H.
    rewrite Hcap in *; simpl in *.
    contradiction.
    (* constructive' -> constructive *)
    case (option_sumbool (SC.getCap i o S)); intros Hcap; [|destruct Hcap as [obj Hcap]];
      rewrite Hcap in *; simpl in *; 
        try solve [ auto | intro Hnot; apply H; do 3 eapply ex_intro; eauto].
  Qed.


  (* TODO: Move these backward *)

  Theorem OCgetCap_dec : forall obj i, 
    {exists cap, OC.getCap i obj = Some cap} + {~exists cap, OC.getCap i obj = Some cap}.
  Proof.
    intros.
    case (option_sumbool (OC.getCap i obj)); intros Hcap; [right| left; destruct Hcap as [cap Hcap]];
      rewrite Hcap in *; simpl in *; eauto ; solve [eapply not_exists_iff; intros; discriminate].
  Qed.
  
  Hint Resolve OCgetCap_dec.

  Theorem SCgetCap_dec : forall s o i,
    {exists cap, SC.getCap i o s = Some cap} + {~exists cap, SC.getCap i o s = Some cap}.
  Proof.
    intros.
    case (option_sumbool (SC.getCap i o s)); intros Hcap; [right| left; destruct Hcap as [cap Hcap]];
      rewrite Hcap in *; simpl in *; eauto ; solve [eapply not_exists_iff; intros; discriminate].
  Qed.

  Hint Resolve SCgetCap_dec.

  (* TODO: Generalize and move to OrdFMapEquiv *)
    (* Theorem Proper_Exists: *)
    (*   Proper ((Ind.eq ==> Cap.eq ==> impl) ==> Obj.eq ==> impl) (fun P m => OC.Obj_Exists.Exists P m). *)
    (* Proof. *)
    (*   intros. *)
    (*   unfold Proper; unfold respectful; unfold impl; unfold OC.Obj_Exists.Exists. *)
    (*   intros P P' Hproper x y Heq [i [cap [Hmap Pcap]]]. *)
    (*   apply ex_intro with i. *)
    (*   generalize (OC.Obj_MapEquiv.exists_mapsTo_eq _ _ Heq _ _ Hmap _ (Ind.eq_refl i));  *)
    (*     intros [cap' [Hcap'eq Hcap'Map]]. *)
    (*   eapply ex_intro. *)
    (*   split; [apply Hcap'Map|]. *)
    (*   eapply Hproper; eauto. *)
    (* Qed. *)



  (* This is a little stronger than necessary.
     We are required to have P be compat_P over Ind.eq and Cap.eq as this decidability lifts
     as part of the embedding through the system state.
     We choose to lift the entire morphism for simplicity.
     *)


  Theorem constructive_test'_dec: forall E S e, {constructive_test' E S e} + {~ constructive_test' E S e}.
  Proof.
    intros; unfold constructive_test'.
    Sumbool_decide; auto.
    eapply SC.exists_getCap_dec.
    (* Pdec *)
    intros; Sumbool_decide; eauto; try apply RefSetProps.In_dec; try apply Ref.eq_dec.
    (* Proper P *)
    unfold Proper; unfold respectful; unfold impl; intros.
    destruct H2 as [H2 [H3 H4]].
    split.
    rewrite <- H. auto.
    split.
    intro Hnot; eapply H3; rewrite H; auto.
    rewrite <- (Cap.target_eq _ _ H1); auto.
    (* The existentials are coming from Sumbool_decide's theorems having been misquantified. 
       The new section should work correctly now.*)
  Qed.
    

  Theorem Proper_constructive_test : Proper (RefSet.Subset ==> Sys.eq ==> Ref.eq ==> impl) constructive_test.
  Proof.
    unfold Proper; unfold respectful; unfold impl; unfold flip; unfold constructive_test;intros.
    generalize (H o); intros Ho.
    case (RefSetProps.In_dec o x); intros Hcase; [apply Ho in Hcase; contradiction| clear Ho].
    eapply SC.isAlive_eq in H4; [ | apply Ref.eq_refl | apply Sys.eq_sym; apply H0].
    generalize (H2 o Hcase H4 i); clear H2; intros H2.
    generalize (SC.getCap_eq _ _ _ _ _ _ H0 (Ind.eq_refl i) (Ref.eq_refl o)); intros Heq.
    case (option_sumbool (SC.getCap i o x0)); intros HCaseX0; [|destruct HCaseX0 as [X0 HCaseX0]];
      (case (option_sumbool (SC.getCap i o y0)); intros HCaseY0; [|destruct HCaseY0 as [Y0 HCaseY0]]);
        rewrite HCaseX0 in *; rewrite HCaseY0 in *;
          simpl in *; eauto.
    intro Hnot; apply H2; rewrite H1; rewrite (Cap.target_eq _ _ Heq); eauto.
  Qed.


  Theorem compat_P_constructive_test: forall E S, SetoidList.compat_P Ref.eq (constructive_test E S).
  Proof.
    unfold SetoidList.compat_P; unfold Proper; unfold respectful; unfold impl; intros.
    eapply Proper_constructive_test; eauto.
    apply RefSetProps.subset_equal; apply RefSet.eq_refl.
    apply Sys.eq_refl.
  Qed.

  Theorem constructive_test_dec : forall E S e, {constructive_test E S e} + {~ constructive_test E S e}.
  Proof.
    intros E S e.
    case (constructive_test'_dec E S e); intros Hcase; [left|right]; 
      (rewrite constructive_test_iff'; eauto).
  Qed.
  Hint Resolve constructive_test_dec.


  Definition constructive_subsystem E S := RefSet.For_all (fun e => extant_test S e /\ constructive_test E S e) E.

  Theorem constructive_subsystem_dec : forall E S, {constructive_subsystem E S} + {~ constructive_subsystem E S}.
  Proof.
    intros E S.
    unfold constructive_subsystem.
    assert (let f := (fun e => extant_test S e /\ constructive_test E S e) in 
      (forall e, {f e} + {~f e})) as Hdec by ( intros; unfold f; clear f; Sumbool_decide; eauto).
    generalize (RefSetDep.for_all Hdec E); intros [H | H]; [left|right];
    (apply H;
      unfold compat_P; unfold Proper; unfold respectful; unfold impl; intros;
        destruct H1; rewrite H0 in *; split; [eapply Proper_extant_test | eapply Proper_constructive_test];
          solve [apply Ref.eq_refl | apply Sys.eq_refl| apply RefSetProps.subset_refl | auto]).
  Qed.
    
  Implicit Arguments constructive_subsystem_dec [E S].

  Definition authorized_set C E := 
    RefSet.For_all (fun e => ~ CapSet.Exists (fun cap => Ref.eq (Cap.target cap) e) C) E.

  Definition confinement_pred C S E (cap:Cap.t) :=
    CapSet.In cap C \/
    RefSet.In (Cap.target cap) E \/
    ARSet.Empty (Cap.rights cap) \/
    ~ SC.is_alive (Cap.target cap) S \/
    (ARSet.eq (Cap.rights cap) (ARSet.singleton wk) /\ ~ RefSet.In (Cap.target cap) E).
    

  Require Import Sumbool.

    (* TODO: generalize and place in a set library *)
    Theorem Empty_dec : forall s, {ARSet.Empty s} + {~ ARSet.Empty s}.
    Proof.
      intros s.
      case (sumbool_of_bool (ARSet.is_empty s)); intros Hcase; [left|right];
      rewrite ARSetFacts.is_empty_iff; eauto. 
      rewrite Hcase; discriminate.
    Qed.

  Theorem confinement_pred_dec : forall C E S cap, {confinement_pred C S E cap} + {~ confinement_pred C S E cap}.
  Proof.
    intros.
    unfold confinement_pred.
    Sumbool_decide.
    apply CapSetProps.In_dec.
    apply RefSetProps.In_dec.
    eapply Empty_dec.
    eapply SC.is_alive_dec.
    eapply ARSet.eq_dec.
    eapply RefSetProps.In_dec.
  Qed.

  Theorem Proper_confinement_pred: 
    Proper (CapSet.Subset ==> Sys.eq ==> RefSet.eq ==> Cap.eq ==> impl) confinement_pred.
  Proof.
    unfold Proper; unfold respectful; unfold confinement_pred; unfold impl; intros.

    destruct H3 as [H3 | H3]; [left|right].
    eapply H; rewrite <- H2; auto.
    
    destruct H3 as [H3 | H3]; [left|right].
    rewrite <- (Cap.target_eq _ _ H2); eapply H1; auto.

    destruct H3 as [H3 | H3]; [left|right].
    rewrite <- (Cap.rights_eq _ _ H2); eauto.

    destruct H3 as [H3 | H3]; [left|right].
    rewrite <- (Cap.target_eq _ _ H2).
    intros Hnot; apply H3.
    eapply SC.isLabel_eq; eauto; try apply eq_refl.

    destruct H3 as [H3 H3']; split.
    rewrite <- (Cap.rights_eq _ _ H2); eauto.
    rewrite <- (Cap.target_eq _ _ H2); rewrite <- H1; eauto.
  Qed.

  Definition confinement_test C S E e:=
    forall i, option_map1 (confinement_pred C S E) True (SC.getCap i e S).

  Definition confinement_test' C S E e :=
    ~ exists o, exists i, exists cap, 
      SC.getCap i o S = Some cap /\
      Ref.eq o e /\
      ~ confinement_pred C S E cap.

  Theorem confinement_test_iff' : forall C S E e, confinement_test C S E e <-> confinement_test' C S E e.
  Proof.
    unfold confinement_test; unfold confinement_test'.
    split; intros.

    intros [o [i [cap [HgetCap [Heq Hpred]]]]].
    generalize (H i); clear H; intros H.
    rewrite Heq in *.
    rewrite HgetCap in *; simpl in *; auto.

    rewrite not_exists_iff in H; simpl in H.
    generalize (H e); clear H; intros H.
    rewrite not_exists_iff in H; simpl in H.
    generalize (H i); clear H; intros H.
    rewrite not_exists_iff in H; simpl in H.
    
    case (option_sumbool (SC.getCap i e S)); intros Hcase; [|destruct Hcase as [cap Hcase]];
      rewrite Hcase in *; simpl in *; auto.
    generalize (H cap); clear H; intros H.
    eapply Sumbool_not_and in H;
      try solve [Sumbool_decide; eauto; solve [apply Ref.eq_dec |apply confinement_pred_dec]].
    destruct H; [tauto|].
    rewrite Sumbool_not_and in H; 
      try solve [Sumbool_decide; eauto; solve [apply Ref.eq_dec |apply confinement_pred_dec]].
    destruct H; [contradict H; apply Ref.eq_refl|].
    eapply Sumbool_dec_not_not_iff in H;
      try solve [Sumbool_decide; eauto; solve [apply Ref.eq_dec |apply confinement_pred_dec]].
  Qed.

  Implicit Arguments confinement_test_iff' [C S E e].

  Theorem confinement_test'_dec : forall C S E e, {confinement_test' C S E e} + {~ confinement_test' C S E e}.
  Proof.
    intros C S E e.
    unfold confinement_test'.
    Sumbool_decide.
    case (SC.exists_getCap_dec S (fun ref ind cap => Ref.eq ref e/\ (~ confinement_pred C S E cap))).
    
    intros;
    Sumbool_decide; solve [eapply confinement_pred_dec | eapply Ref.eq_dec].

    unfold Proper; unfold respectful; unfold impl; intros.
    destruct H2 as [H2 H3]; split; [ rewrite H in *; eauto |].
    intro Hnot; apply H3.
    eapply Proper_confinement_pred.
    eapply CapSetProps.subset_refl.
    eapply Sys.eq_refl.
    eapply RefSet.eq_refl.
    apply Cap.eq_sym; apply H1.
    auto.

    intros; left; eauto.

    intros; right; eauto.
  Qed.


  Theorem confinement_test_dec : forall C S E e,
    {confinement_test C S E e} + { ~ confinement_test C S E e}.
  Proof.
    intros.
    case (confinement_test'_dec C S E e); intros Hcase; [left|right];
      rewrite confinement_test_iff'; eauto.
  Qed.
  Hint Resolve confinement_test_dec.

  Theorem Proper_confinement_test : 
    Proper (CapSet.Subset ==> Sys.eq ==> RefSet.eq ==> Ref.eq ==> impl) confinement_test.
  Proof.
    unfold Proper; unfold respectful; unfold impl; unfold flip; unfold confinement_test;intros.
    generalize (H3 i); intros Hi; clear H3.
    generalize (SC.getCap_eq _ _ _ _ _ _ H0 (Ind.eq_refl i) H2); intros Heq.
    case (option_sumbool (SC.getCap i x2 x0)); intros HCaseX0; [|destruct HCaseX0 as [X0 HCaseX0]];
      (case (option_sumbool (SC.getCap i y2 y0)); intros HCaseY0; [|destruct HCaseY0 as [Y0 HCaseY0]]);
        rewrite HCaseX0 in *; rewrite HCaseY0 in *;
          simpl in *; eauto; try contradiction.
    eapply Proper_confinement_pred; eauto.
  Qed.

  Definition confined_subsystem C E S :=
    RefSet.For_all (fun e => extant_test S e /\ constructive_test E S e /\ confinement_test C S E e) E.

  Theorem confined_subsystem_dec : forall C E S, {confined_subsystem C E S} + {~ confined_subsystem C E S}.
  Proof.
    intros C E S; unfold confined_subsystem.
    assert (let f := (fun e => extant_test S e /\ constructive_test E S e /\ confinement_test C S E e) in 
      (forall e, {f e} + {~f e})) as Hdec by ( intros; unfold f; clear f; Sumbool_decide; eauto).
    generalize (RefSetDep.for_all Hdec E); intros [H | H]; [left|right];
    (apply H;
      unfold compat_P; unfold Proper; unfold respectful; unfold impl; intros;
        destruct H1 as [H1 [H2 H3]]; rewrite H0 in *; 
          split; [eapply Proper_extant_test | 
            split; [eapply Proper_constructive_test | eapply Proper_confinement_test] ];
    
          try solve [apply Ref.eq_refl | apply Sys.eq_refl| apply RefSetProps.subset_refl |
            apply RefSet.eq_refl| apply CapSetProps.subset_refl| auto]).
  Qed.

  Implicit Arguments confined_subsystem_dec [C E S].

  Definition authorized_confined_subsystem C E S :=
    authorized_set C E /\ confined_subsystem C E S.

(* To Define:
   * Subsystem Constrution notion as a function?
   *)

End MakeSubsystem.
