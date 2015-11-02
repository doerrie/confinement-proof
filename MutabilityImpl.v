Require Import Sumbool.
Require Import OptionSumbool.
Require Import Morphisms.
Require Import AccessRights.
Require Import References.
Require Import RefSets.
Require Import Basics.
Require Import OptionMap2.
Require Import RelationClasses.
Require Import Iff_Equiv.
Require Import Morphisms_Prop.
Require Import AccessEdge.
Require Import AccessGraphs.
Require Import SequentialAccess.

(* type_remove *)
Require Import Mutability.

(* I'm guessing that all of this really relies on Sequential Access and could be reduced. *)

Module MakeMutability (Ref:ReferenceType) (RefS: RefSetType Ref) (Edges: AccessEdgeType Ref) (AccessGraph:AccessGraphType Ref Edges) (Seq:SeqAccType Ref RefS Edges AccessGraph) : MutabilityType Ref RefS Edges AccessGraph Seq.

(*  Module AE := MakeAccessExecution Ref Cap Ind Obj Sys SemDefns Sem Exe Edges AccessGraph Seq.
  Import AE.
  Export AE. *)

  Import Seq.
  Import RefS.
  Import AccessGraph.
(*  Import Seq.RefSet_Mod. *)

  Definition mutable_spec p objs mut := forall x, RefSet.In x mut <->
    RefSet.In x objs \/
    (exists e, RefSet.In e objs /\
      (AG.In (Edges.mkEdge e x tx) p \/ 
        AG.In (Edges.mkEdge e x wr) p \/ 
        AG.In (Edges.mkEdge x e wk) p \/
        AG.In (Edges.mkEdge x e rd) p)).

  Definition add_if_in x y s s' := if RefSet.mem y s then RefSet.add x s' else s'.

  Definition mutable_fold objs edge objs':=
    match (Edges.right edge) with
      | rd => add_if_in (Edges.source edge) (Edges.target edge) objs objs'
      | wk => add_if_in (Edges.source edge) (Edges.target edge) objs objs'
      | wr => add_if_in (Edges.target edge) (Edges.source edge) objs objs'
      | tx => add_if_in (Edges.target edge) (Edges.source edge) objs objs'
    end.

  Definition mutable p objs := 
    AG.fold (mutable_fold objs) p objs.

    Ltac solveInXN' H1 :=
      eapply H1; left; auto.
    Ltac solveAddCase Hadd Hr Hin Hs Ht := 
      eapply AGFacts.add_iff in Hadd; simpl in Hadd; destruct Hadd as [Hadd | Hadd];
        [ eapply Edges.eq_equal in Hadd; rewrite Hadd in *;
            rewrite Edges.right_rewrite in *; 
              rewrite Edges.target_rewrite in *;
                rewrite Edges.source_rewrite in *;
                  rewrite Ht in *; rewrite Hs in *;
                  solve [discriminate
                    | try left; auto 
                    | apply RefSetFacts.mem_iff in Hin; rewrite Hin in *; discriminate
                  ]
          | solve [do 2 try right; eapply ex_intro; split; [apply Hin|intuition auto]]
        ].
    Ltac solveBasicEqCase Hcase edge Heq Hs Ht Hr := 
    eapply RefSetFacts.mem_iff in Hcase; right;
      eapply ex_intro; split; 
        [ eapply Hcase 
          | rewrite <- (Edges.edge_rewrite edge);
            rewrite Ht; rewrite Hs; rewrite Hr; rewrite Heq;
              intuition ( eapply AGFacts.add_iff; simpl; intuition auto)].
    Ltac solveBasicInCase H1 x Hin2:= 
      let H1' := fresh "H1'" in
        let e := fresh "e" in
          let H1'2 := fresh "H1'2" in
            destruct (H1 x) as [H1' _];
              apply H1' in Hin2; clear H1'; 
                destruct Hin2 as [Hin2 | [e [H1' H1'2]]]; 
                  [left; auto
                    | right; eapply ex_intro; split; [eapply H1'|];
                      repeat progress (destruct H1'2 as [H1'2|H1'2]; [left|right]; 
                        try solve [eapply AGFacts.add_iff; right; auto])].
    Ltac solvePerRightCase edge Hs Ht Hr H1 x n r:=
      let Hcase := fresh "Hcase" in 
        (* r case *)
        case (sumbool_of_bool (RefSet.mem r n)); intros Hcase;
          rewrite Hcase in *; simpl in *;
            [ (* r case, target is n *)
              eapply iff_trans; [eapply RefSetFacts.add_iff|];
                split;
                  [ (* eq \/ In -> add *)
                    let Heq := fresh "Heq" in
                      let Hin2 := fresh "Hin2" in
                        intros [Heq | Hin2]; 
                          [ (* eq *)
                            solveBasicEqCase Hcase edge Heq Hs Ht Hr
                            | (* basic in *)
                              solveBasicInCase H1 x Hin2
                          ]
                    | (* add -> In *)
                      let e:= fresh "e" in 
                        let Hin := fresh "Hin" in 
                          let Hadd := fresh "Hadd" in
                            intros [Hin | [e [Hin Hadd]]]; [right; solveInXN' H1|];
                              eapply or_impl_morphism; unfold impl; 
                                [ let z := fresh "z" in intro z; apply z | eapply H1| ];
                                do 3 (destruct Hadd as [Hadd | Hadd]; [solveAddCase Hadd Hr Hin Hs Ht|]); 
                                  solveAddCase Hadd Hr Hin Hs Ht
                  ]
              | (* r case, target ~ in n *)
                split;
                  [ (* basic in *)
                    intros Hin2; solveBasicInCase H1 x Hin2
                    | (* add -> In *)
                      intros [Hin | [e [Hin Hadd]]]; [solveInXN' H1|]; eapply H1;
                        do 3 (destruct Hadd as [Hadd | Hadd]; [solveAddCase Hadd Hr Hin Hs Ht|]);
                          solveAddCase Hadd Hr Hin Hs Ht
                  ]
            ].


  Theorem mutable_spec_mutable: forall p n, mutable_spec p n (mutable p n).
  Proof.
    unfold mutable_spec; unfold mutable. intros p n.
    eapply AGProps.fold_rec_bis with (f:= (mutable_fold n)); intros.
    (* compat *)
    eapply iff_trans; [apply H0| clear H0].
    eapply or_iff_compat_l.
    split; intros [e He]; apply ex_intro with e;
      destruct He as [He He']; 
        (split; 
          [ apply He 
            | do 3 (destruct He' as [He' | He']; [left|right]; (try solve [apply H; apply He'])) 
          ]
        ).
    (* base *)
    split; intros H; [left; auto
      | destruct H as [H | [e [_ H]]]; [auto|]].
    destruct H as [H | [H | [H | H]]]; eapply AGFacts.empty_iff in H; contradiction.
    (* step *)


    rename a into n'.
    rename x into edge.
    rename x0 into x.
    unfold mutable_fold in *.
    assert (exists r, Edges.right edge = r); [eapply ex_intro; apply eq_refl|destruct H2 as [r Hr]].
    assert (exists t, Edges.target edge = t) as [t Ht]; [eapply ex_intro; apply eq_refl|].
    assert (exists s, Edges.source edge = s) as [s Hs]; [eapply ex_intro; apply eq_refl|].
    rewrite Hs in *; rewrite Ht in *.
    rewrite Hr in *; destruct r; unfold add_if_in;
      solve [solvePerRightCase edge Hs Ht Hr H1 x n t| solvePerRightCase edge Hs Ht Hr H1 x n s].
  Qed.

  Hint Resolve mutable_spec_mutable.


  Theorem mutable_spec_subset: 
    forall n n', RefSet.Subset n' n -> forall p p',  AG.Subset p' p -> 
      forall m, mutable_spec p n m -> forall m', mutable_spec p' n' m' ->
        RefSet.Subset m' m.
  Proof.
    intros.
    unfold mutable_spec in *.
    intros e He.
    eapply H1; clear H1.
    eapply H2 in He; clear H2. 
    destruct He as [Hin | [e' [Hin Hcases]]];
      [ left; auto
        | right; apply ex_intro with e'; intuition auto
      ].
  Qed.

  Hint Resolve mutable_spec_subset.

  Theorem Proper_mutable: Proper (AG.Subset ==> RefSet.Subset ==> RefSet.Subset) mutable.
  Proof.
    unfold Proper; unfold respectful; unfold flip; intros; eauto.
  Qed.


  Theorem Proper_mutable_spec: Proper (AG.eq ==> RefSet.eq ==> RefSet.eq ==> impl) mutable_spec.
  Proof.
    unfold Proper; unfold respectful; unfold impl.
    intros ag ag' Hag r1 r1' Hr1 r2 r2' Hr2 Hm.
    unfold mutable_spec in *; intros elem.
    eapply iff_trans. eapply RefSet.eq_sym; apply Hr2.
    eapply iff_trans. apply Hm.
    split; intros H;
      (destruct H as [Hin | [e' [Hin Hcases]]];
        [ left; eapply Hr1; auto
          | right; apply ex_intro with e';
            split; [apply Hr1; auto|intuition (eapply Hag; eauto)]
        ]).
  Qed.


  (* This may come in useful *)

  (* This is intended to be used when AG_attenuating n p p' and n' [<=] n.  
     This ocurrs on potAcc approximating sequences *)
  Theorem mutable_spec_inter :
    forall p n m, mutable_spec p n m ->
      forall p' m', mutable_spec p' n m' ->
        forall n', RefSet.Subset n' n ->
          RefSet.Subset (RefSet.inter m' n') m.
  Proof.
    intros p n m Hm p' m' Hm' n' HSubN e He.
    eapply RefSetFacts.inter_iff in He.
    destruct He as [HeM' HeN'].
    generalize (HSubN _ HeN'); intros HeN.
    eapply Hm; clear Hm; eapply Hm' in HeM'; clear Hm'.
    left; auto.
  Qed.

  Theorem mutable_spec_eq_mutable :
    forall i z m, mutable_spec i z m -> RefSet.eq m (mutable i z).
  Proof.
    intros.
    intro x. 
    generalize (mutable_spec_mutable i z x); intros.
    unfold mutable_spec in *.
    eapply iff_trans; [eapply H|clear H].
    eapply iff_sym.
    eapply H0.
  Qed.
  
  
  Theorem mutable_spec_eq_iff :
    forall i z m, mutable_spec i z m ->
      forall i', AG.eq i i' -> forall z', RefSet.eq z z' ->
        forall m', mutable_spec i' z' m' -> RefSet.eq m m'.
  Proof.
    intros.
    eapply Proper_mutable_spec in H2;
      [ clear H0 H1 i' z'
        | apply AG.eq_sym; apply H0
        | apply RefSet.eq_sym; apply H1
        | apply RefSet.eq_refl
      ].
    rewrite mutable_spec_eq_mutable; eauto.
    rewrite (mutable_spec_eq_mutable i z m'); eauto.
    apply RefSet.eq_refl.
  Qed.


End MakeMutability.