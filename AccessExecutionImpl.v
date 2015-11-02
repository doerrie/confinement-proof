Require Import OptionSumbool.
Require Import Morphisms.
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
Require Import Basics.
Require Import Attenuation.
Require Import OptionMap2.
Require Import RelationClasses.
Require Import Iff_Equiv.
Require Import AccessEdge.
Require Import AccessGraphs.
Require Import SequentialAccess.


Module MakeAccessExecution (Ref:ReferenceType) (RefS: RefSetType Ref) (Edges: AccessEdgeType Ref) (AccessGraph:AccessGraphType Ref Edges) (Seq:SeqAccType Ref RefS Edges AccessGraph) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) (SemDefns: SemanticsDefinitionsType Ref Cap Ind Obj Sys) (Sem: SemanticsType Ref RefS Cap Ind Obj Sys SemDefns) (Exe: ExecutionType Ref RefS Cap Ind Obj Sys SemDefns Sem).

  Module DT := MakeAttenuation Ref RefS Edges AccessGraph Seq Cap Ind Obj Sys SemDefns Sem.
  Import DT.
  Export DT.

(*  Import Seq.RefSet_Mod. *)
  Import RefS.

  Theorem ag_objs_spec_subset: forall a b Na Nb, AG.Subset a b -> 
    Seq.ag_objs_spec a Na -> Seq.ag_objs_spec b Nb -> RefSet.Subset Na Nb.
  Proof.
    unfold Seq.ag_objs_spec; red. intros a b Na Nb Hsub Hobjs_a Hobjs_b x Hx.
    apply Hobjs_a in Hx; destruct Hx as [obj [rgt [Hedge | Hedge]]]; eapply Hsub in Hedge;
    apply Hobjs_b; do 2 eapply ex_intro; [left|right];apply Hedge.
  Qed.

  Theorem dirAcc_dep_compose : forall Fs, Proper (Sys.eq ==> Sys.eq) Fs ->
    forall Fsa, dirAcc_approx_dep Fs Fsa -> forall Fs' Fsa', dirAcc_approx_dep Fs' Fsa' ->
      dirAcc_approx_dep (compose Fs' Fs) (fun s => (compose (Fsa' (Fs s)) (Fsa s))).
  Proof.
    unfold dirAcc_approx_dep; unfold compose; 
      intros Fs HeqF Fsa Hdep Fs' Fsa' Hdep' s s' ag ag' ag2 Hda Hda2 Hsub Heq.
    (* apply Hdep' over subset, but instantiate dirAcc first *)
    generalize (exists_dirAcc_spec (Fs s)); intros [daF' HdaF'].
    eapply Hdep'; [apply HdaF'| apply Hda2|  | apply HeqF; apply Heq].
    eapply Hdep; [ apply Hda | apply HdaF' | apply Hsub | apply Heq].
  Qed.

  Implicit Arguments dirAcc_dep_compose [Fs Fsa Fs' Fsa'].

  Theorem potAcc_eq_iff: forall i p, Seq.potAcc i p -> 
    forall i', AG.eq i i' -> forall p', AG.eq p p' -> Seq.potAcc i' p'.
  Proof.
    intros i p Hpa i' Heq p' Heq'.
    destruct Hpa as [Htrans Hmax]. 
    split;
      [ eapply Seq.potTransfer_eq; [apply Heq| apply Heq' | auto]
        | red; intros a Htrans';
          eapply AG.eq_trans; [apply AG.eq_sym; apply Heq' | ]; apply Hmax;
            eapply Seq.potTransfer_eq; [apply AG.eq_sym; apply Heq'| apply AG.eq_refl | auto]
      ].
  Qed.

  
  Theorem potAcc_approx_dirAcc_dep_compose:  forall Fs, Proper (Sys.eq ==> Sys.eq) Fs ->
    forall Fsa, dirAcc_approx_dep Fs Fsa -> Proper (Sys.eq ==> AG.eq ==> AG.eq) Fsa -> 
      forall Fp, potAcc_approx_dirAcc_dep Fsa Fp -> 
        forall (Fs':Sys.t->Sys.t) Fsa', Proper (Sys.eq ==> AG.eq ==> AG.eq) Fsa' ->
          forall Fp', potAcc_approx_dirAcc_dep Fsa' Fp' -> 
            potAcc_approx_dirAcc_dep (fun s => (compose (Fsa' (Fs s)) (Fsa s))) (fun s => (compose (Fp' (Fs s)) (Fp s))).
  Proof.
    intros Fs HeqF Fsa HdaX HeqFsa Fp HpaX Fs' Fsa' HeqFsa' Fp' HpaX' 
      i i' p p' p2 s s' s'' Heq Heq' Hda Hsub Hpa Hpa' Hsub'.
    generalize (exists_dirAcc_spec (Fs s)); intros [i3 Hda3].
    generalize (HdaX _ _ _ _ _ Hda Hda3 Hsub (Sys.eq_refl _)); intros HdaXi.
    generalize (Seq.exists_potAcc (Fsa s i')); intros [p3 Hpa3].
    eapply HpaX'; 
      [ apply Sys.eq_refl
        | apply HeqF; eapply Sys.eq_trans; [apply Heq| apply Heq']
        | apply Hda3
        | apply HdaXi
        | apply Hpa3
        | eapply potAcc_eq_iff in Hpa'; [ apply Hpa'| | apply AG.eq_refl];
          eapply HeqFsa';
            [eapply HeqF; auto
              | eapply HeqFsa; [auto |apply AG.eq_refl]]
        | eapply HpaX;       
          [ apply Sys.eq_refl
            | eapply Sys.eq_trans; [apply Heq | apply Heq']
            | apply Hda 
            | apply Hsub
            | apply Hpa
            | apply Hpa3
            | apply Hsub'
          ]
      ].
  Qed.


(* This needs to change to capture s in the function *)
(* Perhaps this fixpoint will work better? *)
  
(* not efficient, but closer to inductive *)
  Fixpoint dirAcc_execute op_list s : (AG.t -> AG.t) :=
    match op_list with
      | nil => id_ag
      | cons op tail => compose (dirAcc_op op (Exe.execute s tail)) (dirAcc_execute tail s)
    end.
  
  Inductive dirAcc_execute_spec : list Sem.operation -> (Sys.t -> AG.t -> AG.t) -> Prop:=
  | dirAcc_execute_spec_nil : dirAcc_execute_spec nil (fun (s:Sys.t) (a:AG.t)=> a)
  | dirAcc_execute_spec_cons : forall op op_list Fp, dirAcc_execute_spec op_list Fp ->
    dirAcc_execute_spec (cons op op_list) (fun s => compose (dirAcc_op op (Exe.execute s op_list)) (Fp s)).
  
  Theorem dirAcc_execute_spec_dirAcc_execute: forall op_list,
    dirAcc_execute_spec op_list (dirAcc_execute op_list).
  Proof.
    intros.
    induction op_list; simpl.
  (* base *)
    apply dirAcc_execute_spec_nil.
  (* step *)
    apply dirAcc_execute_spec_cons; auto.
  Qed.

  Theorem dirAcc_execute_spec_eq_iff: forall opList Fsa,
    dirAcc_execute_spec opList Fsa <-> Fsa = (dirAcc_execute opList).
  Proof.
    intros opList.
    induction opList.
    intros; split; intros.
    inversion H.
    simpl in *.
    eauto.
    
    rewrite H; eapply dirAcc_execute_spec_dirAcc_execute.
    
    intros; split; intros.
    inversion H.
    eapply IHopList in H3.
    unfold dirAcc_execute in *.
    rewrite <- H3. auto.

    rewrite H; eapply dirAcc_execute_spec_dirAcc_execute.
    
  Qed.

  Fixpoint potAcc_execute op_list s : (AG.t -> AG.t) := 
    match op_list with
      | nil => id_ag
      | cons op tail => compose (potAcc_op op (Exe.execute s tail)) (potAcc_execute tail s)
    end.

  Inductive potAcc_execute_spec : list Sem.operation -> (Sys.t -> AG.t -> AG.t) -> Prop:=
  | potAcc_execute_spec_nil : potAcc_execute_spec nil (fun (s:Sys.t) (a:AG.t)=> a)
  | potAcc_execute_spec_cons : forall op op_list Fp, potAcc_execute_spec op_list Fp ->
    potAcc_execute_spec (cons op op_list) (fun s => compose (potAcc_op op (Exe.execute s op_list)) (Fp s)).
  
  Theorem potAcc_execute_spec_potAcc_execute: forall op_list,
    potAcc_execute_spec op_list (potAcc_execute op_list).
  Proof.
    intros.
    induction op_list; simpl.
  (* base *)
    apply potAcc_execute_spec_nil.
  (* step *)
    apply potAcc_execute_spec_cons; auto.
  Qed.

  Theorem potAcc_execute_spec_eq_iff: forall opList Fsa,
    potAcc_execute_spec opList Fsa <-> Fsa = (potAcc_execute opList).
  Proof.
    intros opList.
    induction opList.
    intros; split; intros.
    inversion H.
    simpl in *.
    eauto.
    
    rewrite H; eapply potAcc_execute_spec_potAcc_execute.
    
    intros; split; intros.
    inversion H.
    eapply IHopList in H3.
    unfold potAcc_execute in *.
    rewrite <- H3. auto.

    rewrite H; eapply potAcc_execute_spec_potAcc_execute.
    
  Qed.


  (* Inductive potAcc_execute_spec :(list Sem.operation) -> Sys.t -> (AG.t -> AG.t) -> Prop := *)
  (* | potAcc_execute_spec_nil : forall s, potAcc_execute_spec nil s id_ag *)
  (* | potAcc_execute_spec_cons: forall l s Fp, potAcc_execute_spec l s Fp ->  *)
  (*   forall op, potAcc_execute_spec (cons op l) (Sem.do_op op s) (compose (potAcc_op op s) Fp). *)

(* First, demonstrate that execution is approximated by potAcc_execute_spec *)

  (* I didn't write an operation_eq relation, so we will use eq and hope this doesn't hurt us in the long run *)
  Theorem execute_proper_1 :  Proper (Sys.eq ==> eq ==> Sys.eq) Exe.execute.
  Proof.
    unfold Proper; unfold respectful; intros.
    rewrite H0; clear H0; clear x0.
    induction y0; simpl in *; [| apply SemConv.do_op_eq]; auto.
  Qed.

  Theorem dirAcc_execute_approx : 
    forall op_list Fsa, dirAcc_execute_spec op_list Fsa ->
      dirAcc_approx_dep (fun s => (Exe.execute s op_list)) Fsa.
  Proof.
  
    intros; induction H.
  (* base *)
    unfold dirAcc_approx_dep in *; simpl in *; intros.
    eapply AGProps.subset_trans;
      [apply AGProps.subset_equal;
        eapply dirAcc_spec_eq;
          [apply Sys.eq_refl
            |apply H0
            |apply H
          ]
        |auto
      ].
  (* step *)
    eapply dirAcc_dep_compose; auto; try apply dirAcc_approx_dep_op.
  (* Execute is proper *)
    unfold Proper; unfold respectful; intros; eapply execute_proper_1; auto.
  Qed.

  Theorem proper_dirAcc_op: forall op,
    Proper (Sys.eq ==> AG.eq ==> AG.eq) (dirAcc_op op).
  Proof.
    unfold dirAcc_op; unfold Proper; unfold respectful; intros.
    destruct op; simpl; auto.
    (* id_ag cases solved , 4 cases remain*)

    (* fetch *)
    case (SemDefns.fetch_preReq_dec t t0 x);
    case (SemDefns.fetch_preReq_dec t t0 y); intros; eauto;
      (* eauto handles the no_op case.  Solve portion handles contradiciton cases. *)
      try solve [eapply SemDefns.fetch_preReq_eq_iff in f; try apply Ref.eq_refl;
        try apply Ind.eq_refl; eauto; contradiction].

    eapply ag_add_cap_by_indirect_index_equiv; eauto; try apply Ref.eq_refl.
    case ( SemDefns.option_hasRight_dec (SC.getCap t0 t x));
      case ( SemDefns.option_hasRight_dec (SC.getCap t0 t y)); intros; auto;
        (* auto handles the two easy cases, this handles the contradictory cases *)
        eapply SemDefns.option_hasRight_eq in o; solve 
          [apply n in o; contradiction
            | auto
            | apply Ref.eq_refl
            | apply AccessRight.eq_refl
          ].
    
    (* store *)
    case (SemDefns.store_preReq_dec t t0 x);
    case (SemDefns.store_preReq_dec t t0 y); intros; eauto;
      (* eauto handles the no_op case.  Solve portion handles contradiciton cases. *)
      try solve [eapply SemDefns.store_preReq_eq_iff in s; try apply Ref.eq_refl;
        try apply Ind.eq_refl; eauto; contradiction].
     eapply ag_push_cap_by_indices_equiv; eauto; try apply Ref.eq_refl.

     (* send *)
     case (SemDefns.send_preReq_dec t t0 x);
     case (SemDefns.send_preReq_dec t t0 y); intros; eauto;
     (* eauto handles the no_op case.  Solve portion handles contradiciton cases. *)
         try solve [eapply SemDefns.send_preReq_eq_iff in s; try apply Ref.eq_refl;
        try apply Ind.eq_refl; eauto; contradiction].
     unfold send_dep_ag.
     destruct s as [s_1 s_2]; destruct s0 as [s0_1 s0_2].
     unfold SemDefns.option_hasRight in *.
     (case (option_sumbool (SC.getCap t0 t x)); intros opt1; [|destruct opt1 as [v1 opt1]]; try rewrite opt1 in *;
     (case (option_sumbool (SC.getCap t0 t y)); intros opt2; [|destruct opt2 as [v2 opt2]]; try rewrite opt2 in *);
       simpl in *; try contradiction).
     generalize H; intros H'.
     eapply SC.getCap_eq with (i:=t0) (o:=t) in H'; [ | apply Ind.eq_refl | apply Ref.eq_refl ].
     rewrite opt1 in H'; rewrite opt2 in H'; simpl in H'.
     eapply Cap.target_eq in H'.
     
     case (option_map1_eq_tgt_dec t0 t x);
     case (option_map1_eq_tgt_dec t0 t y); intros; eauto;
       try rewrite opt1 in *; try rewrite opt2 in *; simpl in *;
         try solve [rewrite H' in *; contradiction
           | eapply ag_add_caps_reply_equiv; eauto; try apply Ref.eq_refl
           | eapply ag_add_caps_send_equiv; eauto; try apply Ref.eq_refl; try apply CIL_Facts.cil_Equiv
         ].

     (* allocate *)
     unfold allocate_dep_ag.
     case (SemDefns.allocate_preReq_dec t t0 x);
     case (SemDefns.allocate_preReq_dec t t0 y); intros; eauto;
     (* eauto handles the no_op case.  Solve portion handles contradiciton cases. *)
         try solve [eapply SemDefns.allocate_preReq_eq_iff in a; try apply Ref.eq_refl;
        try apply Ind.eq_refl; eauto; contradiction].
     eapply ag_add_caps_allocate_equiv; eauto; try apply Ref.eq_refl; try apply CIL_Facts.cil_Equiv.
  Qed.


  Theorem dirAcc_execute_spec_proper : forall op_list Fsa,
    dirAcc_execute_spec op_list Fsa -> Proper (Sys.eq ==> AG.eq ==> AG.eq) Fsa.
  Proof.
    intros op_list Fsa H.
    induction H; auto.
    (* step *)
    unfold Proper; unfold respectful; intros.
    eapply proper_dirAcc_op.
    eapply execute_proper_1; auto.
    eapply IHdirAcc_execute_spec; auto.
  Qed.
  
  Hint Resolve proper_dirAcc_op dirAcc_execute_spec_proper.


  Theorem potAcc_execute_approx :
    forall op_list Fsa, dirAcc_execute_spec op_list Fsa ->
      forall Fp, potAcc_execute_spec op_list Fp ->
        potAcc_approx_dirAcc_dep Fsa Fp.
  Proof.
    intros. revert H. revert Fsa.
    induction H0.
  (* base *)
    unfold potAcc_approx_dirAcc_dep. intros.
    inversion H. rewrite <- H8 in H5.
    eapply AGProps.subset_trans; [ | apply H6].
    apply AGProps.subset_equal.
    eapply potAcc_equiv; try apply AG.eq_refl; eauto.
  (* step *)
    intros. inversion H.
    eapply potAcc_approx_dirAcc_dep_compose; 
      try solve 
        [auto 
          | (* execute is proper *)
            unfold Proper; unfold respectful; intros; eapply execute_proper_1; auto
          | (* dirAcc_approx_dep *)
            apply dirAcc_execute_approx; auto
          | (* potAcc_approx_dirAcc_dep (dirAcc_op op) (potAcc_op op) *)
            apply potAcc_approx_dirAcc_dep_op; auto
          | eauto
        ].
  Qed.

(* Second, demonstrate that such approximation is reducing over the existing objs *)


  Theorem Proper_AG_attenuating :
    Proper (RefSet.eq ==> AG.eq ==> AG.eq ==> iff) AG_attenuating.
  Proof.
    unfold Proper. unfold respectful. unfold AG_attenuating; intros.
    split; intros;
      
      (case (Ref.eq_dec src tgt); intros Heq;
        [intuition eauto 
          | right; edestruct H2; 
            [ eapply H; apply H3 
              | eapply H; apply H4 
              | intro Hnot; apply H5; apply H0; apply Hnot
              | contradiction 
              | intro Hnot; apply H6; apply H1; apply Hnot
            ]
        ]). 

  Qed.

  Theorem Proper_AG_attenuating_2 :
    Proper (RefSet.eq ==> AG.eq ==> AG.Subset --> impl) AG_attenuating.
  Proof.
    unfold Proper. unfold respectful. unfold impl. unfold flip;  unfold AG_attenuating; intros.
    
    case (Ref.eq_dec src tgt); intros Heq; [intuition eauto | ].
    right; edestruct H2;
      [eapply H; apply H3
        | eapply H; apply H4
        | intro Hnot; apply H5; apply H0; apply Hnot
        | contradiction
        | intro Hnot; apply H6; apply H1; apply Hnot].

  Qed.

  Theorem Proper_AG_attenuating_3:
    Proper (RefSet.Subset --> AG.eq ==> AG.Subset --> impl) AG_attenuating.
  Proof.
    unfold Proper; unfold respectful; unfold impl; unfold flip; intros.
    eapply AG_attenuating_subset_objs; [ | apply H].
    eapply Proper_AG_attenuating_2; eauto. apply RefSet.eq_refl.
  Qed.

  Theorem Proper_AG_attenuating_4:
    Proper (RefSet.Subset --> AG.Subset ==> AG.Subset --> impl) AG_attenuating.
  Proof.
    unfold Proper; unfold respectful; unfold impl; unfold flip; intros. 
    unfold AG_attenuating in *; intros.
    case (Ref.eq_dec src tgt); try solve [intuition auto]; right.
    edestruct H2;
    [ eapply H; apply H3
      | eapply H; apply H4
      |   intro Hnot; apply H5; apply H0; apply Hnot
      |  contradiction
      |  intro Hnot; apply H6; apply H1; apply Hnot].
  Qed.

  (* Helper functions for objs_not_unborn *)
  
  Theorem is_label_id: forall s s', Sys.eq s s' ->
    forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
  Proof.
    intros s s' Heq o lbl; split; intros Hlbl;
      (eapply SC.isLabel_eq;
        [eapply Ref.eq_refl
          |eapply ObjectLabel.eq_refl
          |eauto
          |auto]).
  Qed.
  Theorem is_label_read: forall a t s s', Sys.eq (Sem.do_read a t s) s' -> 
    forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
  Proof.
    intros a t s s' Heq;
      eapply Sys.eq_trans in Heq; 
        [eapply is_label_id; eauto
          | eapply Sys.eq_sym; eapply Sem.read_spec].
  Qed.

  Theorem is_label_write: forall a t s s', Sys.eq (Sem.do_write a t s) s' -> 
    forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
  Proof.
    intros a t s s' Heq;
      eapply Sys.eq_trans in Heq; 
        [eapply is_label_id; eauto
          | eapply Sys.eq_sym; eapply Sem.write_spec].
  Qed.

  Theorem is_label_fetch_invalid: forall a t c i s s', Sys.eq (Sem.do_fetch a t c i s) s' ->
    ~ SemDefns.fetch_preReq a t s ->
    forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
  Proof.
    intros a t c i s s' Heq Hprereq.
    eapply Sys.eq_trans in Heq; 
      [ eapply is_label_id; eauto
        | eapply Sys.eq_sym; eapply Sem.fetch_invalid; eauto].
  Qed.

  Theorem is_label_copyCap: forall c t i a s s', Sys.eq (SemDefns.SC.copyCap c t i a s) s' ->
    forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
  Proof.
    intros c t i a s s' Heq o lbl; split; intros Hlbl; unfold SC.is_label in *;
      
          (* first case *)
      (case (option_sumbool (SC.getLabel o s)); intros Hcase; [|destruct Hcase as [tup Hcase]]; 
        try rewrite Hcase in *; simpl in *; try solve [contradiction];
          (* second case *)
          (case (option_sumbool (SC.getLabel o s')); intros Hcase'; [|destruct Hcase' as [tup' Hcase']]; 
            try rewrite Hcase' in *; simpl in *; try solve [contradiction];
          (* getLabel equiv and solv *)
              (eapply SC.getLabel_copyCap_map_eq_equiv in Hcase'; [ | eapply Heq | apply Hcase ]; simpl in *;
                try solve 
                  [contradiction 
                    | eapply ObjectLabel.eq_trans; solve [eauto | eapply ObjectLabel.eq_sym; eauto]]))).
  Qed.


    (* move the next two Theorems to systemstate_convimpl *)
    Theorem getLabel_weakCopyCap_map_eq: forall s i o i' o' i_src opt_i_lbl opt_i_lbl',
    SC.getLabel i_src s = opt_i_lbl ->
    SC.getLabel i_src (SC.weakCopyCap i o i' o' s) = opt_i_lbl' ->
    option_map_eq ObjectLabel.eq opt_i_lbl opt_i_lbl'.
    Proof.
    intros s i o i' o' i_src opt_i_lbl opt_i_lbl' Hi_lbl Hi_lbl'.
    unfold SC.weakCopyCap in *; unfold SC.getCap in *; unfold SC.getObj in *.

    case (option_sumbool (SC.getObjTuple o s)); intros Hopt1;
      [| destruct Hopt1 as [o'_tuple Hopt1]]; rewrite Hopt1 in *; simpl in *; auto;
        try solve [rewrite <- Hi_lbl; rewrite <- Hi_lbl'; eapply option_map_eq_refl; eauto].
    destruct_tuple o'_tuple o'_obj o'_lbl o'_type o'_sched; simpl in *.

    case (option_sumbool (OC.getCap i o'_obj)); intros Hopt2;
      [| destruct Hopt2 as [copied_cap Hopt2]]; rewrite Hopt2 in *; simpl in *; auto;
        try solve [rewrite <- Hi_lbl; rewrite <- Hi_lbl'; eapply option_map_eq_refl; eauto].

    unfold SC.addCap in *; unfold SC.getLabel in *;
    unfold SC.getObj in *; unfold SC.updateObj in *.

    case (option_sumbool (SC.getObjTuple o' s)); intros Hopt3;
      [|destruct Hopt3 as [t_tuple Hopt3]; destruct_tuple t_tuple t_obj t_lbl t_type t_sched];
      rewrite Hopt3 in *; simpl in *;
        try solve [rewrite <- Hi_lbl; rewrite <- Hi_lbl'; eapply option_map_eq_refl; eauto].        

    unfold SC.addObjTuple in *; unfold SC.getObjTuple in *; unfold OC.addCap in *.
    
    case (Ref.eq_dec o' i_src ); intros Heq1.
    (* i_src [=] o' *)
    rewrite Sys_Facts.add_eq_o in Hi_lbl'; simpl in *; auto.
    unfold SC.tupleGetLabel in *.
    rewrite Heq1 in *; rewrite Hopt3 in *; simpl in *;
      try solve [rewrite <- Hi_lbl; rewrite <- Hi_lbl'; eapply option_map_eq_refl; eauto].

    (* i_src [<>] o' *)
    rewrite Sys_Facts.add_neq_o in Hi_lbl'; simpl in *; auto;
      try solve [rewrite <- Hi_lbl; rewrite <- Hi_lbl'; eapply option_map_eq_refl; eauto].
    Qed.

    Theorem getLabel_weakCopyCap_map_eq_equiv: forall s i o i' o' i_src s' opt_i_lbl opt_i_lbl',
      Sys.eq (SC.weakCopyCap i o i' o' s) s' ->
    SC.getLabel i_src s = opt_i_lbl ->
    SC.getLabel i_src s' = opt_i_lbl' ->
    option_map_eq ObjectLabel.eq opt_i_lbl opt_i_lbl'.
    Proof.
      intros.
      eapply option_map_eq_transitive; 
        [eauto
          |
          |rewrite <- H1; eapply SC.getLabel_eq; [eapply Ref.eq_refl| eapply H]].
      
      rewrite <- H0.
      eapply getLabel_weakCopyCap_map_eq; eapply eq_refl.
    Qed.


        Theorem is_label_weakCopyCap: forall c t i a s s', Sys.eq (SemDefns.SC.weakCopyCap c t i a s) s' ->
           forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
        Proof.
          intros c t i a s s' Heq o lbl; split; intros Hlbl; unfold SC.is_label in *;
            
          (* first case *)
            (case (option_sumbool (SC.getLabel o s)); intros Hcase; [|destruct Hcase as [tup Hcase]]; 
              try rewrite Hcase in *; simpl in *; try solve [contradiction];
          (* second case *)
                (case (option_sumbool (SC.getLabel o s')); intros Hcase'; [|destruct Hcase' as [tup' Hcase']]; 
                  try rewrite Hcase' in *; simpl in *; try solve [contradiction];
          (* getLabel equiv and solv *)
                    (eapply getLabel_weakCopyCap_map_eq_equiv in Hcase'; [ | eapply Heq | apply Hcase ]; simpl in *;
                      try solve 
                        [contradiction 
                          | eapply ObjectLabel.eq_trans; solve [eauto | eapply ObjectLabel.eq_sym; eauto]]))).
        Qed.

      Theorem is_label_fetch_valid: forall a t c i s s', Sys.eq (Sem.do_fetch a t c i s) s' ->
        SemDefns.fetch_preReq a t s ->
        forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
      Proof.
        intros a t c i s s' Heq Hfetch_prereq.
        case (SemDefns.option_hasRight_dec (SemDefns.SC.getCap t a s) rd); intros Hread'.


        generalize Hfetch_prereq; intros [Hprereq Hopt];
          eapply Sys.eq_trans in Heq;
            [ 
              | eapply Sys.eq_sym; eapply Sem.fetch_read; eauto].
        (* has read *)
        destruct Hprereq as [[Halive Hactive] Htarget_alive].
        unfold SemDefns.target_is_alive in *.
        case (option_sumbool (SemDefns.SC.getCap t a s)); intros Hcap; [| destruct Hcap as [cap Hcap]];
        rewrite Hcap in *; simpl in *; try contradiction.
        eapply is_label_copyCap; eauto.
        (* no read *)
        generalize Hfetch_prereq; intros [Hprereq [Hread | Hweak]]; try contradiction.
          eapply Sys.eq_trans in Heq;
            [ 
              | eapply Sys.eq_sym; eapply Sem.fetch_weak; eauto].
        destruct Hprereq as [[Halive Hactive] Htarget_alive].
        unfold SemDefns.target_is_alive in *.
        case (option_sumbool (SemDefns.SC.getCap t a s)); intros Hcap; [| destruct Hcap as [cap Hcap]];
        rewrite Hcap in *; simpl in *; try contradiction.
        unfold SC.weakCopyCap in *.
        eapply is_label_weakCopyCap; eauto.
      Qed.

      Theorem is_label_store_invalid: forall a t c i s s', Sys.eq (Sem.do_store a t c i s) s' ->
        ~ SemDefns.store_preReq a t s ->
        forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
      Proof.
        intros a t c i s s' Heq Hprereq.
        eapply Sys.eq_trans in Heq; 
        [ eapply is_label_id; eauto
          | eapply Sys.eq_sym; eapply Sem.store_invalid; eauto].
      Qed.
      
      Theorem is_label_store_valid: forall a t c i s s', Sys.eq (Sem.do_store a t c i s) s' ->
        SemDefns.store_preReq a t s ->
        forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
      Proof.
        intros a t c i s s' Heq Hstore_prereq.

        generalize Hstore_prereq; intros [Hprereq Hright];
          eapply Sys.eq_trans in Heq; [ | eapply Sys.eq_sym; eapply Sem.store_valid; eauto].

        destruct Hprereq as [[Halive Hactive] Htarget_alive].
        unfold SemDefns.target_is_alive in *.
        case (option_sumbool (SemDefns.SC.getCap t a s)); intros Hcap; [| destruct Hcap as [cap Hcap]];
        rewrite Hcap in *; simpl in *; try contradiction.
        eapply is_label_copyCap; eauto.
      Qed.

      Theorem is_label_revoke_invalid: forall a t c s s', Sys.eq (Sem.do_revoke a t c s) s' ->
        ~ SemDefns.revoke_preReq a t s ->
        forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
      Proof.
        intros a t c s s' Heq Hprereq.
        eapply Sys.eq_trans in Heq; 
        [ eapply is_label_id; eauto
          | eapply Sys.eq_sym; eapply Sem.revoke_invalid; eauto].
      Qed.
      
      Theorem getLabel_updateObj_equiv: forall n o s s',
        Sys.eq (SC.updateObj n o s) s' -> forall a,
          SC.getLabel a s = SC.getLabel a s'.
      Proof.
        unfold SC.updateObj.
        unfold SC.getLabel.
        unfold SC.getObj.
        unfold SC.addObjTuple.
        unfold SC.getObjTuple.
        intros.
        case (option_sumbool (Sys.MapS.find n s)); intros Hcase; [|destruct Hcase as [[[[o' l'] t'] d'] Hcase]]; 
          rewrite Hcase in *; simpl in *; auto.

            (* equiv *)
        
        generalize (Sys_MapEquiv.find_eq a _ _ _ (Ref.eq_refl _) H); intros Heq.
        
        case (option_sumbool (Sys.MapS.find a s));intros Hcase1; 
          [|destruct Hcase1 as [tup1 Hcase1]]; rewrite Hcase1 in *; simpl in *;
            (case (option_sumbool (Sys.MapS.find a s'));intros Hcase2; 
              [|destruct Hcase2 as [tup2 Hcase2]]; rewrite Hcase2 in *; simpl in *);
            try contradiction; auto.
        unfold SC.tupleGetLabel. 
        destruct tup1 as [[[obj1 lbl1] sch1] typ1];
          destruct tup2 as [[[obj2 lbl2] sch2] typ2];
            destruct Heq as [[[Heq1 Heq2] Heq3] Heq4]; simpl in *.
        rewrite Heq2 in *; auto.


            (* not equiv *)

        generalize (Sys_MapEquiv.find_eq a _ _ _ (Ref.eq_refl _) H); intros Heq.

        case (Ref.eq_dec a n); intros Heq_r.

        


        rewrite Sys_Facts.add_eq_o in Heq; simpl in *; auto; try contradiction.
        unfold Sys.P.t in *.
        case (option_sumbool (Sys.MapS.find a s));intros Hcase1; 
          [|destruct Hcase1 as [tup1 Hcase1]]; rewrite Hcase1 in *; simpl in *;
            (case (option_sumbool (Sys.MapS.find a s'));intros Hcase2; 
              [|destruct Hcase2 as [tup2 Hcase2]]; rewrite Hcase2 in *; simpl in *);
            try contradiction; auto; simpl in *;

              (try destruct tup1 as [[[obj1 lbl1] sch1] typ1];
                destruct tup2 as [[[obj2 lbl2] sch2] typ2];
                  destruct Heq as [[[Heq1 Heq2] Heq3] Heq4]; simpl in *;
                    rewrite Heq2 in *; auto;
                      rewrite Heq_r in *;
                        rewrite Hcase in *;
                          try solve [discriminate | injection Hcase1; intros H1 H2 H3 H4; rewrite H3; auto]).

        rewrite Sys_Facts.add_neq_o in Heq; simpl in *; auto; try contradiction.
        unfold Sys.P.t in *.
        case (option_sumbool (Sys.MapS.find a s));intros Hcase1; 
          [|destruct Hcase1 as [tup1 Hcase1]]; rewrite Hcase1 in *; simpl in *;
            (case (option_sumbool (Sys.MapS.find a s'));intros Hcase2; 
              [|destruct Hcase2 as [tup2 Hcase2]]; rewrite Hcase2 in *; simpl in *);
            try contradiction; auto; simpl in *.

        try destruct tup1 as [[[obj1 lbl1] sch1] typ1];
          destruct tup2 as [[[obj2 lbl2] sch2] typ2];
            destruct Heq as [[[Heq1 Heq2] Heq3] Heq4]; simpl in *.
        
        rewrite Heq2; auto.
      Qed.
      Implicit Arguments getLabel_updateObj_equiv [n o s s'].

        Theorem is_label_rmCap: forall c t s s', Sys.eq (SC.rmCap c t s) s' ->
           forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
        Proof.
          intros c t s s' Heq o lbl; split; intros Hlbl; unfold SC.is_label in *;
          unfold SC.rmCap in *;

            (case (option_sumbool (SC.getObj t s)); intros Hcase2; [| destruct Hcase2 as [obj Hcase2]];
              try rewrite Hcase2 in *; simpl in *; try contradiction);

            solve [
          (* equiv case  *)
          case (option_sumbool (SC.getLabel o s')); intros Hcase'; [|destruct Hcase' as [tup' Hcase']]; 
            try rewrite Hcase' in *; simpl in *; try solve [contradiction];
              (case (option_sumbool (SC.getLabel o s)); intros Hcase; [|destruct Hcase as [tup Hcase]]; 
                try rewrite Hcase in *; simpl in *; try solve [contradiction];
                  (eapply SC.getLabel_eq with (r:=o) in Heq; [| eapply Ref.eq_refl];
                    rewrite Hcase in Heq; rewrite Hcase' in Heq;  simpl in *; 
                      solve [contradiction
                        | eapply ObjectLabel.eq_trans; solve [eapply Sys.eq_sym; eauto | eauto]]))
|
          (* second *)

          generalize (getLabel_updateObj_equiv Heq); intros Hrw;
          rewrite Hrw in *; auto].
          Qed.

      Theorem is_label_revoke_valid: forall a t c s s', Sys.eq (Sem.do_revoke a t c s) s' ->
        SemDefns.revoke_preReq a t s ->
        forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
      Proof.
        intros a t c s s' Heq Hrevoke_prereq.

        generalize Hrevoke_prereq; intros [Hprereq Hright];
          eapply Sys.eq_trans in Heq; [ | eapply Sys.eq_sym; eapply Sem.revoke_valid; eauto].

        destruct Hprereq as [[Halive Hactive] Htarget_alive].
        unfold SemDefns.target_is_alive in *.
        case (option_sumbool (SemDefns.SC.getCap t a s)); intros Hcap; [| destruct Hcap as [cap Hcap]];
        rewrite Hcap in *; simpl in *; try contradiction.
        eapply is_label_rmCap; eauto.
      Qed.

        Theorem is_label_copyCapList: forall c t ixi_list s s', Sys.eq (SC.copyCapList c t ixi_list s) s' ->
           forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
        Proof.
          intros c t ixi_list s s' Heq o lbl; split; intros Hlbl; unfold SC.is_label in *;
            
          (* first case *)
            (case (option_sumbool (SC.getLabel o s)); intros Hcase; [|destruct Hcase as [tup Hcase]]; 
              try rewrite Hcase in *; simpl in *; try solve [contradiction];
          (* second case *)
                (case (option_sumbool (SC.getLabel o s')); intros Hcase'; [|destruct Hcase' as [tup' Hcase']]; 
                  try rewrite Hcase' in *; simpl in *; try solve [contradiction];
          (* getLabel equiv and solv *)
                    (eapply SC.getLabel_copyCapList_map_eq_equiv in Hcase'; [ | eapply Heq | apply Hcase ]; simpl in *;
                      try solve 
                        [contradiction 
                          | eapply ObjectLabel.eq_trans; solve [eauto | eapply ObjectLabel.eq_sym; eauto]]))).
        Qed.

        Theorem is_label_addCap: forall c a cap s s', Sys.eq (SC.addCap c cap a s) s' ->
           forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
        Proof.
          intros c a cap s s' Heq o lbl; split; intros Hlbl; unfold SC.is_label in *;
          unfold SC.addCap in *; unfold SC.getObj in *;
            (case (option_sumbool (SC.getObjTuple a s)); intros Htuple; [| destruct Htuple as [[[[obj1 lbl1] typ1] schd1] Htuple]];
              rewrite Htuple in *; simpl in *; try contradiction;
            (case (option_sumbool (SC.getLabel o s)); intros Hcase; [|destruct Hcase as [tup Hcase]]; 
              try rewrite Hcase in *; simpl in *; try solve [contradiction];
                (case (option_sumbool (SC.getLabel o s')); intros Hcase'; [|destruct Hcase' as [tup' Hcase']]; 
                  try rewrite Hcase' in *; simpl in *; try solve [contradiction])));
            try solve [
          (* Solve s [=] s' cases *)
              first 
                [ generalize (getLabel_updateObj_equiv Heq o); intros Hlbl_eq
                  | generalize (SC.getLabel_eq _ _ _ _ (Ref.eq_refl o) Heq); intros Hlbl_eq
                ];
                try rewrite Hcase' in Hlbl_eq; try rewrite Hcase in Hlbl_eq; try rewrite Hlbl_eq in *; simpl in *; 
                  (* attempt solutions *)
                  try contradiction; try discriminate; auto;
                    try solve [injection Hlbl_eq; intros Hlbl_eq'; rewrite Hlbl_eq' in *; auto]].
        Qed.

      Theorem is_label_send_valid: forall a t c i s s', Sys.eq (Sem.do_send a t c i s) s' ->
        SemDefns.send_preReq a t s ->
        forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
      Proof.
        intros a t c i s s' Heq Hsend_prereq.

        generalize Hsend_prereq; intros [Hprereq Hright];
          eapply Sys.eq_trans in Heq; [ | eapply Sys.eq_sym; eapply Sem.send_valid; eauto].

        destruct Hprereq as [[Halive Hactive] Htarget_alive].
        unfold SemDefns.target_is_alive in *.
        case (option_sumbool (SemDefns.SC.getCap t a s)); intros Hcap; [| destruct Hcap as [cap Hcap]];
        rewrite Hcap in *; simpl in *; try contradiction.
        case (option_sumbool i); intros Hi; [|destruct Hi as [i' Hi]]; rewrite Hi in *; simpl in *.
        (* no reply *)
        eapply is_label_copyCapList; eauto.
        (* has reply *)
        intros o lbl.

        eapply Sys.eq_trans in Heq; 
          [|eapply SC.copyCapList_eq; [ eapply Ref.eq_refl | apply Ref.eq_refl | eapply CIL_Facts.cil_Equiv| ]].
        eapply iff_sym; eapply iff_trans; eapply iff_sym.
        eapply is_label_copyCapList; apply Heq.
        2:apply Sys.eq_refl.
        eapply is_label_addCap; eapply Sys.eq_refl.
      Qed.

      Theorem is_label_send_invalid: forall a t c i s s', Sys.eq (Sem.do_send a t c i s) s' ->
        ~ SemDefns.send_preReq a t s ->
        forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
      Proof.
        intros a t c i s s' Heq Hprereq.
        eapply Sys.eq_trans in Heq; 
        [ eapply is_label_id; eauto
          | eapply Sys.eq_sym; eapply Sem.send_invalid; eauto].
      Qed.

      Theorem is_label_allocate_invalid: forall a t c i s s', Sys.eq (Sem.do_allocate a t c i s) s' ->
        ~ SemDefns.allocate_preReq a t s ->
        forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
      Proof.
        intros a t c i s s' Heq Hprereq.
        eapply Sys.eq_trans in Heq; 
        [ eapply is_label_id; eauto
          | eapply Sys.eq_sym; eapply Sem.allocate_invalid; eauto].
      Qed.

      Theorem is_label_allocate_valid: forall a t c i s s', Sys.eq (Sem.do_allocate a t c i s) s' ->
        SemDefns.allocate_preReq a t s ->
        forall o lbl, (if (Ref.eq_dec o t) then 
          SC.is_label o s unborn /\ ObjectLabel.eq lbl alive 
          else SC.is_label o s lbl) <-> 
          SC.is_label o s' lbl.
      Proof.
        intros a t c i s s' Heq Hallocate_prereq o lbl.

        generalize Hallocate_prereq; intros [Halive Hunborn];
          eapply Sys.eq_trans in Heq; [ | eapply Sys.eq_sym; eapply Sem.allocate_valid; eauto].

        generalize Hunborn; intros Hunborn'; eapply SC.is_label_iff_getLabel in Hunborn.

        eapply Sys.eq_trans in Heq.
        2:eapply SC.addCap_eq; [ eapply Ind.eq_refl| eapply Cap.eq_refl | eapply Ref.eq_refl| ].
        eapply iff_trans.
        2:eapply is_label_addCap; apply Heq.
        2:apply Sys.eq_refl.

        clear Heq.
        
        eapply iff_trans.
        2:eapply is_label_copyCapList;eapply Sys.eq_refl.

        (* cases of o [=] t *)
        case (Ref.eq_dec o t); intros Href_case.
        (* o [=] t *) 
        rewrite Href_case in *.

        unfold SC.set_alive.
        unfold SC.is_label in *.
        unfold SC.is_unborn in *.

        rewrite SC.getLabel_set_label_eq_o; simpl; try apply Ref.eq_refl.
        rewrite SC.getLabel_updateObj_o.
        rewrite SC.getLabel_rmCapsByTarget_o.
        rewrite Hunborn in *; simpl.
        intuition (eauto; try apply ObjectLabel.eq_sym; auto).

        (* o [<>] t *)
        unfold SC.set_alive in *.
        unfold SC.is_label in *.
        unfold SC.is_unborn in *.

        rewrite SC.getLabel_set_label_neq_o; auto.
        rewrite SC.getLabel_updateObj_o.
        rewrite SC.getLabel_rmCapsByTarget_o; auto.
        eapply iff_refl.
      Qed.
      Implicit Arguments is_label_allocate_valid [a t c i s s' o lbl].

      Theorem is_label_allocate_valid_unborn: forall a t c i s s', Sys.eq (Sem.do_allocate a t c i s) s' ->
        SemDefns.allocate_preReq a t s ->
        forall lbl, ObjectLabel.eq lbl unborn ->
        forall o, SC.is_label o s' lbl -> SC.is_label o s lbl.
      Proof.
        intros.
        eapply is_label_allocate_valid in H2; try eauto 1.
        revert H2; case (Ref.eq_dec o t); intros Hcase H2; intuition.
        eapply ObjectLabel.eq_trans in H1; [|apply ObjectLabel.eq_sym; apply H4]; discriminate H1.
      Qed.
      
      Require Import OptionMap2.


      

      Theorem is_label_destroy_valid: forall a t s s', Sys.eq (Sem.do_destroy a t s) s' ->
        SemDefns.destroy_preReq a t s ->
        forall o lbl, (if (option_map_eq_dec Ref.eq_dec (Some o) (SemDefns.option_target (SC.getCap t a s))) then 
          SC.is_label o s alive /\ ObjectLabel.eq lbl dead 
          else SC.is_label o s lbl) <-> 
          SC.is_label o s' lbl.
      Proof.
        intros a t s s' Heq Hdestroy_prereq o lbl.

        generalize Hdestroy_prereq; intros [[[Halive Hactive] Htarget_alive] Hwrite];
          eapply Sys.eq_trans in Heq; [ | eapply Sys.eq_sym; eapply Sem.destroy_valid; eauto].

        unfold SemDefns.target_is_alive in *.
        unfold SC.getCap in *.
        unfold SC.getObj in *.
        
        case (option_sumbool (SC.getObjTuple a s)) as [Hcase | [[[[obj1 lbl1] typ1] sch1] Hcase]];
          rewrite Hcase in *; simpl in *; try contradiction;
            (case (option_sumbool (OC.getCap t obj1)) as [Hcase2 | [cap Hcase2]];
              rewrite Hcase2 in *; simpl in*; try contradiction).

        unfold SC.is_alive in *.
        clear Hcase Hcase2 Hwrite.
        revert Heq Htarget_alive.  generalize (Cap.target cap). intros target Heq Htarget_alive.
        clear obj1 lbl1 typ1 sch1. clear cap.
        clear Hactive.
        unfold SC.set_dead in *.


        idtac.
        eapply iff_trans; [ clear Heq |
          apply SC.is_label_eq_iff; [ apply Ref.eq_refl| apply Heq | apply ObjectLabel.eq_refl]].
 
        case (option_map_eq_dec Ref.eq_dec (Some o) (Some target)) as [Heq_t|Heq_t]; simpl in *.
        unfold Ref.eq in Heq_t; rewrite Heq_t in *.


        (* target [=] o] *)
        rewrite SC.is_label_set_label_eq_o; [| apply Ref.eq_sym; auto].
        generalize Htarget_alive; intros Htarget_alive'.
        eapply SC.is_label_iff_getLabel in Htarget_alive.
        rewrite Htarget_alive.
        intuition.

        (* target [<>] o *)
        rewrite SC.is_label_set_label_neq_o; [apply iff_refl| intro; apply Heq_t; apply Ref.eq_sym; auto].
      Qed.
      Implicit Arguments is_label_destroy_valid [a t s s' o lbl].

      Theorem is_label_destroy_valid_unborn: forall a t s s', Sys.eq (Sem.do_destroy a t s) s' ->
        SemDefns.destroy_preReq a t s ->
        forall lbl, ObjectLabel.eq lbl unborn ->
        forall o, SC.is_label o s' lbl -> SC.is_label o s lbl.
      Proof.
        intros.
        eapply is_label_destroy_valid in H2; try eauto 1.
        revert H2; case (option_map_eq_dec Ref.eq_dec (Some o) (SemDefns.option_target (SC.getCap t a s)));
          intros Hcase H2; intuition.
        eapply ObjectLabel.eq_trans in H1; [|apply ObjectLabel.eq_sym; apply H4]; discriminate H1.
      Qed.
      





      Theorem is_label_destroy_invalid: forall a t s s', Sys.eq (Sem.do_destroy a t s) s' ->
        ~ SemDefns.destroy_preReq a t s ->
        forall o lbl, (SC.is_label o s lbl <-> SC.is_label o s' lbl).
      Proof.
        intros a t s s' Heq Hprereq.
        eapply Sys.eq_trans in Heq; 
        [ eapply is_label_id; eauto
          | eapply Sys.eq_sym; eapply Sem.destroy_invalid; eauto].
      Qed.

        Theorem set_label_eq: forall t t', Ref.eq t t' ->
          forall l l', ObjectLabel.eq l l' ->
            forall s s', Sys.eq s s' ->
              Sys.eq (SC.set_label t s l) (SC.set_label t' s' l').
        Proof.
          intros.
          unfold SC.set_label in *.
          generalize (SC.getObjTuple_eq _ _ _ _ H H1); intros Heq_tuple.
          case (option_sumbool (SC.getObjTuple t s)) as [Hcase | [[[[obj lbl] sch] typ] Hcase]]; 
            rewrite Hcase in *; simpl in *; 
              (case (option_sumbool (SC.getObjTuple t' s')) as [Hcase' | [[[[obj' lbl'] sch'] typ'] Hcase']]; 
                rewrite Hcase' in *; simpl in *; try contradiction; eauto). 
          destruct Heq_tuple as [[[Hobj Hlbl] Hsch] Htyp]; simpl in *.
          eapply SC.addObjTuple_eq; eauto; try apply Ref.eq_refl.
          unfold ObjectLabel.eq in *. rewrite H0; rewrite Hsch; rewrite Hobj; rewrite Htyp.
          eapply Sys.P.eq_refl.
        Qed.





    (* we need a theorem about objs_not_unborn n s -> Exe.execute_def s list s' -> objs_not_unborn n s' *)


      Theorem objs_not_unborn_op: forall n s, objs_not_unborn n s ->
        forall op s', Sys.eq (Sem.do_op op s) s' -> objs_not_unborn n s'.
      Proof.
      intros n s Hobjs op s' H.
      unfold objs_not_unborn in *.
      intros x Hx Hnot.
      eapply Hobjs.
      apply Hx.


      unfold SC.is_unborn in *.
      (* cases *)
      destruct op. simpl in *.
      (* read *)
      eapply is_label_read; eauto.
      (* write *)
      eapply is_label_write; eauto.
      (* fetch *)
      case (SemDefns.fetch_preReq_dec t t0 s); intros Hcase;
        solve [ eapply is_label_fetch_valid; eauto | eapply is_label_fetch_invalid; eauto].
      (* store *)
      case (SemDefns.store_preReq_dec t t0 s); intros Hcase;
        solve [ eapply is_label_store_valid; eauto | eapply is_label_store_invalid; eauto].
      (* revoke *)
      case (SemDefns.revoke_preReq_dec t t0 s); intros Hcase;
        solve [ eapply is_label_revoke_valid; eauto | eapply is_label_revoke_invalid; eauto].
      (* send *)
      case (SemDefns.send_preReq_dec t t0 s); intros Hcase;
        solve [ eapply is_label_send_valid; eauto | eapply is_label_send_invalid; eauto].
      (* allocate *)
       case (SemDefns.allocate_preReq_dec t t0 s); intros Hcase;
         solve 
         [ eapply is_label_allocate_valid_unborn; solve [eauto; apply ObjectLabel.eq_refl] 
           | eapply is_label_allocate_invalid; eauto
         ].
       (* destroy *)
       case (SemDefns.destroy_preReq_dec t t0 s); intros Hcase;
         solve 
         [ eapply is_label_destroy_valid_unborn; solve [eauto; apply ObjectLabel.eq_refl] 
           | eapply is_label_destroy_invalid; eauto
         ].        
      Qed.

    Theorem objs_not_unborn_oplist : forall n s, objs_not_unborn n s ->
      forall opL s', Exe.execute_def s opL s' -> objs_not_unborn n s'.
    Proof.
      intros n s Hobjs opL s' Hexe.
      induction Hexe.
      (* base *)
      unfold objs_not_unborn in *.
      intros x Hx Hnot.
      eapply Hobjs.
      apply Hx.
      unfold SC.is_unborn in *.
      eapply SC.isLabel_eq in Hnot.
        apply Hnot.
        apply Ref.eq_refl.
        apply ObjectLabel.eq_refl.
        apply Sys.eq_sym; apply H.
      (* step *)
      eapply objs_not_unborn_op; eauto.
      Qed.


      Theorem Proper_objs_not_unborn : 
        Proper (RefSet.Subset --> Sys.eq ==> impl) objs_not_unborn.
      Proof.
        unfold Proper; unfold respectful; unfold impl; unfold flip; intros.
        unfold objs_not_unborn in *.
        intros e Hin.
        eapply H in Hin. 
        generalize (H1 e Hin); clear H1; intros H1.
        intro Hnot. apply H1.
        eapply SC.isLabel_eq; 
          [ apply Ref.eq_refl | apply ObjectLabel.eq_refl | apply Sys.eq_sym; apply H0 | apply Hnot].
      Qed.

      Ltac try_solve_potAcc_op_id_case Hp_objs Hp'_objs Hunborn2:=
        let Heq := fresh "Heq" in
          try solve [ generalize (ag_objs_spec_equiv _ _ _ _ Hp_objs Hp'_objs (AG.eq_refl _)); intros Heq;
            eapply Proper_objs_not_unborn; unfold flip; 
              [ apply RefSetProps.subset_equal; apply RefSet.eq_sym; apply Heq
                | apply Sys.eq_refl | apply Hunborn2]].

        Theorem ag_objs_spec_insert: forall p p_objs,  Seq.ag_objs_spec p p_objs ->
          forall a n p'_objs, Seq.ag_objs_spec (insert a n p) p'_objs ->
            RefSet.eq p'_objs (RefSet.add a (RefSet.add n p_objs)).
        Proof.
          intros.
          unfold insert in *.

          generalize (Seq.ag_objs_spec_ag_objs (ag_add_cap a (Cap.mkCap n all_rights) p)).
          generalize (Seq.ag_objs (ag_add_cap a (Cap.mkCap n all_rights) p)).
          intros mid_objs Hmid_objs.

          rewrite ag_objs_spec_add_cap_equiv_nonempty with (objs':=p'_objs); 
            [ rewrite CC.mkCap_target
              | apply Hmid_objs
              | rewrite CC.mkCap_rights; intro Hnot; apply Hnot with tx; eapply in_all_rights
              | apply H0
            ].

          rewrite ag_objs_spec_add_cap_equiv_nonempty with (objs':=mid_objs); 
            [ rewrite CC.mkCap_target
              | apply H
              | rewrite CC.mkCap_rights; intro Hnot; apply Hnot with tx; eapply in_all_rights
              | apply Hmid_objs
            ].

          rewrite RefSetAddEq.double_add;
            rewrite RefSetProps.add_add;
              rewrite RefSetAddEq.double_add.
          eapply RefSet.eq_refl.
        Qed.

      Theorem ag_objs_spec_endow: forall p p_objs, Seq.ag_objs_spec p p_objs ->
        forall a n p'_objs, Seq.ag_objs_spec (endow a n p) p'_objs ->
          RefSet.eq p'_objs (RefSet.add a (RefSet.add n p_objs)).
      Proof.
        intros. unfold endow in *.
        generalize (Seq.potAcc_potAcc_fun (insert a n p)); intros Hpa.
        destruct Hpa as [Htrans _].
        eapply ag_objs_spec_potTransfer in Htrans; eauto. 
        eapply ag_objs_spec_equiv in H0; [ | apply Htrans | apply AG.eq_refl].
        rewrite <- H0 in *.
        clear H0 Htrans; clear p'_objs.
        eapply ag_objs_spec_insert; eauto.
      Qed.


        Theorem getLabel_addCap_map_eq_inline: forall r i c o s,
          option_map_eq ObjectLabel.eq (SC.getLabel r (SC.addCap i c o s)) (SC.getLabel r s).
        Proof.
          intros.
          generalize (option_map_eq_Equiv _ ObjectLabelEQ); intros [EQ_refl EQ_sym EQ_trans].
          eapply EQ_sym.
          eapply SC.getLabel_addCap_map_eq; eapply eq_refl.
        Qed.

        Theorem getLabel_copyCapList_map_eq_inline: forall s o t ixi_list i_src,
          option_map_eq ObjectLabel.eq (SC.getLabel i_src (SC.copyCapList o t ixi_list s)) (SC.getLabel i_src s).
        Proof.
          intros.
          generalize (option_map_eq_Equiv _ ObjectLabelEQ); intros [EQ_refl EQ_sym EQ_trans].
          eapply EQ_sym; eapply SC.getLabel_copyCapList_map_eq; eapply eq_refl.
        Qed.

      Theorem is_label_allocate_not_unborn : forall lbl, ~ ObjectLabel.eq lbl unborn ->
        forall x s, SC.is_label x s lbl ->
        forall a t t' l s', Sys.eq (Sem.do_allocate a t t' l s) s' ->
        SC.is_label x s' lbl.
      Proof.
        intros.
        case (SemDefns.allocate_preReq_dec a t s); intros Hcase;
          (eapply Sys.eq_trans in H1; 
            [ 
              | eapply Sys.eq_sym; solve 
                [eapply Sem.allocate_valid; eauto 
                  | eapply Sem.allocate_invalid; eauto]]);
        try solve[ eapply SC.isLabel_eq; [ apply Ref.eq_refl| apply ObjectLabel.eq_refl | apply H1 | apply H0]].
        (* allocate occrus*)
        generalize Hcase; intros [[Halive Hactive] Hunborn].
        eapply SC.is_label_iff_getLabel in Halive.
        eapply SC.is_label_iff_getLabel in Hunborn.
        eapply SC.is_label_iff_getLabel in H0.
        unfold SC.is_label.
        generalize (SC.getLabel_eq _ _ _ _ (Ref.eq_refl x) H1); intros Heq; clear H1.

        (* this the main theorem what we want, how do we instantiate EQ options, playing with ones I can find*)

        generalize (option_map_eq_Equiv _ ObjectLabelEQ); intros [EQ_refl EQ_sym EQ_trans].
        unfold Transitive in *.
        eapply EQ_trans in Heq;[|eapply EQ_sym; eapply getLabel_addCap_map_eq_inline].
        eapply EQ_trans in Heq;[|eapply EQ_sym; eapply getLabel_copyCapList_map_eq_inline].
        unfold SC.set_alive in *.

        case (Ref.eq_dec x t); intros Hcase2; [unfold Ref.eq in Hcase2; rewrite Hcase2 in *|].
        (* x = t *)
        rewrite SC.getLabel_set_label_eq_o in Heq; try apply Ref.eq_refl.
        rewrite SC.getLabel_updateObj_o in Heq.
        rewrite SC.getLabel_rmCapsByTarget_o in Heq.
        rewrite H0 in *.
        inversion Hunborn as [Hlbl].
        rewrite Hlbl in H.
        generalize (H (ObjectLabel.eq_refl _)); intros; contradiction.
        (* x <> t *)
        rewrite SC.getLabel_set_label_neq_o in Heq; auto.
        rewrite SC.getLabel_updateObj_o in Heq.
        rewrite SC.getLabel_rmCapsByTarget_o in Heq.
        
        (* there should really be a theorem for this *)
        rewrite H0 in *.
        case (option_sumbool (SC.getLabel x s')) as [Hcase3 | [lbl' Hcase3]]; 
          rewrite Hcase3 in *; simpl in *; auto.
        rewrite Heq. apply ObjectLabel.eq_refl.
      Qed.

      Theorem is_label_allocate_new_label : forall a t s, SemDefns.allocate_preReq a t s ->
        forall t2 l s', Sys.eq (Sem.do_allocate a t t2 l s) s' ->
        SC.is_label t s' alive.
      Proof.
        intros a t s Hprereq t2 l s' Heq.
        generalize Hprereq; intros [[Halive Hactive] Hunborn].
        eapply SC.is_label_iff_getLabel in Halive.
        eapply SC.is_label_iff_getLabel in Hunborn.
        eapply SC.is_label_iff_getLabel.
        eapply Sys.eq_trans in Heq; [|eapply Sys.eq_sym; eapply Sem.allocate_valid; auto].
        generalize (SC.getLabel_eq _ _ _ _ (Ref.eq_refl t) Heq); clear Heq; intros Heq.

        generalize (option_map_eq_Equiv _ ObjectLabelEQ); intros [EQ_refl EQ_sym EQ_trans].
        unfold Transitive in *.

        eapply EQ_trans in Heq;[|eapply EQ_sym; eapply getLabel_addCap_map_eq_inline].
        eapply EQ_trans in Heq;[|eapply EQ_sym; eapply getLabel_copyCapList_map_eq_inline].
        unfold SC.set_alive in *.

        rewrite SC.getLabel_set_label_eq_o in Heq; try apply Ref.eq_refl.
        rewrite SC.getLabel_updateObj_o in Heq.
        rewrite SC.getLabel_rmCapsByTarget_o in Heq.
        rewrite Hunborn in *.

        case (option_sumbool (SC.getLabel t s')) as [Hcase3 | [lbl' Hcase3]]; 
          rewrite Hcase3 in *; simpl in *; auto; try contradiction.
        rewrite Heq. apply eq_refl.
      Qed.

    Theorem objs_not_unborn_potAcc_op: forall p p_objs, Seq.ag_objs_spec p p_objs ->
      forall s, objs_not_unborn p_objs s ->
      forall op p'_objs, Seq.ag_objs_spec (potAcc_op op s p) p'_objs ->
      forall s', Sys.eq (Sem.do_op op s) s' ->
      objs_not_unborn p'_objs s'.
    Proof.
      intros p p_objs Hp_objs s Hp_objs_unborn op p'_objs Hp'_objs s' Hsys_eq.
      generalize (objs_not_unborn_op _ _ Hp_objs_unborn _ _ Hsys_eq); intros Hunborn2.

      destruct op; simpl in *; unfold id_ag in *;
        try_solve_potAcc_op_id_case Hp_objs Hp'_objs Hunborn2.
      unfold endow_dep in *.
      revert Hp'_objs; case (SemDefns.allocate_preReq_dec t t0 s); intros Hcase Hp'_objs;
        try_solve_potAcc_op_id_case Hp_objs Hp'_objs Hunborn2.

      eapply Proper_objs_not_unborn; unfold flip; 
        [ eapply RefSetProps.subset_equal; eapply ag_objs_spec_endow; [apply Hp_objs | apply Hp'_objs ]
          | eapply Sys.eq_refl
          |].
      clear Hp'_objs Hp_objs_unborn Hp_objs.
      unfold objs_not_unborn in *.
      intros x Hin.
      eapply RefSetProps.Add_add in Hin.
      destruct Hin as [Hin | Hin].
      (* t = x *)
      rewrite Hin in *.
      generalize Hcase; intros [[Halive Hactive] Hunborn].

      eapply is_label_allocate_not_unborn in Halive; [ | intro Hnot; discriminate Hnot| apply Hsys_eq].
      intro Hnot.
      unfold SC.is_unborn in *.
      eapply SC.is_label_iff_getLabel in Hnot.
      eapply SC.is_label_iff_getLabel in Halive.
      rewrite Halive in Hnot.
      discriminate.

      eapply RefSetProps.Add_add in Hin.
      destruct Hin as [Hin|Hin].
      (* t0 = x *)
      rewrite Hin in *.
      generalize Hcase; intros [[Halive Hactive] Hunborn].

      idtac.
      generalize Hcase; intros Halive'.
      eapply is_label_allocate_new_label in Halive'; [ | eapply Hsys_eq].
      eapply SC.is_label_iff_getLabel in Halive'. unfold SC.is_unborn.  intro Hnot. 
      eapply SC.is_label_iff_getLabel in Hnot.
      rewrite Halive' in Hnot.
      discriminate Hnot.

      (* induction hypothesis *)
      eapply Hunborn2; eauto.
    Qed.


    Theorem objs_not_unborn_potAcc_execute_spec: forall p p_objs, Seq.ag_objs_spec p p_objs ->
      forall s,  objs_not_unborn p_objs s ->
      forall op_list Fp', potAcc_execute_spec op_list Fp' -> 
      forall Fp'_objs, Seq.ag_objs_spec (Fp' s p) Fp'_objs ->
      forall s', Exe.execute_def s op_list s' ->
      objs_not_unborn Fp'_objs s'.
    Proof.
      intros p p_objs Hp_objs s Hp_objs_unborn op_list Fp' Hpax.
      induction Hpax; intros Fp'_objs HFp'_objs s' Hexe.
      eapply ag_objs_spec_equiv in Hp_objs; [ | apply HFp'_objs | apply AG.eq_refl ].
      inversion Hexe.
      red; intros. eapply Hp_objs in H0. eapply Hp_objs_unborn in H0.
      intros Hnot; apply H0.
      eapply SC.isLabel_eq;
        [ eapply Ref.eq_refl | eapply ObjectLabel.eq_refl | eapply Sys.eq_sym; eapply H | eapply Hnot].
    (* step *)
      unfold compose in *.
      inversion Hexe.
      generalize (Seq.ag_objs_spec_ag_objs (Fp s p)); generalize (Seq.ag_objs (Fp s p)); intros ag_objs' Hag_objs'.
      eapply objs_not_unborn_potAcc_op; 
        [apply Hag_objs'
          | 
          | apply HFp'_objs
          |
        ]; [eapply IHHpax; eauto;  eapply Exe.execute_spec; eapply Sys.eq_refl|].
      
      inversion Hexe.
      eapply Exe.execute_spec in H6.
      eapply Sys.eq_trans; [ | eapply H8].
      eapply SemConv.do_op_eq.
      eapply H6.
    Qed.


    Theorem potAcc_execute_spec_potAcc: forall p, Seq.maxTransfer p ->
      forall op_list Fp', potAcc_execute_spec op_list Fp' -> forall s, Seq.maxTransfer (Fp' s p).
    Proof.
      intros p Hmax op_list Fp' Hpax s.
      induction Hpax; eauto.
    (* step *)
      unfold compose.
      unfold potAcc_op.
      destruct op; unfold id_ag; simpl;
      (* eliminate 7 cases of identity transformation *) auto.

      unfold endow_dep.
      case (SemDefns.allocate_preReq_dec t t0 (Exe.execute s op_list)); intros Hcase; 
        (* eliminate 1/2 case of id_ag *) auto.
      unfold endow.
      generalize Seq.potAcc_potAcc_fun; intros Hpa.
      edestruct Hpa as [Htrasn Hmax']. eapply Seq.maxTransfer_maxPotTransfer in Hmax'. apply Hmax'.
    Qed.

    Theorem objs_not_unborn_dirAcc_spec: forall s i, dirAcc_spec s i ->
      forall objs, Seq.ag_objs_spec i objs -> objs_not_unborn objs s.
    Proof.
      intros.
      (* introduce contradiciton *)
      unfold objs_not_unborn; intros n Hin Hunborn.
      (* work through objs_spec *)
      eapply H0 in Hin; clear H0; destruct Hin as [obj [rgt [HinE | HinE ]]];
      (* cases *)
      (* apply dirAcc in HinE and destruct*)
      eapply H in HinE;
      destruct_dirAcc HinE s'' HeqS src_ref src lbl srcType srcSched HmapS 
      src' lbl' srcType' srcSched' HeqP Halive ind cap HmapSrc'
      cap_obj cap_lbl cap_type cap_sched HmapScap cap_obj' cap_lbl' cap_type' cap_sched' 
      HeqPcap HaliveCap rgt' HinR HeqEdge;
      (* simplify edge equality *)
      generalize (Edges.eq_source _ _ HeqEdge); intros HeqEdgeS; 
        repeat progress rewrite Edges.source_rewrite in HeqEdgeS;
          generalize (Edges.eq_target _ _ HeqEdge); intros HeqEdgeT;
            repeat progress rewrite Edges.target_rewrite in HeqEdgeT;
            generalize (Edges.eq_right _ _ HeqEdge); intros HeqEdgeR;
              repeat progress rewrite Edges.right_rewrite in HeqEdgeR;
      (* simplify tuple equality *)
      destruct_tuple HeqP Hsrc Hlbl HsrcT HsrcS; simpl in *;
      destruct_tuple HeqPcap Hsrc_cap Hlbl_cap HsrcT_cap HsrcS_cap; simpl in *;
      (* rewrite everything through to show that n is alive in hyp HmapS | HmapScap. *)
      rewrite HeqEdgeS in *;
      rewrite HeqEdgeT in *;
      rewrite Hlbl in *;
      rewrite Hlbl_cap in *;
      unfold ObjectLabel.eq in *;
      rewrite <- Halive in *;
      rewrite <- HaliveCap in *.

      (* use HmapS to find an equivelent label in s *)
      eapply Sys_MapEquiv.exists_mapsTo_eq in HmapS;
        [ | apply Sys.eq_sym; apply HeqS | apply Ref.eq_refl].
      destruct HmapS as [tuple [Htuple HmapS]].
      destruct_tuple tuple t_obj t_lbl t_schd t_typ; simpl in *.
      destruct_tuple Htuple Ht_obj Ht_lbl Ht_schd Ht_typ.
      rewrite <- Ht_lbl in *.
      (* prove contradiciton by discrimination *)
      unfold SC.is_unborn in Hunborn.
      unfold SC.is_label in Hunborn.
      unfold SC.getLabel in Hunborn.
      unfold SC.getObjTuple in Hunborn.
      eapply Sys.MapS.find_1 in HmapS.
      rewrite HmapS in Hunborn.
      simpl in Hunborn.
      discriminate.

      (* other case *)

      (* use HmapScap to find an equivelent label in s *)
      eapply Sys_MapEquiv.exists_mapsTo_eq in HmapScap;
        [ | apply Sys.eq_sym; apply HeqS | apply Ref.eq_refl].
      destruct HmapScap as [tuple [Htuple HmapScap]].
      destruct_tuple tuple t_obj t_lbl t_schd t_typ; simpl in *.
      destruct_tuple Htuple Ht_obj Ht_lbl Ht_schd Ht_typ.
      rewrite <- Ht_lbl in *.
      (* prove contradiciton by discrimination *)
      unfold SC.is_unborn in Hunborn.
      unfold SC.is_label in Hunborn.
      unfold SC.getLabel in Hunborn.
      unfold SC.getObjTuple in Hunborn.
      eapply Sys.MapS.find_1 in HmapScap.
      rewrite HmapScap in Hunborn.
      simpl in Hunborn.
      discriminate.
    Qed.


    (* throw into sequential access *)
    Theorem maxTransfer_potAcc_refl : forall p, Seq.maxTransfer p -> Seq.potAcc p p.
    Proof.
      intros; split.
      eapply Seq.potTransfer_base; apply AG.eq_refl.
      eapply Seq.maxTransfer_maxPotTransfer; auto.
    Qed.


Theorem AG_attenuating_potAcc_op_2: forall objs s, objs_not_unborn objs s -> 
  forall i p, Seq.potAcc i p -> 
  forall ag_N, Seq.ag_objs_spec p ag_N -> objs_not_unborn ag_N s ->
    forall op, AG_attenuating objs p (potAcc_op op s p).
Proof.
  intros objs s Hobjs i p Hpa ag_N Hag_objs Hag_objs_unborn op.
  destruct op; simpl; try unfold id_ag; try solve [apply AG_attenuating_eq; apply AG.eq_refl].
  unfold endow_dep.
  case (SemDefns.allocate_preReq_dec t t0 s); intros H'; try solve [apply AG_attenuating_eq; apply AG.eq_refl].
  destruct H'.
  eapply AG_attenuating_endow; try solve [ apply Hag_objs | apply Hpa
| intro Hnot; first [apply Hobjs in Hnot|apply Hag_objs_unborn in Hnot]; apply Hnot; auto].
Qed.

  Theorem AG_attenuating_compose: forall objs p Fp1, AG_attenuating objs p (Fp1 p) ->
    forall Fp2, AG_attenuating objs (Fp1 p) (compose Fp2 Fp1 p) ->
    AG_attenuating objs p (compose Fp2 Fp1 p).
  Proof.
    intros.
    eapply AG_attenuating_trans; [ apply H | apply H0].
  Qed.


(* This theorem states that the function Fp, which conservatively approximates the execution
   of op_list on s, is AG_attenuating-ing on its input provided all objs are unborn. *)

Theorem execute_potAcc_attenuating: 
     forall op_list Fsa, dirAcc_execute_spec op_list Fsa ->
     forall Fp, potAcc_execute_spec op_list Fp ->
     forall s i, dirAcc_spec s i -> forall p, Seq.potAcc i p ->
     forall objs, objs_not_unborn objs s ->
     AG_attenuating objs p (Fp s p).
Proof.
  intros op_list Fsa Hdax Fp Hpax s i Hda p Hpa objs Hobjs.
  revert Hdax Hpax; revert Fsa Fp.
  induction op_list; intros Fsa Fp Hdax Hpax.

  (* base *)
  
  inversion Hpax; eauto.

  (* step *)

  rename a into op.
  inversion Hdax. rename Fp0 into Fsa'. clear H H1. clear op0 op_list0.
  inversion Hpax. rename Fp0 into Fp'. clear H H3. clear op0 op_list0.

  generalize (IHop_list _ _ H2 H4); intros IHreduce; clear IHop_list.

  apply AG_attenuating_compose; [apply IHreduce|].
  unfold compose.

  (* generalize (exists_dirAcc_spec (Exe.execute s op_list)); intros [i' Hda']. *)
  (* generalize (Seq.exists_potAcc i'); intros [p' Hpa']. *)
  (* generalize (Seq.ag_objs_spec_ag_objs p'); intros Hagobjs. *)
  (* generalize (objs_not_unborn_oplist _ _ Hobjs op_list _  (Exe.execute_spec_2 s op_list _ (Sys.eq_refl _))); intros Hobjsunborn. *)

(* okay, aside from the potAcc property, all of these subgoals are about the objs_not_unborn invariants *)
(* first, we need to know that objs not unborn remain not unborn over execution.
   second, we need to know that no objs produced by a potAcc_execute_spec funcitons also preserve 
   objs_obj_unborn *)

eapply AG_attenuating_potAcc_op_2.
(* objs unborn in Exe.execute s op_list *) 
  eapply objs_not_unborn_oplist; [apply Hobjs| eapply Exe.execute_spec_2; apply Sys.eq_refl].
(* potAcc_execute_spec op_list Fp' -> exists da, Seq.potAcc da (Fp' s p) *)
  eapply maxTransfer_potAcc_refl; eapply potAcc_execute_spec_potAcc; [ | eauto];
    destruct Hpa as [HpotTrans Hmax]; eapply Seq.maxTransfer_maxPotTransfer in Hmax; auto.
(* ag_objs_spec *)
eapply Seq.ag_objs_spec_ag_objs.
(* potAcc_execute_spec op_list Fp' -> objs_not_unborn (Seq.ag_objs (Fp' s p)) (Exe.execute s op_list) *)
eapply objs_not_unborn_potAcc_execute_spec; eauto; [|apply Exe.execute_spec; eapply Sys.eq_refl].
generalize (Seq.ag_objs_spec_ag_objs p); intros Hp_objs.
eapply ag_objs_spec_potTransfer_2 in Hp_objs; [ | eapply Hpa].
eapply objs_not_unborn_dirAcc_spec; eauto.
Qed.

(* Given execute_potAcc_attenuating, we can now turn to execute_attenuatinge *)

  Theorem execute_attenuating : forall s i, dirAcc_spec s i -> forall p, Seq.potAcc i p ->
    forall op_list s', Exe.execute_def s op_list s' -> forall i', dirAcc_spec s' i' ->
      forall p', Seq.potAcc i' p' -> forall objs, objs_not_unborn objs s ->
        AG_attenuating objs p p'.
  Proof.
    intros s i Hda p Hpa op_list s' Hexe i' Hda' p' Hpa' objs HnAlive.
    (* proof sketch *)
    (* by  dirAcc_execute_spec_dirAcc_execute and potAcc_execute_spec_potAcc_execute, we know that we can
       instantiate  execute_potAcc_attenuating*)
    generalize (execute_potAcc_attenuating
      op_list 
      _ (dirAcc_execute_spec_dirAcc_execute _)
      _ (potAcc_execute_spec_potAcc_execute _)
      _ _ Hda
      _ Hpa
      _ HnAlive); intros Hreduce.

    
    eapply Proper_AG_attenuating_4; unfold flip;
      [ apply RefSetProps.subset_equal; apply RefSet.eq_refl
        | apply AGProps.subset_equal; apply AG.eq_refl
        |
        | apply Hreduce
      ].

    (* all that remains is to show that potAcc_execute conservatively approximates potAcc *) 
    generalize (potAcc_execute_approx 
      op_list
      _ (dirAcc_execute_spec_dirAcc_execute _)
      _ (potAcc_execute_spec_potAcc_execute _)); intros HPAapprox.
    generalize (dirAcc_execute_approx
      op_list
      _ (dirAcc_execute_spec_dirAcc_execute _)); intros HDAapprox.
    unfold dirAcc_approx_dep in *.
    unfold potAcc_approx_dirAcc_dep in *.
    eapply Exe.execute_spec in Hexe.
    eapply dirAcc_spec_iff in Hda'; [ | apply Hexe| apply AG.eq_refl].
    
    generalize (HDAapprox _ _ _ _ _ 
      Hda Hda' (AGProps.subset_equal (AG.eq_refl _)) (Sys.eq_refl _)); 
    clear HDAapprox; intros HDAapprox.
    generalize (Seq.exists_potAcc (dirAcc_execute op_list s i)); intros [p2 Hpa2].
    generalize (HPAapprox _ _ _ _ _ _ _ _ 
      (Sys.eq_refl _) (Sys.eq_refl _)
      Hda (AGProps.subset_equal (AG.eq_refl _))
      Hpa Hpa2
      (AGProps.subset_equal (AG.eq_refl _)));
    clear HPAapprox; intros HPAapprox.
    
    eapply AGProps.subset_trans;[|eapply HPAapprox].

    eapply Seq.potAcc_monotonic; [ apply HDAapprox | apply Hpa'| apply Hpa2].
    Qed.







End MakeAccessExecution.

