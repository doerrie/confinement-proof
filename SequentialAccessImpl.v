Require Import Decidable.
Require Import References.
Require Import AccessRights.
Require Import OrderedTypeEx.
Require Import OptionSumbool.
Require Import Sumbool.
Require Import Sumbool_dec.
Require Import AccessEdge.
Require Import AccessGraphs.
Require FSets.
Require FSetFacts.
Require FSetEqProperties.
Require FSetAddEq.
Require FSetBridge.
Require Import RefSets.
Require Minus.
Require Plus.
(* type_remove *)
Require Import SequentialAccess.

(* Sequential Access is the notion of how to directly relate one access graph to another. *)

Set Implicit Arguments.

Module MakeSeqAcc (Ref : ReferenceType) (RefS: RefSetType Ref) (Edges: AccessEdgeType Ref) (AccessGraph: AccessGraphType Ref Edges) : SeqAccType Ref RefS Edges AccessGraph.

(*  Module AccessGraph := AccessGraphs.Make Ref. *)

  Import AccessGraph.

(*  Module RefSet_Mod := RefSets.Make Ref.
  Import RefSet_Mod. *)
Import RefS.

(*  Require FSetBridge.
  Module AGDep := FSetBridge.DepOfObjp AG. *)


  Inductive transfer (a b : AG.t) : Prop :=
  | transfer_self_src : forall (rgt rgt': accessRight) (src tgt:Ref.t),
    AG.In (Edges.mkEdge src tgt rgt) a ->
    AGProps.Add (Edges.mkEdge src src rgt') a b ->
    transfer a b
  | transfer_self_tgt : forall (rgt rgt': accessRight) (src tgt:Ref.t),
    AG.In (Edges.mkEdge src tgt rgt) a -> 
    AGProps.Add (Edges.mkEdge tgt tgt rgt') a b ->
    transfer a b
  | transfer_read : forall (rgt: accessRight) (src tgt tgt':Ref.t),
    AG.In (Edges.mkEdge src tgt rd) a -> 
    AG.In (Edges.mkEdge tgt tgt' rgt) a -> 
    AGProps.Add (Edges.mkEdge src tgt' rgt) a b ->
    transfer a b
  | transfer_write : forall (rgt: accessRight) (src tgt tgt':Ref.t),
    AG.In (Edges.mkEdge src tgt wr) a -> 
    AG.In (Edges.mkEdge src tgt' rgt) a -> 
    AGProps.Add (Edges.mkEdge tgt tgt' rgt) a b ->
    transfer a b
  | transfer_send : forall (rgt: accessRight) (src tgt tgt':Ref.t),
    AG.In (Edges.mkEdge src tgt tx) a -> 
    AG.In (Edges.mkEdge src tgt' rgt) a -> 
    AGProps.Add (Edges.mkEdge tgt tgt' rgt) a b ->
    transfer a b
  | transfer_send_reply : forall (src tgt:Ref.t),
    AG.In (Edges.mkEdge src tgt tx) a -> 
    AGProps.Add (Edges.mkEdge tgt src tx) a b ->
    transfer a b
  | transfer_weak : forall (rgt: accessRight) (src tgt tgt':Ref.t),
    AG.In (Edges.mkEdge src tgt wk) a -> 
    AG.In (Edges.mkEdge tgt tgt' rgt) a -> 
    (eq rgt wk \/ eq rgt rd) ->
    AGProps.Add (Edges.mkEdge src tgt' wk) a b ->
    transfer a b.

  Hint Constructors transfer.

  Theorem transfer_edge : 
    forall (a b:AG.t), transfer a b -> 
      exists edge:Edge.t,
        (AGProps.Add edge a b).
  Proof.
    intros.
    destruct H;
      esplit;
        eauto.
  Qed.

  Hint Resolve transfer_edge.

  (* Moved Add_Subset to FSetAddEq *)
  Hint Resolve AGAddEq.Add_Subset.

  Theorem transfer_subset :
    forall (a b:AG.t), transfer a b -> AG.Subset a b.
  Proof.
    intros a b H.
    destruct H;
    eauto.
  Qed.

(* For antisym, find out how the FSet material plays in with In *)

  Hint Resolve transfer_subset.

  Theorem transfer_antisym:
    forall (a b : AG.t), transfer a b -> transfer b a -> AG.Equal a b.
  Proof.
    intros a b H H0.
    generalize transfer_subset H0.
    intros H1 H2.
    generalize (H1 a b H).
    generalize (H1 b a H0).
    unfold AG.Equal.
    unfold AG.Subset.
    intuition.
  Qed.

  Hint Resolve transfer_antisym.

  Theorem transfer_not_Add:
    forall (A B :AG.t), ~ (exists edge:Edge.t, AGProps.Add edge A B) -> ~ transfer A B.
  Proof.
    intuition.
  Qed.

  Theorem transfer_not_subset:
    forall (a b :AG.t), ~ AG.Subset a b -> ~ transfer a b.
  Proof.
    intros a b H.
    auto with *.
  Qed.

  Hint Resolve AGProps.equal_sym.
  Hint Immediate AGProps.equal_refl.

  Theorem transfer_equality_full: forall (a a' b b':AG.t),
    AG.Equal a a' -> AG.Equal b b' -> transfer a b -> transfer a' b'.
  Proof.
    intros a a' b b' HeqA HeqB Htrans.
    destruct Htrans as [rgt rgt' src tgt Hin1 Hadd1 | 
      rgt rgt' src tgt Hin1 Hadd1| 
        rgt src tgt tgt' Hin1 Hin2 Hadd1|
          rgt src tgt tgt' Hin1 Hin2 Hadd1|
            rgt src tgt tgt' Hin1 Hin2 Hadd1|
              src tgt Hin1 Hadd1|
                rgt src tgt tgt' Hin1 Hin2 Hright Hadd1];
    generalize (AGAddEq.Add_eq_full _ _ _ _ _ HeqA HeqB Hadd1);
      generalize (AGAddEq.In_eq_full _ _ _ HeqA Hin1);
        try generalize (AGAddEq.In_eq_full _ _ _ HeqA Hin2); intros; intuition eauto.
    Qed.

    Hint Resolve transfer_equality_full.

  Theorem transfer_equality: forall (a b b':AG.t),
    transfer a b -> AG.Equal b b' -> transfer a b'.
  Proof.
    intros.
    destruct H; eauto.
  (* was: 
       destruct H; eauto with *. 
       Returns:
Toplevel input, characters 39-51:
Anomaly: uncaught exception Failure "Cannot print a global reference".
Please report.
*)
  Qed.

  Hint Resolve transfer_equality.


  Inductive potTransfer (a c:AG.t) : Prop :=
  | potTransfer_base :  AG.Equal a c -> potTransfer a c
  | potTransfer_trans : forall (b:AG.t), potTransfer a b -> transfer b c -> potTransfer a c.

  Hint Constructors potTransfer.

  Theorem potTransfer_reflexive:
    forall (a:AG.t), potTransfer a a.
  Proof.
    intros.
    apply potTransfer_base.
    apply AGProps.equal_refl.
  Qed.
  
  Hint Immediate potTransfer_reflexive.

  Theorem potTransfer_equality_full: forall a a' b b',
   AG.Equal a a' -> AG.Equal b b' -> potTransfer a b -> potTransfer a' b'.
  Proof.
    intros.
    revert H H0. revert a' b'.
    induction H1; intros.
    eapply potTransfer_base.
    eapply AG.eq_trans.
      eapply AG.eq_sym; apply H0.
      eapply AG.eq_trans.
        eapply H.
        eauto.
    eapply potTransfer_trans.
      eapply IHpotTransfer; auto.
      eapply transfer_equality_full; eauto.
  Qed.

(* add this later, it's mucking up tauto *)
  Hint Resolve potTransfer_equality_full.

  Theorem potTransfer_refl_equal:
    forall (a b c:AG.t),
      potTransfer a b -> AG.Equal b c -> potTransfer a c.
  Proof.
    intros.
    eapply potTransfer_equality_full; eauto.
  Qed.

  Hint Resolve potTransfer_refl_equal.

  Theorem potTransfer_transitive:
    forall (a b c:AG.t), potTransfer a b -> potTransfer b c -> potTransfer a c.
  Proof.
    intros a b c H1 H2.
    induction H2; eauto.
  Qed.

  Hint Resolve potTransfer_transitive.

  Theorem potTransfer_subset:
    forall (a b:AG.t), potTransfer a b -> AG.Subset a b.
  Proof.
    intros a b H.
    induction H.
    generalize (AGProps.double_inclusion a c); intros H1; destruct H1 as [H2 H3]; destruct H2; eauto.
    generalize (transfer_subset H0); intro H1.
    unfold AG.Subset in *; intuition.
  Qed.

  Hint Resolve potTransfer_subset.

  (* This is the best we can do for the time being.  We can not deduce
     AG.Equal a c -> a = c without some lifting. *)

  Theorem potTransfer_antisym:
    forall (a c: AG.t), potTransfer a c -> potTransfer c a -> AG.Equal a c.
  Proof.
    intros a c H H0.
    generalize (potTransfer_subset H).
    generalize (potTransfer_subset H0).
    intros H1 H2.
    unfold AG.Equal.
    unfold AG.Subset in *.
    intuition.
  Qed.

  Hint Resolve potTransfer_antisym.

  Theorem potTransfer_In:
    forall (a b:AG.t) (edge:Edge.t), potTransfer a b -> AG.In edge a -> AG.In edge b.
  Proof.
    intros.
    generalize (potTransfer_subset H).
    unfold AG.Subset in *.
    intuition.
  Qed.
  
  Hint Resolve potTransfer_In.

  Theorem transfer_monotonic: forall (i a b c : AG.t) (edge: Edge.t),
    AG.Subset i b -> AGProps.Add edge i a -> transfer i a -> AGProps.Add edge b c -> transfer b c.
  Proof.
    intros.
    destruct H1.
  (* we know that we can (transfer b c) in this case, since:
     1. AG.In (Edges.mkEdge src tgt rgt) i -> AG.Subset i b -> AG.In (Edges.mkEdge src tgt rgt) b
     2. Subset i b ->
        Add edge  i a ->
        Add edge  b c ->
        Add edge' i a ->
        Add edge' b c.

     *)
    constructor 1 with rgt rgt' src tgt; eauto.
    
(*    
    e' = (Edges.mkEdge src src rgt')
    F.Subset  A B -> Properties.Add x    A A' -> Properties.Add x    B B' -> Properties.Add x' A A' -> Properties.Add x' B B'
    AG.Subset i b -> AGProps.Add    edge i a  -> AGProps.Add    edge b c  -> AGProps.Add    e' i a  -> AGProps.Add    e' b c
    
    This is all present, what is going on?  THis should just eapply.
  
  *)    
    apply AGAddEq.Subset_Add with edge i a; intuition eauto.
    constructor 2 with rgt rgt' src tgt; eauto.
    apply AGAddEq.Subset_Add with edge i a; intuition eauto.
    constructor 3 with rgt src tgt tgt'; eauto.
    apply AGAddEq.Subset_Add with edge i a; intuition eauto.
    constructor 4 with rgt src tgt tgt'; eauto.
    apply AGAddEq.Subset_Add with edge i a; intuition eauto.
    constructor 5 with rgt src tgt tgt'; eauto.
    apply AGAddEq.Subset_Add with edge i a; intuition eauto.
    constructor 6 with src tgt; eauto.
    apply AGAddEq.Subset_Add with edge i a; intuition eauto.
    constructor 7 with rgt src tgt tgt'; eauto.
    apply AGAddEq.Subset_Add with edge i a; intuition eauto.
  Qed.

  Hint Resolve transfer_monotonic.

  Theorem potTransfer_add_transfer: forall (i a b c : AG.t) (edge: Edge.t),
    transfer i a -> potTransfer i b -> AGProps.Add edge i a -> AGProps.Add edge b c -> transfer b c.
  Proof.
    intros.
    eauto.
  Qed.

  Theorem transfer_lub: forall (i a b:AG.t),
    transfer i a -> transfer i b -> exists c:AG.t, transfer a c /\ transfer b c.
  Proof.
    intros i a b Tia Tib.
    generalize (transfer_edge Tia); intro Aia; generalize (transfer_edge  Tib); intro Aib.
    destruct Aia as [Eia Aia]; destruct Aib as [Eib Aib].
    assert (exists c:AG.t, AGProps.Add Eib a c) as Hadd; eauto.
    destruct Hadd as [c Hadd].
    apply ex_intro with c.
    split; [eauto|].
    assert (AGProps.Add Eia b c); eauto.
    eapply AGAddEq.Add_lub; eauto.
  Qed.

  Hint Resolve transfer_lub.

  Theorem potTransfer_transfer_lub: forall (i a b:AG.t),
    potTransfer i a -> transfer i b -> exists c:AG.t, transfer a c /\ potTransfer b c.
  Proof.
    intros.
    induction H as[|a a' H H1 H2].
    eapply ex_intro; eauto.
    destruct H1 as [c' H1].
    destruct H1 as [H1 H3].
    generalize (transfer_lub H2 H1).
    intro H4.
    destruct H4 as [c H4]; destruct H4 as [H4 H5];
      apply ex_intro with c;
        eauto.
  Qed.

  Hint Resolve potTransfer_transfer_lub.
    

  Theorem potTransfer_lub:
    forall (i a b: AG.t), potTransfer i a -> potTransfer i b -> exists c : AG.t, potTransfer b c /\ potTransfer a c.
  Proof.
    intros.
    induction H as [a H1 | a a' H3 H4 H5].
    induction H0; [split with i; intuition | split with c; intuition; eauto].
    destruct H4 as [c' H6]; destruct H6 as [H7 H8].
    generalize (potTransfer_transfer_lub H8 H5). intros H.
    destruct H as [c [H H1]].
    apply ex_intro with c.
    split; eauto.
  Qed.


  Definition maxTransfer (i:AG.t) : Prop := forall a:AG.t, transfer i a -> AG.Equal i a.

  Definition maxPotTransfer (i:AG.t) : Prop := forall a:AG.t, potTransfer i a -> AG.Equal i a.

  Theorem maxTransfer_maxPotTransfer: forall (i:AG.t),  maxTransfer i <-> maxPotTransfer i.
  Proof.
    intros; split; intros; unfold maxTransfer in *; unfold maxPotTransfer in *; intros a H0.
    induction H0; [auto | assert (transfer i c); eauto].
    induction H0; eauto.
  Qed.

  (* TODO: Look up if this needs to be Resolve to work, or if Immediate will do. *)
  Hint Resolve maxTransfer_maxPotTransfer.

  Definition potAcc (i max:AG.t) : Prop := potTransfer i max /\ maxPotTransfer max.

  Hint Unfold potAcc.

  Theorem potAcc_potTransfer: forall (i:AG.t) (a max:AG.t), potTransfer i a -> potAcc a max -> potAcc i max.
  Proof.
    intros; induction H; unfold potAcc in H0; destruct H0; split; eauto.
  Qed.

  Hint Resolve potAcc_potTransfer. 

  Theorem potAcc_maxPotTransfer: forall (max:AG.t), maxPotTransfer max -> potAcc max max.
  Proof.
    eauto.
  Qed.

  Hint Resolve potAcc_maxPotTransfer.  

(* The above 2 thms reduces the problem to searching things that are potTransferable.
   In order to make a decision procedure, we would need to know that there are a finite number
   of transable edges, construct a potTransfer of them all, and instantiate that. *)

(* There are a finite number of edges in a complete graph *)
(* a complete graph is a maximal graph *)
(* As we potTransfer a b, where ~ a [=] b, we get closer to the complete graph *)
(* for any i, either i is maximal or exists a:AG.t, ~ a [=] i /\ potTransfer i a getting us closer to a complete graph. *)

  (* prove that there are only so many potential edges on any graph *)
  (* show that this number decreases with each transfer not equal *)
  (* use this to distance to potAcc *)
  (* we should know that (maxPotTransfer max) is decidable. *)
  (* Prove: ~ maxPotTransfer a -> exists b:AG.t, ~ AG.Equal a b -> potTransfer a b. *)
  (* Given the above, we can always find one more edge to forward chain to maxPotTransfer from i
     and compute potAcc incrementally. *)

(*   Module RefSet := FSetList.Make Ref. *)
(*   Module RefProps := FSetProperties.Properties RefSet. *)
(*   Module RefFacts := FSetFacts.Facts RefSet. *)
(*   Module RefDep := FSetBridge.DepOfObjp RefSet. *)
(*   Module RefEqProps := FSetEqProperties.EqProperties RefSet. *)
(*   Module RefAddEq := FSetAddEq.Make RefSet. *)

  Definition obj_fold (edge:Edge.t) (refs:RefSet.t) : RefSet.t := 
    RefSet.add (Edges.source edge) (RefSet.add (Edges.target edge) refs).

  Definition ag_objs (i:AG.t) := AG.fold obj_fold i RefSet.empty.

  Definition ag_objs_spec (i:AG.t) (objs: RefSet.t) := forall x, 
    RefSet.In x objs <->
    (exists obj, exists rgt, (AG.In (Edges.mkEdge x obj rgt) i) \/ (AG.In (Edges.mkEdge obj x rgt) i)).

  Definition AG_all_objs (i:AG.t) (objs: RefSet.t):= (forall (src tgt:Ref.t) (rgt:accessRight),
    AG.In (Edges.mkEdge src tgt rgt) i -> RefSet.In src objs /\ RefSet.In tgt objs).

  Theorem compat_op_obj_fold: forall (edge edge': Edge.t) (refs refs': RefSet.t),
    AG.E.eq edge edge' -> RefSet.Equal refs refs' ->
    RefSet.Equal (obj_fold edge refs) (obj_fold edge' refs').
  Proof.
    intros.
    unfold obj_fold.
    apply RefSetAddEq.add_equal_complete; try apply RefSetAddEq.add_equal_complete; 
      try first [apply Edges.eq_target | apply Edges.eq_source]; auto.
  Qed.
  
  Hint Resolve compat_op_obj_fold.
  
  Theorem transpose_ag_objs_full: forall (e e': Edge.t) (refs refs' :RefSet.t),
    RefSet.Equal refs refs' ->
    RefSet.Equal (obj_fold e (obj_fold e' refs)) (obj_fold e' (obj_fold e refs')).
  Proof.
    unfold obj_fold; unfold RefSet.Equal; intros; RefSetFacts.set_iff; generalize (H a); tauto.
  Qed.

  Hint Resolve transpose_ag_objs_full.

(*  Hint Resolve potTransfer_equality_full. *)

  Theorem ag_objs_spec_ag_objs: forall i, ag_objs_spec i (ag_objs i).
  Proof.
    unfold ag_objs; unfold ag_objs_spec; intros.
    eapply AGProps.fold_rec_bis with (P:= fun i n => 
    RefSet.In x n <->
      (exists obj : Ref.t,
         exists rgt : accessRight,
           AG.In (Edges.mkEdge x obj rgt) i \/ AG.In (Edges.mkEdge obj x rgt) i)) .
   (* compat op *)
   intros; eapply iff_trans; [eapply H0|
   split; intro Heq;
   (destruct Heq as [obj [rgt Hin]]; do 2 eapply ex_intro;
   destruct Hin as [Hin | Hin]; [left|right];
   eapply H; eauto)].
   (* base *)
   split; intro Hin; [|destruct Hin as [obj [rgt [Hin|Hin]]]];
   first [eapply RefSet.empty_1 in Hin | eapply AG.empty_1 in Hin]; contradiction.
   (* step *)
   intros edge objs i'; intros.
   unfold obj_fold.
   (* 3 cases: x[=](source edge), x[=](target edge), neiter. *)
   case (Ref.eq_dec x (Edges.source edge)); intros Hsource.
   split; intro Hin.
   (* in -> exists *)
   eapply ex_intro with (Edges.target edge); eapply ex_intro with (Edges.right edge).
   rewrite Hsource; rewrite Edges.edge_rewrite; left; eapply AGProps.Add_add; left; auto.
   (* exists -> in *)
   rewrite Hsource; repeat progress (eapply RefSetProps.Add_add; auto; right).
   case (Ref.eq_dec x (Edges.target edge)); intros Htarget.
   split; intro Hin.
   (* in -> exists *)
   eapply ex_intro with (Edges.source edge); eapply ex_intro with (Edges.right edge).
   rewrite Htarget; rewrite Edges.edge_rewrite; intuition (eapply AGProps.Add_add; auto).
   (* exists -> in *)
   rewrite Htarget; repeat progress (eapply RefSetProps.Add_add; auto; right).
   (* neither case *)
   (* in -> exists *)
   split; intros Hin.
   eapply RefSetProps.Add_add in Hin. destruct Hin as [Hin | Hin]; [rewrite Hin in *; generalize (Hsource (Ref.eq_refl _)); contradiction|].
   eapply RefSetProps.Add_add in Hin. destruct Hin as [Hin | Hin]; [rewrite Hin in *; generalize (Htarget (Ref.eq_refl _)); contradiction|].
   eapply H1 in Hin. destruct Hin as [obj [rgt Hin]].
   eapply ex_intro with obj; eapply ex_intro with rgt.
   destruct Hin as [Hin | Hin]; [left|right]; eapply AGProps.Add_add; eauto.
   (* exists -> in *)
   do 2 (eapply RefSetProps.Add_add; right). eapply H1.
   destruct Hin as [obj [rgt [Hin |Hin]]]; do 2 eapply ex_intro; [left|right];
     (eapply AGProps.Add_add in Hin; destruct Hin as [Hin | Hin]; 
       [simpl in *; destruct Hin as [Hin_s [Hin_t Hin_r]]; 
         eapply Ref.eq_sym in Hin_s; eapply Ref.eq_sym in Hin_t;
         first [eapply Hsource in Hin_s | eapply Htarget in Hin_t];contradiction | eauto]).
  Qed.

  Hint Resolve ag_objs_spec_ag_objs.

  Theorem ag_objs_spec_AG_all_objs: forall i n,
    ag_objs_spec i n -> AG_all_objs i n.
  Proof.
    unfold ag_objs_spec; unfold AG_all_objs; intros.
    split; [eapply (H src)| eapply (H tgt)];
    do 2 eapply ex_intro; intuition eauto.
  Qed.

  Hint Resolve ag_objs_spec_AG_all_objs.

  Theorem AG_all_objs_ag_objs : forall (i:AG.t),
    AG_all_objs i (ag_objs i).
  Proof.
    intros; auto.
  Qed.

  Theorem AG_objs_equal: forall A objs,
    AG_all_objs A objs -> 
    forall edge, RefSet.In (Edges.source edge) objs -> RefSet.In (Edges.target edge) objs ->
      forall A', AGProps.Add edge A A' -> AG_all_objs A' objs.
  Proof.
    intros.
    unfold AG_all_objs in *.
    intros.
    case (Edge.eq_dec edge (Edges.mkEdge src tgt rgt)); intros.
    unfold Edges.AccessEdge.eq in e.
    destruct e as [Hsrc Hmore].
    destruct Hmore as [Htgt Hrgt].
    simpl in *.
    unfold Edges.source in H0.
    unfold Edges.target in H1.
    rewrite Hsrc in *.
    rewrite Htgt in *.
    auto.
  
    generalize (H2 (Edges.mkEdge src tgt rgt)); intros Hadd; destruct Hadd as [Hadd Hadd'].
    apply Hadd in H3.
    destruct H3.
    contradiction.
    apply H with (rgt:=rgt). auto.
  Qed.



  Theorem compat_op_ag_objs: forall i i', AG.Equal i i' -> RefSet.Equal (ag_objs i) (ag_objs i').
  Proof.
    intros.
    unfold ag_objs.
    apply AGProps.fold_equal with (eqA:=RefSet.Equal); eauto.
    exact RefSetFacts.Equal_ST.
    unfold SetoidList.transpose; intros; apply transpose_ag_objs_full; apply RefSetProps.equal_refl.
  Qed.

  Hint Resolve compat_op_ag_objs.


  Definition add_obj_fold_P i := forall src tgt, 
    RefSet.In src (ag_objs i) -> RefSet.In tgt (ag_objs i) ->
    forall rgt,
      RefSet.Equal (ag_objs i) (ag_objs (AG.add (Edges.mkEdge src tgt rgt) i)).
  
  Theorem add_obj_fold_P_compat_op: forall i i', AG.Equal i i' ->
    add_obj_fold_P i -> add_obj_fold_P i'.
  Proof.
    unfold add_obj_fold_P.
    intros i i' H H0 src tgt H1 H2 rgt.
    generalize (compat_op_ag_objs H); intros Hequal.
    apply Hequal in H1.
    apply Hequal in H2.
    generalize (H0 _ _ H1 H2 rgt).
    intros HeqI.
    generalize (AGFacts.add_m (Edge.eq_refl (Edges.mkEdge src tgt rgt)) H); intros HeqAdd.
    apply RefSetProps.equal_trans with (ag_objs i); auto.
    apply RefSetProps.equal_trans with (ag_objs (AG.add (Edges.mkEdge src tgt rgt) i)); auto.
  Qed.
  
  Theorem not_In_ag_objs_empty: forall n, ~ RefSet.In n (ag_objs AG.empty).
  Proof.
    intros.
    unfold ag_objs.
    rewrite (AGEqProps.fold_empty).
    apply RefSet.empty_1.
  Qed.
  
  Hint Resolve not_In_ag_objs_empty.

  Theorem obj_fold_simpl : forall src refs, RefSet.In src refs -> 
    forall tgt, RefSet.In tgt refs ->
      forall rgt, RefSet.Equal (obj_fold (Edges.mkEdge src tgt rgt) refs) refs.
  Proof.
    intros.
    unfold obj_fold.
    simpl.
    unfold RefSet.Equal.
    intros a.
    RefSetFacts.set_iff.

    intuition.
    rewrite <- H2; auto.
    unfold Edges.target in H1; rewrite <- H1. auto.

  Qed.

  Theorem obj_fold_simpl_eq: forall src refs, RefSet.In src refs -> 
    forall tgt, RefSet.In tgt refs ->
      forall refs', RefSet.Equal refs refs' ->
        forall rgt, RefSet.Equal (obj_fold (Edges.mkEdge src tgt rgt) refs') refs.
  Proof.
    intros.
    generalize (compat_op_obj_fold (Edge.eq_refl (Edges.mkEdge src tgt rgt)) H1); intros.
    apply RefSetProps.equal_sym in H2.
    eapply RefSetProps.equal_trans; [apply H2| apply obj_fold_simpl]; auto.
  Qed.

  Theorem add_obj_fold_P_ag_objs : forall i, add_obj_fold_P i.
  Proof.
    intros.
    unfold add_obj_fold_P.
    intros.
    case (AGProps.In_dec (Edges.mkEdge src tgt rgt) i); intros Hin.
    apply compat_op_ag_objs; apply AGProps.equal_sym; apply AGProps.add_equal; trivial.

    unfold ag_objs.

    assert 
      (let x := (Edges.mkEdge src tgt rgt) in
        let s := (AG.add x i) in
        (RefSet.Equal
          (obj_fold x (AG.fold obj_fold (AG.remove x s) RefSet.empty))
          (AG.fold obj_fold s RefSet.empty))); simpl; try simpl in H1.
    apply AGProps.remove_fold_1 with  (s:=(AG.add (Edges.mkEdge src tgt rgt) i)).
    apply RefSetFacts.Equal_ST.
    Require Import Morphisms.
    unfold SetoidList.compat_op; unfold Proper; unfold respectful; intros;  apply compat_op_obj_fold; auto.
    unfold SetoidList.transpose; intros; apply transpose_ag_objs_full; apply RefSetProps.equal_refl.
    apply AG.add_1; auto.
    eapply RefSetProps.equal_trans; [clear H1|apply H1].
    generalize (AGProps.remove_add Hin); intros Hobjs.
    apply compat_op_ag_objs in Hobjs.
    apply compat_op_obj_fold with (edge:=(Edges.mkEdge src tgt rgt)) (edge':=(Edges.mkEdge src tgt rgt)) in Hobjs; [|apply Edge.eq_refl].
    apply RefSetProps.equal_sym.
    eapply RefSetProps.equal_trans.
    apply Hobjs.
    clear Hobjs.
    apply obj_fold_simpl; assumption.
  Qed.


(* This is the inner fold for a complete access graph *)

  Definition complete_ag_fold_src (src tgt:Ref.t)(acc:AG.t) : AG.t :=
    AG.add (Edges.mkEdge src tgt wk) 
    (AG.add (Edges.mkEdge src tgt rd)
     (AG.add (Edges.mkEdge src tgt wr)
      (AG.add (Edges.mkEdge src tgt tx) acc))).

  Definition AG_all_rights (src tgt:Ref.t) (A:AG.t) := forall rgt:accessRight,
    AG.In (Edges.mkEdge src tgt rgt) A.

  Hint Unfold AG_all_rights.

  Theorem eq_complete_ag_fold_src_full: 
    forall (src src' tgt tgt':Ref.t) (acc acc' acc1 acc2 acc3 result:AG.t),
      Ref.eq src src' ->
      Ref.eq tgt tgt' ->
      AG.Equal acc acc' ->
      AGProps.Add (Edges.mkEdge src tgt tx) acc acc1 ->
        AGProps.Add (Edges.mkEdge src tgt wr) acc1 acc2 ->
          AGProps.Add (Edges.mkEdge src tgt rd) acc2 acc3 ->
            AGProps.Add (Edges.mkEdge src tgt wk) acc3 result ->
              AG.Equal (complete_ag_fold_src src' tgt' acc') result.
  Proof.
    intros.
    unfold complete_ag_fold_src.
    apply AGAddEq.Add_add; apply AGAddEq.Eq_Add_Add with acc3; auto;
      [apply AG.eq_sym | eapply AGAddEq.Add_Eq_Add; eauto; eapply Edges.edge_equal; eauto; 
        try apply AccessRight.eq_refl].
    apply AGAddEq.Add_add; apply AGAddEq.Eq_Add_Add with acc2; auto; 
      [apply AG.eq_sym | eapply AGAddEq.Add_Eq_Add; eauto; eapply Edges.edge_equal; eauto;
        try apply AccessRight.eq_refl].
    apply AGAddEq.Add_add; apply AGAddEq.Eq_Add_Add with acc1; auto; 
      [apply AG.eq_sym | eapply AGAddEq.Add_Eq_Add; eauto; eapply Edges.edge_equal; eauto;
        try apply AccessRight.eq_refl].
    apply AGAddEq.Add_add; auto; eapply AGAddEq.Add_eq_full; eauto;
      eapply AGAddEq.Add_Eq_Add; eauto; eapply Edges.edge_equal; eauto; 
        try apply AccessRight.eq_refl.
  Qed.


  Theorem eq_complete_ag_fold_src: forall (src tgt:Ref.t) (acc acc1 acc2 acc3 result:AG.t),
    AGProps.Add (Edges.mkEdge src tgt tx) acc acc1 ->
      AGProps.Add (Edges.mkEdge src tgt wr) acc1 acc2 ->
        AGProps.Add (Edges.mkEdge src tgt rd) acc2 acc3 ->
          AGProps.Add (Edges.mkEdge src tgt wk) acc3 result ->
            AG.Equal (complete_ag_fold_src src tgt acc) result.
  Proof.
    intros.
    eapply eq_complete_ag_fold_src_full;
      [apply Ref.eq_refl | apply Ref.eq_refl | apply AGProps.equal_refl| | | | ]; eauto.
  Qed.

  Theorem eq_complete_ag_fold_src_2: forall (src tgt tgt':Ref.t) (acc acc1 acc2 acc3 result:AG.t),
    Ref.eq tgt tgt' ->
    AGProps.Add (Edges.mkEdge src tgt tx) acc acc1 ->
      AGProps.Add (Edges.mkEdge src tgt wr) acc1 acc2 ->
        AGProps.Add (Edges.mkEdge src tgt rd) acc2 acc3 ->
          AGProps.Add (Edges.mkEdge src tgt wk) acc3 result ->
            AG.Equal (complete_ag_fold_src src tgt' acc) result.
  Proof.
    intros.
    eapply eq_complete_ag_fold_src_full;
      [apply Ref.eq_refl | apply H | apply AGProps.equal_refl| | | | ]; eauto.
  Qed.

  Theorem eq_complete_ag_fold_src_3: forall (src tgt tgt':Ref.t) (acc acc' acc1 acc2 acc3 result:AG.t),
    Ref.eq tgt tgt' ->
    AG.Equal acc acc' ->
    AGProps.Add (Edges.mkEdge src tgt tx) acc acc1 ->
      AGProps.Add (Edges.mkEdge src tgt wr) acc1 acc2 ->
        AGProps.Add (Edges.mkEdge src tgt rd) acc2 acc3 ->
          AGProps.Add (Edges.mkEdge src tgt wk) acc3 result ->
            AG.Equal (complete_ag_fold_src src tgt' acc') result.
  Proof.
    intros.
    eapply eq_complete_ag_fold_src_full;
      [apply Ref.eq_refl | apply H | apply H0 | | | | ]; eauto.
  Qed.

  Theorem compat_op_complete_ag_fold_src: forall (y y':AG.t) (x x' src:Ref.t),
    Ref.eq x x' -> AG.Equal y y' ->
    AG.Equal (complete_ag_fold_src src x y) (complete_ag_fold_src src x' y').
  Proof.
    intros.
    eapply eq_complete_ag_fold_src_3;
      [apply Ref.eq_sym; apply H |
        apply AGProps.equal_sym; apply H0|eauto|eauto|eauto|unfold complete_ag_fold_src;eauto].
  Qed.

  Hint Resolve compat_op_complete_ag_fold_src.


  Theorem transpose_complete_ag_fold_src_full2: forall (src src': Ref.t) (refs refs' : RefSet.elt) (A A' : AG.t),
    AG.Equal A A' ->
    AG.Equal (complete_ag_fold_src src refs (complete_ag_fold_src src' refs' A))
    (complete_ag_fold_src src' refs' (complete_ag_fold_src src refs A')).
  Proof.
    unfold complete_ag_fold_src; unfold AG.Equal; intros; AGFacts.set_iff.
    generalize (H a); intros H'; destruct H' as [H'1 H'2].
    tauto.
  Qed.

  Theorem transpose_complete_ag_fold_src_full: forall (src src': Ref.t) (refs refs' : RefSet.elt) (A : AG.t),
    AG.Equal (complete_ag_fold_src src refs (complete_ag_fold_src src' refs' A))
    (complete_ag_fold_src src' refs' (complete_ag_fold_src src refs A)).
  Proof.
    intros.
    eapply transpose_complete_ag_fold_src_full2.
    exact (AGProps.equal_refl A).
  Qed.

  Hint Resolve transpose_complete_ag_fold_src_full.

  Theorem transpose_complete_ag_fold_src: forall (src : Ref.t) (refs refs' : RefSet.elt) (A : AG.t),
    AG.Equal (complete_ag_fold_src src refs (complete_ag_fold_src src refs' A))
    (complete_ag_fold_src src refs' (complete_ag_fold_src src refs A)).
  Proof.
    intros.
    eapply transpose_complete_ag_fold_src_full.
  Qed.

  Hint Resolve transpose_complete_ag_fold_src.

  Theorem in_complete_ag_fold_src : forall (src tgt:Ref.t) (rgt:accessRight) (A:AG.t),
    AG.In (Edges.mkEdge src tgt rgt)
     (complete_ag_fold_src src tgt A).
  Proof.
    intros.
    destruct rgt;
    unfold complete_ag_fold_src;
    AGFacts.set_iff; intuition auto.
  Qed.

  Hint Resolve in_complete_ag_fold_src.

  Theorem fold_AG_all_rights: forall (src tgt:Ref.t) (acc:AG.t),
    AG_all_rights src tgt (complete_ag_fold_src src tgt acc).
  Proof.
    intros.
    unfold AG_all_rights.
    intros.
    unfold complete_ag_fold_src.
    destruct rgt;
      repeat first [apply AG.add_1; eapply Edge.eq_refl | apply AGAddEq.elim_In_add].
  Qed.

  Hint Resolve fold_AG_all_rights.

  Theorem complete_ag_fold_src_acc : forall src tgt tgt' rgt acc, 
    AG.In (Edges.mkEdge src tgt rgt) (complete_ag_fold_src src tgt' acc) ->
    ~ Ref.eq tgt tgt' ->
    AG.In (Edges.mkEdge src tgt rgt) acc.
  Proof.
    intros src tgt tgt' rgt acc H Heq.
    unfold complete_ag_fold_src in H.
    do 4 (apply AG.add_3 in H; simpl; auto; 
      try solve [intro F; destruct F as [F1 F2]; destruct F2 as [F2 F3]; rewrite F2 in Heq; apply Heq; apply Ref.eq_refl]).
  Qed.

  Require SetoidList.


(* In this section, we focus on the second fold *)


  Definition complete_ag_fold (allRefs:RefSet.t) (src:Ref.t) (acc:AG.t):=
    RefSet.fold (complete_ag_fold_src src) allRefs acc.

  Definition AG_all_target_rights (src:Ref.t) (refs:RefSet.t) (A:AG.t) := 
    forall (tgt:Ref.t)(rgt:accessRight), RefSet.In tgt refs -> AG.In (Edges.mkEdge src tgt rgt) A.

  Definition AG_in_target_refs (src:Ref.t) (refs:RefSet.t) (acc A:AG.t) := 
    forall (tgt:Ref.t)(rgt:accessRight), AG.In (Edges.mkEdge src tgt rgt) A ->
      ~ AG.In (Edges.mkEdge src tgt rgt) acc -> RefSet.In tgt refs.

  Hint Unfold AG_all_target_rights AG_in_target_refs.

  Theorem fold_AG_all_target_rights: forall (src:Ref.t) (refs:RefSet.t) (acc:AG.t),
    AG_all_target_rights src refs (complete_ag_fold refs src acc).
  Proof.
    intros.
    unfold AG_all_target_rights.
    intros.
    unfold complete_ag_fold.
    assert (let f:=(complete_ag_fold_src src) in 
      (AG.Equal 
      (f tgt (RefSet.fold f (RefSet.remove tgt refs) acc)) (RefSet.fold f refs acc))).
    simpl.
    apply RefSetProps.remove_fold_1 with (eqA:=AG.Equal); eauto.
(* no longer needed *)
(*    exact AGFacts.Equal_ST. *)
    (* compat_op is automated *)
    (* transpose is automated *)
    simpl in H0.
    red in H0.
    generalize (H0 (Edges.mkEdge src tgt rgt)); intros H1.
    destruct H1 as [H1 H2].
    apply H1.
    auto.
  Qed.

  Theorem fold_AG_in_target_refs: forall (src:Ref.t) (refs:RefSet.t) (acc:AG.t),
    AG_in_target_refs src refs acc (complete_ag_fold refs src acc).
  Proof.
    intros.
    unfold complete_ag_fold.
    eapply RefSetProps.fold_rec_bis with (P:=fun refs A, AG_in_target_refs src refs acc A).
    (* Equality section *)
    unfold AG_in_target_refs.
    intros.
    generalize (H tgt); intros Hin.
    destruct Hin as [Hin _].
    apply Hin; apply H0 with rgt; auto.
    (* Base case *)
    unfold AG_in_target_refs.
    intros.
    contradiction.
    (* Induction step *)
    intros tgt' acc' s' H H0 H1.
    unfold AG_in_target_refs in *.
    intros tgt rgt H2 H3.
    (* either tgt = tgt' or not *)
    (* if so, then add_1, else, reduce to in tgt s' *)
    (* in edge (complete_ag_fold_src src tgt' acc') -> in edge acc' *)
    (* apply IH (H1) with tgt rgt, qed. *)
    case (Ref.eq_dec tgt tgt'); intros Heq.
    apply RefSet.add_1; auto.
    (* neq case *)
    assert (~ Ref.eq tgt' tgt) as Heq'; 
      [ red; intros Hiseq; apply Heq; apply Ref.eq_sym; auto |
        clear Heq; rename Heq' into Heq].
    generalize (RefSetFacts.add_neq_iff s' Heq); intros Hin; 
      let Hdc := fresh H in destruct Hin as [Hdc Hin]; clear Hdc; apply Hin; clear Hin.
    (* apply IH *)
    apply H1 with rgt; auto.
    apply complete_ag_fold_src_acc with tgt'; auto.
    intros Hnot; apply Heq.
    eapply Ref.eq_sym; auto.
  Qed.

(* In this section, we focus on the outer fold. *)


  Definition complete_ag (refs:RefSet.t):=
    RefSet.fold (complete_ag_fold refs) refs AG.empty.
      
  Definition complete_AG (refs:RefSet.t) (full:AG.t) : Prop :=
    forall (src tgt:Ref.t)(rgt:accessRight), 
      RefSet.In src refs -> RefSet.In tgt refs -> AG.In (Edges.mkEdge src tgt rgt) full.

  Definition foldAGEqual (f : Ref.t -> AG.t -> AG.t) (f' : Ref.t -> AG.t -> AG.t) :=
    RefSetFold.foldEqual AG.Equal f f'.

  Theorem foldAGEqual_complete_ag_fold_src :
    forall (src src' : Ref.t),
      Ref.eq src src' ->
      foldAGEqual (complete_ag_fold_src src) (complete_ag_fold_src src').
  Proof.
    intros.
    unfold foldAGEqual.
    intros.
    unfold RefSetFold.foldEqual; intros.
    eapply eq_complete_ag_fold_src_full;
      [apply Ref.eq_sym; apply H | 
        apply Ref.eq_sym; apply H1 |
          apply AG.eq_sym; apply H0 | 
            eauto | eauto | eauto | 
              unfold complete_ag_fold_src; eauto].
  Qed.

  Theorem compat_op_complete_ag_fold: forall (acc acc':AG.t) (src src':Ref.t) (refs refs':RefSet.t),
    RefSet.Equal refs refs' -> Ref.eq src src' -> AG.Equal acc acc' ->
    AG.Equal (complete_ag_fold refs src acc) (complete_ag_fold refs' src' acc').
  Proof.
    intros.
    unfold complete_ag_fold.
    apply (RefSetFold.fold_foldEqual _ _ AGFacts.Equal_ST); auto.
    unfold RefSetFold.foldEqual; intros.
    apply foldAGEqual_complete_ag_fold_src; auto.
  Qed.

  Theorem equal_complete_fold_fold_src : forall (src src' tgt : Ref.t) (refs:List.list Ref.t) (acc:AG.t),
    AG.Equal
    (complete_ag_fold_src src tgt (List.fold_right (complete_ag_fold_src src') acc refs))
    (List.fold_right (complete_ag_fold_src src') (complete_ag_fold_src src tgt acc) refs).
  Proof.
    intros.
    induction refs as [|obj refs]; auto.
    simpl in *.
    (* 1. swap
       (complete_ag_fold_src src tgt (complete_ag_fold_src src' obj ...)) with
       (complete_ag_fold_src src' obj (complete_ag_fold_src src tgt ...)) 
       *)
    generalize (transpose_complete_ag_fold_src_full src src' tgt obj
      (List.fold_right (complete_ag_fold_src src') acc refs)).
    intro H; eapply AGProps.equal_trans; [apply H| clear H].
    (* 2. apply IHrefs to produce rewrite:
       (complete_ag_fold_src src tgt
         (complete_ag_fold_src src' obj
           (List.fold_right (complete_ag_fold_src src') acc refs)))
         to:
       (complete_ag_fold_src src' obj
         (List.fold_right (complete_ag_fold_src src')
           (complete_ag_fold_src src tgt acc) refs)
       *)
    apply compat_op_complete_ag_fold_src; [apply Ref.eq_refl|assumption].
  Qed.

  Theorem transpose_complete_ag_fold: 
    forall (refs: RefSet.t) (x y: Ref.t) (acc: AG.t),
      AG.Equal (complete_ag_fold refs x (complete_ag_fold refs y acc))
      (complete_ag_fold refs y (complete_ag_fold refs x acc)).
  Proof.
    intros.
    unfold complete_ag_fold.
      (* first we need to rewrite all of this in terms of list and elements folding *)
      (* this turns out to be hard, as the rewrite and replace tactics are not on our side due to equivelences*)
    Set Printing All.

(*    unfold AG.t. *)
    generalize (RefSet.fold_1 refs acc (complete_ag_fold_src y)); intros.
    replace (@RefSet.fold AG.t (complete_ag_fold_src y) refs acc) with
      (@List.fold_left AG.t RefSet.elt
        (fun (a : AG.t) (e : RefSet.elt) => complete_ag_fold_src y e a)
        (RefSet.elements refs) acc).
    clear H.
    generalize (RefSet.fold_1 refs (List.fold_left
      (fun (a : AG.t) (e : RefSet.elt) => complete_ag_fold_src y e a)
      (RefSet.elements refs) acc) (complete_ag_fold_src x)); intros.
    replace (@RefSet.fold AG.t (complete_ag_fold_src x) refs
      (@List.fold_left AG.t RefSet.elt
        (fun (a : AG.t) (e : RefSet.elt) => complete_ag_fold_src y e a)
        (RefSet.elements refs) acc)) with
    (@List.fold_left AG.t RefSet.elt
      (fun (a : AG.t) (e : RefSet.elt) =>
        complete_ag_fold_src x e a) (RefSet.elements refs)
      (@List.fold_left AG.t RefSet.elt
        (fun (a : AG.t) (e : RefSet.elt) =>
          complete_ag_fold_src y e a) (RefSet.elements refs) acc)).
    clear H.
    generalize (RefSet.fold_1 refs acc (complete_ag_fold_src x)); intros.
    replace (@RefSet.fold AG.t (complete_ag_fold_src x) refs acc) with
      (@List.fold_left AG.t RefSet.elt
        (fun (a : AG.t) (e : RefSet.elt) => complete_ag_fold_src x e a)
        (RefSet.elements refs) acc).
    clear H.
    generalize (RefSet.fold_1 refs (List.fold_left
      (fun (a : AG.t) (e : RefSet.elt) => complete_ag_fold_src x e a)
      (RefSet.elements refs) acc) (complete_ag_fold_src y)); intros.
    replace (@RefSet.fold AG.t (complete_ag_fold_src y) refs
      (@List.fold_left AG.t RefSet.elt
        (fun (a : AG.t) (e : RefSet.elt) =>
          complete_ag_fold_src x e a) (RefSet.elements refs) acc)) with
    (@List.fold_left AG.t RefSet.elt
      (fun (a : AG.t) (e : RefSet.elt) => complete_ag_fold_src y e a)
      (RefSet.elements refs)
      (@List.fold_left AG.t RefSet.elt
        (fun (a : AG.t) (e : RefSet.elt) =>
          complete_ag_fold_src x e a) (RefSet.elements refs) acc)).
    Unset Printing All.
    clear H.

    destruct refs as [refs sorted].
    simpl.
    clear sorted.
    (* reduce to pure lists *)
    unfold AG.t.
    unfold RefSet.MSet.Raw.t in *.
    unfold RefSet.MSet.Raw.elt in *.
    (* Not needed in v8.2 *)
    (* unfold RefSet.E.t in *. *)
    unfold RefSet.elt in *.

    (* reverse refs and fold_left to fold_right so induction aligns, eliminate (rev refs) *)
    
    generalize (List.fold_left_rev_right (complete_ag_fold_src y) refs acc); intros H; unfold AG.t in H; rewrite <- H; clear H.
    generalize (List.fold_left_rev_right (complete_ag_fold_src x) refs acc); intros H; unfold AG.t in H; rewrite <- H; clear H.
    generalize (List.fold_left_rev_right (complete_ag_fold_src y) refs (List.fold_right (complete_ag_fold_src x) acc (List.rev refs))); 
      intros H; unfold AG.t in H; rewrite <- H; clear H.
    generalize (List.fold_left_rev_right (complete_ag_fold_src x) refs (List.fold_right (complete_ag_fold_src y) acc (List.rev refs))); 
      intros H; unfold AG.t in H; rewrite <- H; clear H.
    
    generalize (List.rev refs); clear refs; intros refs.

    (* the proof should now appear as straightforward induction on refs *)

    induction refs as [|hd refs]; simpl.
    apply AGProps.equal_refl.

    (* in the above theorem, fully instantiated (complete_ag_fold_src [x|y] hd ... ) operations reduce to adding edges. *)
    (* This is equal to a series of 4 outer adds, an outer fold, 4 inner adds, and an inner fold. *)
    (* if we can show that we can move the inner adds out from the outer fold, we can apply our induction hypothesis *)
    (* We obviously can, but this will probably be easier with another theorem.  *)
    (* our best approach is to demonstrate that an add can be moved, and then a complete_ag_fold_src can *)

    generalize (equal_complete_fold_fold_src x y hd refs (List.fold_right (complete_ag_fold_src x) acc refs)); intro HmvX.
    generalize (equal_complete_fold_fold_src y x hd refs (List.fold_right (complete_ag_fold_src y) acc refs)); intro HmvY.

    (* now do the actual move *)
    
    generalize (compat_op_complete_ag_fold_src x (Ref.eq_refl hd) HmvY). intro Hmv.
    eapply AGProps.equal_trans.
    apply AGProps.equal_sym.
    apply Hmv.

    generalize (compat_op_complete_ag_fold_src y (Ref.eq_refl hd) HmvX). intro Hmv'.
    apply AGProps.equal_sym.
    eapply AGProps.equal_trans.
    apply AGProps.equal_sym.
    apply Hmv'.

    clear Hmv Hmv' HmvX HmvY.
    
    apply transpose_complete_ag_fold_src_full2.
    apply AGProps.equal_sym.
    assumption.
  Qed.


  Theorem fold_AG_complete_ag: forall (refs:RefSet.t),
    complete_AG refs (complete_ag refs).
  Proof.
    intros.
    unfold complete_AG.
    intros.
    unfold complete_ag.
    assert (let f:= (complete_ag_fold refs) in
      (AG.Equal
        (f src (RefSet.fold f (RefSet.remove src refs) AG.empty)) (RefSet.fold f refs AG.empty))).
    simpl. 
    apply RefSetProps.remove_fold_1 with (eqA:=AG.Equal); eauto.
(*     exact AGFacts.Equal_ST. *)
    unfold SetoidList.compat_op.
    intros.
    unfold Proper; unfold respectful. intros.
    apply compat_op_complete_ag_fold.
    apply RefSetProps.equal_refl.
    unfold RefSet.E.eq in H1; assumption.
    assumption.
    unfold SetoidList.transpose.
    intros.
    eapply transpose_complete_ag_fold.
    simpl in H1.
    red in H1.
    generalize (H1 (Edges.mkEdge src tgt rgt)); intros H2.
    destruct H2 as [H2 H3].
    apply H2.
    apply fold_AG_all_target_rights.
    assumption.
  Qed.


  Definition AG_in_source_refs (refs:RefSet.t) (acc A:AG.t) := 
    forall (src tgt:Ref.t)(rgt:accessRight), AG.In (Edges.mkEdge src tgt rgt) A ->
      ~ AG.In (Edges.mkEdge src tgt rgt) acc -> RefSet.In src refs.

  Theorem complete_ag_fold_src_not_target : forall src src', ~ Ref.eq src src' ->
    forall tgt tgt' rgt acc, AG.In (Edges.mkEdge src tgt rgt) (complete_ag_fold_src src' tgt' acc) ->
      AG.In (Edges.mkEdge src tgt rgt) acc.
  Proof.
    intros.
    unfold complete_ag_fold_src in *.

    let destructive :=red; 
      let Hnot := fresh Hnot in intros Hnot;
        let Hnot1 := fresh Hnot in destruct Hnot as [Hnot Hnot1]; auto in
          let attempt := try (rewrite Hnot in H; apply H; apply Ref.eq_refl) in
          do 4 (apply AG.add_3 in H0; [auto;attempt |simpl; destructive]);attempt.
  Qed.
  
  Theorem complete_ag_fold_not_source: forall refs src tgt rgt src' acc, ~ Ref.eq src src' -> 
    AG.In (Edges.mkEdge src tgt rgt) (complete_ag_fold refs src' acc) ->
    AG.In (Edges.mkEdge src tgt rgt) acc.
  Proof.
    intros refs src tgt rgt src' acc H.
    unfold complete_ag_fold in *.
    apply RefSetProps.fold_rec_bis with 
      (f:=(complete_ag_fold_src src'))
      (s:=refs); [intros; auto|intros;auto|].
    intros.
    apply complete_ag_fold_src_not_target in H3; auto.
  Qed.
   

  Theorem AG_in_source_refs_complete_ag_fold: 
    forall refs acc,
      AG_in_source_refs refs acc (RefSet.fold (complete_ag_fold refs) refs acc).
  Proof.
    intros.
    apply RefSetProps.fold_rec_bis with (P:=fun refs A, AG_in_source_refs refs acc A).
    (*equiv op*)
    intros.
    unfold AG_in_source_refs in *; intros.
    generalize (H0 src tgt rgt H1 H2); intros Hin.
    apply H in Hin; tauto.
    (* base case *)
    unfold AG_in_source_refs; intros.
    contradiction.
    (* inductive step *)
    unfold  AG_in_source_refs.
    intros src' acc' s' H H0 IH src tgt rgt H1 H2.
    (* focus on src for a moment *)
    (* if src <> src', then it is not possible for complete_ag_fold refs src' acc' to add edge *)
    (* we may need to prove this *)
    (* this should give us In edge acc', then apply IH and end subgoal. *)
    case (Ref.eq_dec src' src); intros HeqS.
    apply RefSet.add_1; auto.
    generalize (RefSetFacts.add_neq_iff s' HeqS); intros Hin; 
      let Hdc := fresh H in destruct Hin as [Hdc Hin]; clear Hdc; apply Hin; clear Hin.    
    apply IH with tgt rgt; auto.
    apply complete_ag_fold_not_source with refs src'; auto.
    intros Hnot; apply HeqS; apply Ref.eq_sym; auto.
  Qed.

  (* now that we have the hang of this, we need to prove that target is also in there *)
  (* This induction is lexicographic with src, so our IH must give us the property that
     we want when src is not the src we are looking for *)
  Definition AG_in_source_target_refs (refs:RefSet.t) (acc A:AG.t) := 
    forall (src tgt:Ref.t)(rgt:accessRight), AG.In (Edges.mkEdge src tgt rgt) A ->
      ~ AG.In (Edges.mkEdge src tgt rgt) acc -> RefSet.In src refs /\ RefSet.In tgt refs.

  Theorem AG_in_source_target_refs_complete_ag_fold:
    forall refs acc,
      AG_in_source_target_refs refs acc (RefSet.fold (complete_ag_fold refs) refs acc).
  Proof.
    intros.
    unfold AG_in_source_target_refs.
    intros src tgt rgt.
    apply RefSetProps.fold_rec_bis
      with (s:=refs)
        (P:=fun sub_refs A => AG.In (Edges.mkEdge src tgt rgt) A ->
          ~ AG.In (Edges.mkEdge src tgt rgt) acc -> 
          RefSet.In src sub_refs /\ RefSet.In tgt refs).
    (* equiv case *)
    intros.
    intuition; apply H in H3; assumption.
    (* base case *)
    intros.
    contradiction.
    (* inductive step *)
    intros.
    case (AGProps.In_dec (Edges.mkEdge src tgt rgt) a); intros Hina.
    (* In edge a *)
    apply H1 in Hina; auto.
    destruct Hina.
    split; auto; RefSetFacts.set_iff; right; auto.
    (* ~ In edge a *)
    case (Ref.eq_dec x src); intros HeqS.
    (* x = src *)
    split. apply RefSet.add_1; auto.
    (* TODO: for some unknown reason, the rewrite hangs in coq 8.3 unless we unfold Ref.eq *)
    unfold Ref.eq in HeqS; rewrite HeqS in H2.
    generalize (@fold_AG_in_target_refs src refs a tgt rgt H2 Hina); auto.
    (* x <> src *)
    apply complete_ag_fold_not_source in H2; auto.
    apply H1 in H2; destruct H2; auto.
    split; auto.
    let Hin := fresh Hin in
      generalize (RefSetFacts.add_neq_iff s' HeqS); intros Hin;
        let Hdc := fresh H in
          destruct Hin as [Hdc Hin]; clear Hdc; apply Hin; clear Hin; auto.
    intro Hnot; apply HeqS; apply Ref.eq_sym; auto.
  Qed.



  Definition complete_AG_conv (refs:RefSet.t) (full:AG.t) : Prop :=
    forall src tgt rgt, 
      AG.In (Edges.mkEdge src tgt rgt) full -> RefSet.In src refs /\ RefSet.In tgt refs.

  Theorem complete_AG_conv_complete_ag: 
    forall refs,
      complete_AG_conv refs (complete_ag refs).
  Proof.
    intros.
    unfold complete_AG_conv.
    unfold complete_ag.
    intros.
    eapply AG_in_source_target_refs_complete_ag_fold.
    apply H.
    apply AG.empty_1.
  Qed.

  Definition complete_ag_spec refs full :=
    forall edge, 
      AG.In edge full <-> RefSet.In (Edges.source edge) refs /\ RefSet.In (Edges.target edge) refs.

  Theorem complete_ag_spec_complete_ag : forall refs,
    complete_ag_spec refs (complete_ag refs).
  Proof.
    unfold complete_ag_spec; intros.
    split; intros H.
    eapply complete_AG_conv_complete_ag;
      rewrite <- (Edges.edge_rewrite edge) in H; eauto.
    rewrite <- (Edges.edge_rewrite edge) in H.
    rewrite Edges.source_rewrite in H;
    rewrite Edges.target_rewrite in H;
    rewrite <- (Edges.edge_rewrite edge);
    eapply fold_AG_complete_ag; intuition; auto.
  Qed.

(* there are two approaches we could take.:
   1. Fold over a complete access graph until convergence.
   However, we can't easily turn a prop into a bool without decidability.
   2. Induct over a complete access graph until convergence.
   However, we can't determine completeness without decidability.
   This all relies on decidability of transfer.
   *)

  (* It is difficult to prove decidability over transfer as we don't have any hyp. in set to destruct
     accurately.  The Coq.Decidable library provides for reasoning over /\ and \/, so
     transfer_as_logic gives us something to build up decidability. *)

  Definition transfer_as_logic_edge_wit (A B:AG.t) (edge:Edge.t) (wit:Ref.t) : Prop :=
      AGProps.Add edge A B /\
        (*read*)
        ((AG.In (Edges.mkEdge (Edges.source edge) wit rd) A /\
          AG.In (Edges.mkEdge wit (Edges.target edge) (Edges.right edge)) A) \/
         (*write*)
         (AG.In (Edges.mkEdge wit (Edges.source edge) wr) A /\
          AG.In (Edges.mkEdge wit (Edges.target edge) (Edges.right edge)) A) \/
         (*send*)
         (AG.In (Edges.mkEdge wit (Edges.source edge) tx) A /\
          AG.In (Edges.mkEdge wit (Edges.target edge) (Edges.right edge)) A) \/
         (*reply*)
         (AG.In (Edges.mkEdge (Edges.target edge) (Edges.source edge) tx) A /\
           AccessRight.eq (Edges.right edge) tx) \/
         (*weak*)
         (exists rgt:accessRight,
           AG.In (Edges.mkEdge (Edges.source edge) wit wk) A /\
           AG.In (Edges.mkEdge wit (Edges.target edge) rgt) A /\
          (AccessRight.eq rgt wk \/ AccessRight.eq rgt rd) /\
          AccessRight.eq (Edges.right edge) wk) \/
         (*self*)
         (Ref.eq (Edges.source edge) (Edges.target edge) /\
           exists rgt:accessRight,
           (* source *)
           (AG.In (Edges.mkEdge wit (Edges.source edge) rgt) A \/
           (* target *)
            AG.In (Edges.mkEdge (Edges.source edge) wit rgt) A))).


  Definition transfer_as_logic_edge (A B:AG.t) (edge:Edge.t) : Prop :=
    exists wit:Ref.t, transfer_as_logic_edge_wit A B edge wit.

  Definition transfer_as_logic (A B:AG.t) : Prop :=
    exists edge:Edge.t, transfer_as_logic_edge A B edge.

  Hint Unfold transfer_as_logic transfer_as_logic_edge transfer_as_logic_edge_wit.

  Theorem compat_P_transfer_A : forall A:AG.t, SetoidList.compat_P AG.Equal (transfer A).
  Proof.
    unfold SetoidList.compat_P.
    intros A B B' Heq HA.
    destruct HA; eauto.
  Qed.

  Theorem compat_P_transfer_B : forall B:AG.t, SetoidList.compat_P AG.Equal (fun A => transfer A B). 
  Proof.
    unfold SetoidList.compat_P.
    intros B A A' Heq HA.
    destruct HA; eauto.
  Qed.

  Hint Unfold complete_AG.


  Theorem AG_all_objs_src : forall (A:AG.t) (N:RefSet.t), AG_all_objs A N -> 
    forall (src tgt:Ref.t) (rgt:accessRight), AG.In (Edges.mkEdge src tgt rgt) A -> RefSet.In src N.
  Proof.
    intros; unfold AG_all_objs in *; generalize (H src tgt rgt H0); intros; destruct H1; trivial.
  Qed.

  Theorem AG_all_objs_tgt : forall (A:AG.t) (N:RefSet.t), AG_all_objs A N -> 
    forall (src tgt:Ref.t) (rgt:accessRight), AG.In (Edges.mkEdge src tgt rgt) A -> RefSet.In tgt N.
  Proof.
    intros; unfold AG_all_objs in *; generalize (H src tgt rgt H0); intros; destruct H1; trivial.
  Qed.

  Hint Resolve AG_all_objs_src AG_all_objs_tgt.

  Theorem transfer_in_complete : forall (A:AG.t) (N:RefSet.t), AG_all_objs A N -> 
    forall C:AG.t, complete_AG N C -> 
    forall B:AG.t, transfer A B -> 
    exists e:Edge.t, AGProps.Add e A B /\ AG.In e C.
  Proof.
    intros A N Hobjs C Hcompl B Htrans.
    destruct Htrans; esplit; split; eauto; first [apply H0|apply H1|apply H2].
  Qed.

  Theorem not_in_complete_not_transfer : forall (A:AG.t) (N:RefSet.t), AG_all_objs A N -> 
    forall C:AG.t, complete_AG N C -> 
      forall B:AG.t, ~ (exists e:Edge.t, AGProps.Add e A B /\ AG.In e C) -> ~ transfer A B.
  Proof.
    intros A N Hobjs C Hcomplete B Hexists.
    unfold not in Hexists; red; intros.
    apply Hexists.
    eapply transfer_in_complete; eauto.
  Qed.
  

Theorem ag_all_objs_transfer: forall A N B, AG_all_objs A N -> transfer A B -> AG_all_objs B N.
Proof.
  intros.
  generalize (@fold_AG_complete_ag N); set (C:=(complete_ag N));intros H1.
  generalize (transfer_in_complete H H1 H0); intros [edge [H2 H3]].
  unfold AG_all_objs; intros.
  rewrite <- (Edges.edge_rewrite edge) in *.
  eapply H2 in H4; destruct H4 as [[H4 [H5 H6]] | H4]; [| eapply H; apply H4].
  simpl in *.
  rewrite H4 in *; rewrite H5 in *; rewrite H6 in *; clear H4 H5 H6.
  eapply complete_AG_conv_complete_ag. apply H3.
Qed.

Hint Resolve ag_all_objs_transfer.

Theorem ag_all_objs_potTransfer: forall A N B, AG_all_objs A N -> potTransfer A B -> AG_all_objs B N.
Proof.
  intros.
  induction H0; eauto.
  unfold AG_all_objs in *; intros. eauto.
Qed.

  Theorem complete_case : forall (A:AG.t) (N:RefSet.t), AG_all_objs A N -> 
    forall C:AG.t, complete_AG N C -> 
      forall B:AG.t, {(exists e:Edge.t, AGProps.Add e A B /\ AG.In e C)} +
        {~ (exists e:Edge.t, AGProps.Add e A B /\ AG.In e C)}.
  Proof.
    intros.
    generalize (AGDep.exists_ (fun x => (AGAddEq.Add_dec x A B)) C).
    intros H1.
    let resolve_compatP := fun H1 H2 => generalize (H1 (AGAddEq.compat_P_Add A B)); clear H1; intros H2; unfold AG.Exists in H2 in
      destruct H1 as [H1 | H1];
        [left; (resolve_compatP H1 He) | right; resolve_compatP H1 H2; unfold not in *; intros He];
        destruct He as [e He]; destruct He as [He1 He2]; eauto.
  Qed.


  Theorem transfer_transfer_as_logic: forall A B:AG.t,
    transfer A B -> transfer_as_logic A B.
  Proof.
    intros.
    unfold transfer_as_logic; unfold transfer_as_logic_edge; unfold transfer_as_logic_edge_wit.
    destruct H.

    (* self source case *)
    apply ex_intro with (Edges.mkEdge src src rgt').
    apply ex_intro with tgt.
    split; auto; right; right; right; right; right;
      split; [unfold Ref.eq ; auto | esplit; right; eauto].
    (* self target case *) 
    apply ex_intro with (Edges.mkEdge tgt tgt rgt').
    apply ex_intro with src.
    split; auto; right; right; right; right; right;
      split; [unfold Ref.eq ; auto | esplit; left; eauto] .
    (* read case *)
    apply ex_intro with (Edges.mkEdge src tgt' rgt);
      apply ex_intro with tgt;
        split; auto.
    (* write case *)
    apply ex_intro with (Edges.mkEdge tgt tgt' rgt);
      apply ex_intro with src;
        split; auto.
    (* send case *)
    apply ex_intro with (Edges.mkEdge tgt tgt' rgt);
      apply ex_intro with src;
        split; auto.
    (* send reply case *)
    apply ex_intro with (Edges.mkEdge tgt src tx);
      apply ex_intro with src;
        split; [|right; right; right; left]; 
          intuition (eauto; try (rewrite Edges.right_rewrite; apply AccessRight.eq_refl)). 
    (* weak case *)
    apply ex_intro with (Edges.mkEdge src tgt' wk);
      apply ex_intro with tgt.
     split; auto.
     right; right; right; right; left.
     esplit.
     simpl.
     split; auto.
     split; unfold Edges.target; simpl;
       intuition (eauto; try (rewrite Edges.right_rewrite; apply AccessRight.eq_refl)).
  Qed.

  Theorem transfer_as_logic_transfer: forall A B:AG.t,
    transfer_as_logic A B -> transfer A B.
  Proof.
    intros.
    unfold transfer_as_logic in *; unfold transfer_as_logic_edge in *; unfold transfer_as_logic_edge_wit in *.
    destruct H as [edge H]; destruct H as [wit H].
    intuition.
    (* read case *)
    eapply transfer_read; eauto; autorewrite with caps_rewrite.
    (* write case *)
    eapply transfer_write; eauto; autorewrite with caps_rewrite.
    (* send case *)
    eapply transfer_send; eauto; autorewrite with caps_rewrite.
    (* send reply case *)
    eapply transfer_send_reply; eauto.
    unfold AccessRight.eq in *.
    rewrite <- H2 in *.
    autorewrite with caps_rewrite; trivial.
    (* weak case *)
    destruct H as [rgt H]; destruct H; destruct H1; destruct H2; auto.
    eapply transfer_weak with rgt (Edges.source edge) wit (Edges.target edge); auto.
    unfold AccessRight.eq in *; rewrite <- H3; auto.
    (* self case *)
    destruct H2 as [rgt H2]; destruct H2.
    (* self target *)
    eapply transfer_self_tgt with (rgt:=rgt). 
    apply H.
    unfold Ref.eq in *.
    rewrite <- (Edges.edge_rewrite edge) in H0.
    rewrite <- H1 in H0.
    apply H0.
    (*self source *)
    eapply transfer_self_src with (rgt:=rgt).
    apply H.
    unfold Ref.eq in *.
    rewrite <- (Edges.edge_rewrite edge) in H0.
    rewrite <- H1 in H0.
    apply H0.
  Qed.

  Hint Resolve transfer_as_logic_transfer transfer_transfer_as_logic.

  Theorem transfer_iff_transfer_as_logic : forall A B:AG.t,
    transfer A B <-> transfer_as_logic A B.
  Proof.
    intros; split; auto.
  Qed.

  Hint Resolve transfer_iff_transfer_as_logic.

  Theorem not_transfer_iff_not_transfer_as_logic : forall A B:AG.t,
    ~ transfer_as_logic A B <-> ~ transfer A B.
  Proof.
    intros; split; auto.
  Qed.

  Hint Resolve not_transfer_iff_not_transfer_as_logic.
  
  (* we need to know this so that we may determine the existence of decidable properties 
     over accessRights.  Thus, the two (exists rgt, ...) statements can be shown to be
     decidable, and since the logic is compat_P, the entire trans_as_logic is decidable, making
     trans decidable. *)

  Theorem accessRight_ex_dec : forall (P: accessRight -> Prop)
    (Pdec: forall r, {P r} + {~ P r}),
    {exists r, P r} + {~ exists r, P r}.
  Proof.
    intros.
    generalize (Pdec rd) (Pdec wr) (Pdec wk) (Pdec tx).
    intros Hr Hw Hk Hs;
    destruct Hr; destruct Hw; destruct Hk; destruct Hs.
    (* eauto throws an uncaught exception on the last case.  Exceptions aren't failure, so 
       we can't try to apply it.  Fix this when we update to Coq 8.2-pl1. *)
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    right.
    intro.
    destruct H as [rgt H].
    destruct rgt;
    auto.
  Qed.

  Theorem transfer_as_logic_edge_wit_dec : forall A B edge wit,
    {transfer_as_logic_edge_wit A B edge wit} + {~ transfer_as_logic_edge_wit A B edge wit}.
  Proof.
    intros.
    unfold transfer_as_logic_edge_wit.
    apply Sumbool_dec_and.
      apply AGAddEq.Add_dec.
    apply Sumbool_dec_or. apply Sumbool_dec_and; apply AGDep.mem.
    apply Sumbool_dec_or. apply Sumbool_dec_and; apply AGDep.mem.
    apply Sumbool_dec_or. apply Sumbool_dec_and; apply AGDep.mem.
    apply Sumbool_dec_or. apply Sumbool_dec_and; [apply AGDep.mem|apply AccessRight.eq_dec].
    apply Sumbool_dec_or.
      apply accessRight_ex_dec; intros.
      apply Sumbool_dec_and.
      apply AGDep.mem.
      apply Sumbool_dec_and.
      apply AGDep.mem.
      apply Sumbool_dec_and.
        apply Sumbool_dec_or;
          apply AccessRight.eq_dec.
      apply AccessRight.eq_dec.
    apply Sumbool_dec_and.
      apply Ref.eq_dec.
      apply accessRight_ex_dec; intros.
      apply Sumbool_dec_or; apply AGDep.mem.
  Qed.

  Theorem transfer_as_logic_edge_wit_in_objs: 
    forall A N, AG_all_objs A N -> 
      forall B edge,
        (exists wit, transfer_as_logic_edge_wit A B edge wit) <->
        exists wit', RefSet.In wit' N /\ transfer_as_logic_edge_wit A B edge wit'.
  Proof.
    intros.
    split.

    intros.
    destruct H0 as [wit H0].
    destruct H0; destruct H1; destruct H1.
    generalize (H _ _ _ H1); intros; destruct H3.
    apply ex_intro with wit; split; auto.
    destruct H1.
    generalize (H _ _ _ H1); intros; destruct H3.
    apply ex_intro with wit; split; auto 6.
    destruct H1; destruct H1.
    generalize (H _ _ _ H1); intros; destruct H3.
    apply ex_intro with wit; split; auto 10.
    destruct H1.
    assert (exists wit', RefSet.In wit' N).
    apply ex_intro with (Edges.source edge).
    generalize (H _ _ _ H1).
    intros; destruct H3; auto.
    destruct H3 as [wit' H3].
    apply ex_intro with wit';split;auto 10.

    destruct H1.
    destruct H1 as [rgt H1].
    destruct H1.
    destruct H2.
    destruct H3.
    generalize (H _ _ _ H1); intros H5; destruct H5.
    apply ex_intro with wit; split; auto.
    unfold transfer_as_logic_edge_wit.
    split; auto.
    right; right; right; right; left.
    split with rgt.
    auto.
    destruct H1.
    destruct H2 as [rgt H2].
    destruct H2.
    generalize (H _ _ _ H2); intros.
    destruct H3.
    split with wit.
    split; auto.
    unfold transfer_as_logic_edge_wit.
    split;auto; right;right;right;right;right.
    split;auto.
    split with rgt; auto.
    generalize (H _ _ _ H2); intros H3; destruct H3.
    split with wit.
    split;auto.
    unfold transfer_as_logic_edge_wit.
    split; auto; right;right;right;right;right; split;auto.
    split with rgt; auto.
  
    intros.
    destruct H0 as [wit' H0].
    destruct H0.
    eauto.
  Qed.

  Theorem transfer_as_logic_edge_wit_compat_P: forall A B edge,
    SetoidList.compat_P Ref.eq (transfer_as_logic_edge_wit A B edge).
  Proof.
    unfold SetoidList.compat_P; unfold Ref.eq; intros.
    unfold Proper; unfold respectful; intros.  rewrite <- H. unfold Basics.impl.  trivial.
  Qed.

  Theorem transfer_as_logic_edge_dec: forall A B edge,
    {transfer_as_logic_edge A B edge} + {~ transfer_as_logic_edge A B edge}.
  Proof.
    intros.
    unfold transfer_as_logic_edge.
    generalize (@AG_all_objs_ag_objs A).
    generalize (ag_objs A).
    intros N Hobjs.
    generalize (RefSetDep.exists_ (transfer_as_logic_edge_wit_dec A B edge) N).
    intros.
  

    destruct H as [H|H]; unfold RefSet.Exists in *;
      generalize (H (@transfer_as_logic_edge_wit_compat_P A B edge)); intros.
    left.
    destruct H0 as [wit H0]; destruct H0.
    split with wit; auto.

    right.
    intuition.

    generalize (@transfer_as_logic_edge_wit_in_objs A N Hobjs B edge); intros H2.
    destruct H2 as [H2 H3].
    auto.
  Qed.
  

  Theorem transfer_as_logic_edge_compat_P: forall A B,
    SetoidList.compat_P Edge.eq (transfer_as_logic_edge A B).
  Proof.
    intros.
    unfold SetoidList.compat_P; intros.
    unfold Basics.impl; unfold Proper; unfold respectful; intros.
    generalize (Edges.eq_source _ _ H); intros HeqS.
    generalize (Edges.eq_target _ _ H); intros HeqT.
    generalize (Edges.eq_right _ _ H); intros HeqR.
    unfold transfer_as_logic_edge in *.
    destruct H0 as [wit H0].
    eapply ex_intro with wit.
    Require Import Basics.
    unfold transfer_as_logic_edge_wit in*.
    destruct H0 as [H0 H0'].
    split; [eapply AGAddEq.Add_eq_complete; [ apply H | apply AG.eq_refl|apply AG.eq_refl | apply H0]|].
    unfold Ref.eq in *; unfold AccessRight.eq in *;
    rewrite <- HeqS in *; rewrite <- HeqT in *; rewrite <- HeqR in *; simpl in *; trivial.
  Qed.

  Ltac applyHcomplete := fun edge Hcomplete => rewrite <- (Edges.edge_rewrite edge); apply Hcomplete.
  Ltac applyHobjs := fun Hobjs Hin final => 
    generalize (Hobjs _ _ _ Hin); let Hnew := fresh in
      intro Hnew; destruct Hnew; final.

  Theorem transfer_as_logic_edge_in_complete: 
    forall A N, AG_all_objs A N -> 
      forall C, complete_AG N C ->
        forall B,
          (exists edge, transfer_as_logic_edge A B edge) <->
          exists edge', AG.In edge' C /\ transfer_as_logic_edge A B edge'.
  Proof.
    intros A N Hobjs C Hcomplete B; split; intros.
    destruct H as [edge H].
    split with edge; split; auto.
    unfold transfer_as_logic_edge in *.
    destruct H as [wit H].
    unfold transfer_as_logic_edge_wit.
    destruct H.
    destruct H0; destruct H0.
    applyHcomplete edge Hcomplete.
    applyHobjs Hobjs H0 trivial.
    applyHobjs Hobjs H1 trivial.
    destruct H0.
    applyHcomplete edge Hcomplete.
    applyHobjs Hobjs H0 trivial.
    applyHobjs Hobjs H1 trivial.
    destruct H0; destruct H0.
    applyHcomplete edge Hcomplete.
    applyHobjs Hobjs H0 trivial.
    applyHobjs Hobjs H1 trivial.
    destruct H0.
    applyHcomplete edge Hcomplete;
      applyHobjs Hobjs H0 trivial.
    destruct H0; destruct H0 as [rgt H0]; destruct H0. destruct H1.
    applyHcomplete edge Hcomplete.
    applyHobjs Hobjs H0 trivial.
    applyHobjs Hobjs H1 trivial.
    unfold Ref.eq in *.
    destruct H0; applyHcomplete edge Hcomplete;
    applyHobjs Hobjs H0 trivial.
    rewrite rgt in H0; applyHobjs Hobjs H0 trivial.
    applyHobjs Hobjs H0 trivial.
    rewrite rgt in H0; applyHobjs Hobjs H0 trivial.
    
    destruct H as [edge' H]; destruct H; split with edge'; assumption.
  Qed.

  Theorem transfer_as_logic_dec : forall A B,
    {transfer_as_logic A B} + {~ transfer_as_logic A B}.
  Proof.
    intros.
    unfold transfer_as_logic.
    generalize (@fold_AG_complete_ag (ag_objs A)).
    generalize (@AG_all_objs_ag_objs A).
    generalize (complete_ag (ag_objs A)).
    generalize (ag_objs A).
    intros N C Hobjs Hcomplete.
    generalize (AGDep.exists_ (transfer_as_logic_edge_dec A B) C).
    intros H.
    
    unfold AG.Exists in *; destruct H as [H|H];
    generalize (H (@transfer_as_logic_edge_compat_P A B)); intros.
    left.
    destruct H0 as [edge H0]; destruct H0; split with edge; trivial.
    right; intuition.
    generalize (@transfer_as_logic_edge_in_complete _ _ Hobjs _ Hcomplete B); intros H2.
    destruct H2 as [H2 H3].
    auto.
  Qed.


  (* To prove transfer_as_logic_dec, we need to know that:
     edge is in the complete access graph, and
     wit is in ag_objs *)

  (* note, we can't destruct Hexists, until we choose a sumbool side since sumbools are members of set.
     This requires the use of transfer_as_logic *)

  Theorem transfer_dec : forall A B:AG.t, {transfer A B} + {~ transfer A B}.
  Proof.
    intros.
    generalize (transfer_as_logic_dec A B); intros Hdec;
      generalize (transfer_iff_transfer_as_logic A B); intro Hiff;
        destruct Hiff.
    destruct Hdec; [left|right]; auto.
  Qed.    
  
    

  (* to prove that AG.Exists is decidable, transfer must be decidable *)

  (* Hrm, now that transfer is decidable, we may be able to fold trans over
     a complete access graph:
     Close a foldable function over a complete access graph.
     Fold that function over a complete access graph to find one edge that can transfer.
     When that edge can transfer, add to the accumulator and repeat.
     Additional edges are redundant computation.
 *)

  
  

  Definition transfer_bool A B:=
    true_bool_of_sumbool (transfer_dec A B).
  
  (* This function, given a graph i, examines each edge and determines if it can transfer i i+edge.
     If it can, and the accumulator is not Some edge, it returns this edge, otherwise it returns
     the accumulator. *)
  Definition findTransferEdge_fold i edge prev_edge :=
    if (andb (negb (AG.mem edge i)) (transfer_bool i (AG.add edge i)))
      then Some edge
      else prev_edge.

  (* Hideously ineficient, but easy to work with.  I would not extract this as software. *)

  Definition findTransferEdge i :=
    AG.fold (findTransferEdge_fold i) (complete_ag (ag_objs i)) None.

  Import Bool.

  (* I can't find this anywhere, so I'm proving it *)

  Theorem negb_false : forall b,
    b = false -> negb b = true.
  Proof.
    intros.
    destruct b; simpl; eauto; simpl.
  Qed.

  Theorem negb_true : forall b,
    b = true -> negb b = false.
  Proof.
    intros.
    destruct b; simpl; eauto; simpl.
  Qed.

  Theorem findTransferEdge_fold_Pred: forall i edge,
    match findTransferEdge_fold i edge None with
      | None => AG.In edge i \/ (forall B, AGProps.Add edge i B -> ~ transfer i B)
      | Some edge' => edge' = edge /\ ~ AG.In edge i /\ forall B, AGProps.Add edge i B -> transfer i B
    end.
  Proof.
    intros i edge.
    case (option_sumbool (findTransferEdge_fold i edge None)); intros H.
    (* None Case *)
    rewrite H.
    unfold findTransferEdge_fold in H.
     case (sumbool_of_bool (negb (AG.mem edge i) && transfer_bool i (AG.add edge i))); 
      intros He; rewrite He in H.
    inversion H.
    clear H.
    apply negb_false in He.
    rewrite negb_andb in He.
    rewrite negb_involutive in He.
    apply orb_true_elim in He.
    case He; clear He; intros He.
    left. apply AG.mem_2; assumption.
    right. intros B Hadd.
    apply negb_true in He.
    rewrite negb_involutive in He.
    unfold transfer_bool in *.
    unfold true_bool_of_sumbool in *.
    apply true_bool_of_sumbool_r in He.
    eapply AGAddEq.Add_add in Hadd.
    apply AGProps.equal_sym in Hadd.
    generalize (@compat_P_transfer_A i B (AG.add edge i) Hadd).
    intros.
    red; intros.
    apply He; auto.
    (* Some edge Case *)
    destruct H.
    rewrite H.
    unfold findTransferEdge_fold in H.
    case (sumbool_of_bool (negb (AG.mem edge i) && transfer_bool i (AG.add edge i)));
      intros He; rewrite He in H; inversion H.
    split; auto.
    rewrite <- H1.
    clear H H1.
    apply sym_eq in He.
    apply andb_true_eq in He.
    destruct He as [Hmem Htransfer].
    split; auto.
    apply sym_eq in Hmem.
    apply negb_true in Hmem.
    rewrite negb_involutive in Hmem.
    generalize (AGFacts.not_mem_iff i edge); intros HnotMem; destruct HnotMem as [H_mem1 Hmem2]; auto.
    intros B Hadd.
    apply sym_eq in Htransfer.
    unfold transfer_bool in *.
    unfold true_bool_of_sumbool in *.
    apply true_bool_of_sumbool_l in Htransfer.
    eapply AGAddEq.Add_add in Hadd.
    generalize (@compat_P_transfer_A i (AG.add edge i) B Hadd).
    intros.
    auto.
  Qed.

  Theorem findTransferEdge_fold_Pred2: forall i edge opt,
    match findTransferEdge_fold i edge opt with
      | None => AG.In edge i \/ (forall B, AGProps.Add edge i B -> ~ transfer i B)
      | Some edge' => 
        let P := edge' = edge /\ ~ AG.In edge i /\ forall B, AGProps.Add edge i B -> transfer i B in
          match opt with
            | None => P
            | Some edge'' => edge'' = edge' \/ P
          end
    end.
  Proof.
    intros i edge opt.
    case (option_sumbool (findTransferEdge_fold i edge opt)); intros H.
    (* None Case *)
    rewrite H.
    unfold findTransferEdge_fold in H. 
    case (sumbool_of_bool (negb (AG.mem edge i) && transfer_bool i (AG.add edge i))); 
      intros He; rewrite He in H.
    inversion H.
    clear H.
    apply negb_false in He.
    rewrite negb_andb in He.
    rewrite negb_involutive in He.
    apply orb_true_elim in He.
    case He; clear He; intros He.
    left. apply AG.mem_2; assumption.
    right. intros B Hadd.
    apply negb_true in He.
    rewrite negb_involutive in He.
    unfold transfer_bool in *.
    unfold true_bool_of_sumbool in *.
    apply true_bool_of_sumbool_r in He.
    eapply AGAddEq.Add_add in Hadd.
    apply AGProps.equal_sym in Hadd.
    generalize (@compat_P_transfer_A i B (AG.add edge i) Hadd).
    intros.
    red; intros.
    apply He; auto.
    (* Some edge Case *)
    destruct H.
    rewrite H.
    unfold findTransferEdge_fold in H.
    simpl.

    destruct opt as [edge'|].

    case (sumbool_of_bool (negb (AG.mem edge i) && transfer_bool i (AG.add edge i)));
      intros He; rewrite He in H; inversion H.

    (* solve for He *)
    rewrite <- H1.
    clear x H H1.
    apply sym_eq in He.
    apply andb_true_eq in He.
    destruct He as [Hmem Htrans].
    apply sym_eq in Hmem.
    apply negb_true in Hmem.
    rewrite negb_involutive in Hmem.
    generalize (AGFacts.not_mem_iff i edge); intros HnotMem; destruct HnotMem as [H_mem1 H_mem2]; apply H_mem2 in Hmem.
    clear H_mem1 H_mem2.
    apply sym_eq in Htrans.
    unfold transfer_bool in *.
    unfold true_bool_of_sumbool in *.
    apply true_bool_of_sumbool_l in Htrans.

    right.

    (* solve P *)
    split; auto; split; auto.
    intros B Hadd.
    eapply AGAddEq.Add_add in Hadd.
    generalize (@compat_P_transfer_A i (AG.add edge i) B Hadd).
    intros.
    auto.

    (* solve left *)

    left; auto.

    case (sumbool_of_bool (negb (AG.mem edge i) && transfer_bool i (AG.add edge i)));
      intros He; rewrite He in H; inversion H.

    (* solve for He *)
    rewrite <- H1.
    clear x H H1.
    apply sym_eq in He.
    apply andb_true_eq in He.
    destruct He as [Hmem Htrans].
    apply sym_eq in Hmem.
    apply negb_true in Hmem.
    rewrite negb_involutive in Hmem.
    generalize (AGFacts.not_mem_iff i edge); intros HnotMem; destruct HnotMem as [H_mem1 H_mem2]; apply H_mem2 in Hmem.
    clear H_mem1 H_mem2.
    apply sym_eq in Htrans.
    unfold transfer_bool in *.
    unfold true_bool_of_sumbool in *.
    apply true_bool_of_sumbool_l in Htrans.

    (* solve P *)
    split; auto; split; auto.
    intros B Hadd.
    eapply AGAddEq.Add_add in Hadd.
    generalize (@compat_P_transfer_A i (AG.add edge i) B Hadd).
    intros.
    auto.
  Qed.

  Definition findTransferEdge_A_P A B o :=
    match o with
      | None => forall edge, AG.In edge B -> ~ AG.In edge A -> forall A', AGProps.Add edge A A' -> ~ transfer A A'
      | Some edge => AG.In edge B /\  ~ AG.In edge A /\ (forall A', AGProps.Add edge A A' -> transfer A A')
    end.

  Theorem transfer_not_empty : forall A, AG.Empty A -> forall e B, AGProps.Add e A B -> ~ transfer A B.
  Proof.
    intros.
    red.
    intros.
    unfold AG.Empty in *.
    destruct H1.
    generalize (H (Edges.mkEdge src tgt rgt)); intros; tauto.
    generalize (H (Edges.mkEdge src tgt rgt)); intros; tauto.
    generalize (H (Edges.mkEdge src tgt rd)); intros; tauto.
    generalize (H (Edges.mkEdge src tgt wr)); intros; tauto.
    generalize (H (Edges.mkEdge src tgt tx)); intros; tauto.
    generalize (H (Edges.mkEdge src tgt tx)); intros; tauto.
    generalize (H (Edges.mkEdge src tgt wk)); intros; tauto.
  Qed.

  Theorem findTransferEdge_general: forall A, findTransferEdge_A_P A (complete_ag (ag_objs A)) (findTransferEdge A).
  Proof.
    intros.
    unfold findTransferEdge.
    apply AGProps.fold_rec.
    (* base case *)
    unfold findTransferEdge_A_P.
    intros.
    generalize (H edge); intros.
    tauto.
    (* inductive step *)
    intros new_edge opt B B' Hcompl Hin Hadd Hfind.
    
    case (option_sumbool (findTransferEdge_fold A new_edge opt)); intros; [|destruct e as [e He]]; try rewrite e in *; try rewrite He in *.
    case (option_sumbool opt); intros; [|destruct e0 as [e' e0]];  rewrite e0 in *.

    (* findTransferEdge_fold A new_edge None = None && opt = None *)
    unfold findTransferEdge_A_P in *.
    unfold findTransferEdge_fold in e.
    intros.
    case (sumbool_of_bool (negb (AG.mem new_edge A) && transfer_bool A (AG.add new_edge A))); intros HeqB; rewrite HeqB in e.
    red; intros; discriminate e.
    (* solve for transfer_bool *)    



    (* inputs: A new_edge H He*)
    case (sumbool_of_bool (negb (AG.mem new_edge A) && transfer_bool A (AG.add new_edge A))); 
      intros He; rewrite He in HeqB.
    absurd (true=false); auto; simplify_eq.
    apply negb_false in He.
    rewrite negb_andb in He.
    rewrite negb_involutive in He.
    apply orb_true_elim in He.
    case He; clear He; intros He; 
      [apply AG.mem_2 in He | 
        apply negb_true in He; 
          rewrite negb_involutive in He;
            unfold transfer_bool in He;
              unfold true_bool_of_sumbool in He;
                apply true_bool_of_sumbool_r in He].
    (* In edge B' -> Add new_edge B B' -> In edge B \/ new_edge = edge, by definition of Add *)
    (* However, edge = new_edge -> ~ In edge A -> In new_edge A -> False, so therefore, we know In edge B *)
    (* given Hfind, we can show In edge B -> ~ transfer A A' *)
    (* for some reason, the edge is broken down *)
    apply AGAddEq.Add_unfold with (x':=edge) in Hadd.
    destruct Hadd as [Hadd1 Hadd2].
    generalize (Hadd1 H); intros Hor.
    destruct Hor.
    apply Hfind with (edge:=edge) (A':=A'); auto.
    apply Hfind with (edge:=edge); auto.
    generalize (Edges.eq_equal new_edge edge); intros Ht.
    destruct Ht as[Ht1 Ht2].
    apply Ht1 in H2.
    rewrite H2 in *.
    intuition.


    apply AGAddEq.Add_unfold with (x':=edge) in Hadd.
    destruct Hadd as [Hadd1 Hadd2].
    generalize (Hadd1 H); intros Hor.
    destruct Hor.
    apply Hfind with (edge:=edge) (A':=A'); auto.
    generalize (Edges.eq_equal new_edge edge); intros Ht.
    destruct Ht as[Ht1 Ht2].
    apply Ht1 in H2.
    rewrite H2 in *.
    intuition.
    
    eapply AGAddEq.Add_add in H1.
    apply AGProps.equal_sym in H1.
    generalize (compat_P_transfer_A H1 (A:=A)).
    intros.
    auto.

    (* case findTransferEdge_fold A new_edge (Some e') = None *)
    (* can't happen *)
    
    unfold findTransferEdge_A_P in *;
      unfold findTransferEdge_fold in e;
        intros;
          case (sumbool_of_bool (negb (AG.mem new_edge A) && transfer_bool A (AG.add new_edge A))); intros HeqB; rewrite HeqB in e;
            red; intros; discriminate e. 
    
    (* now for Some e results *)

    case (option_sumbool opt); intros; [|destruct e0 as [e' e0]];  rewrite e0 in *.

    (* findTransferEdge_fold A new_edge None = Some e *)
    unfold findTransferEdge_A_P in *;
      unfold findTransferEdge_fold in *;
        intros.

    case (sumbool_of_bool (negb (AG.mem new_edge A) && transfer_bool A (AG.add new_edge A))); intros HeqB; rewrite HeqB in He.
    (* straightforward rewrite into transfer A (add new_edge A) and solve for none <> Some e. *)
    rename He into He'.
    rename HeqB into He.
    injection He';intros Heq; rewrite Heq in *.

    generalize (andb_true_eq (negb (AG.mem e A)) (transfer_bool A (AG.add e A))).
    intros.
    apply sym_eq in He.
    apply H in He.
    clear H.
    destruct He.
    apply sym_eq in H; apply sym_eq in H0.
    unfold transfer_bool in H0.
    unfold true_bool_of_sumbool in H.
    apply true_bool_of_sumbool_l in H0.
    apply negb_true in H.
    rewrite negb_involutive in H.
    generalize (AGFacts.not_mem_iff A e); intros Hmem; destruct Hmem as [Hmem1 Hmem2]; auto.
    apply Hmem2 in H.
    clear Hmem1 Hmem2.
    generalize (AGProps.Add_add A e); intros.
    split. apply AGAddEq.Add_In with (x:=e) (A:=B); auto.
    split; auto.
    intros.
    apply compat_P_transfer_A with (A:=A) (y:=A') (x:=(AG.add e A)); auto.
    eapply AGAddEq.Eq_Add with (A:=A) (B':=A') (x:=e); auto.
    discriminate He.

    (* findTransferEdge_fold A new_edge (Some e') = Some e *)
    unfold findTransferEdge_A_P in *;
      unfold findTransferEdge_fold in *;
        intros.

    case (sumbool_of_bool (negb (AG.mem new_edge A) && transfer_bool A (AG.add new_edge A))); intros HeqB; rewrite HeqB in He.
    (* straightforward rewrite into transfer A (add new_edge A) and solve for none <> Some e. *)
    rename He into He'.
    rename HeqB into He.
    injection He'; intros Heq; rewrite Heq in *.
    generalize (andb_true_eq (negb (AG.mem e A)) (transfer_bool A (AG.add e A))).
    intros.
    apply sym_eq in He.
    apply H in He.
    clear H.
    destruct He.
    apply sym_eq in H; apply sym_eq in H0.
    unfold transfer_bool in H0.
    unfold true_bool_of_sumbool in H0.
    apply true_bool_of_sumbool_l in H0.
    apply negb_true in H.
    rewrite negb_involutive in H.
    generalize (AGFacts.not_mem_iff A e); intros Hmem; destruct Hmem as [Hmem1 Hmem2]; auto.
    apply Hmem2 in H.
    clear Hmem1 Hmem2.
    generalize (AGProps.Add_add A e); intros.
    destruct Hfind.
    split. eapply AGAddEq.Add_In with (x:=e) (A:=B); auto.
    split; auto.
    intros.
    eapply compat_P_transfer_A with (x:=(AG.add e A)); auto.
    eapply AGAddEq.Eq_Add with (A:=A) (A':=A) (x:=e); auto. 


    (* last case e=e' *)
    injection He; intros Heq; rewrite Heq in *.
    destruct Hfind as [H_e_in_B Hfind].
    split; auto.
    generalize (Hadd e); intros Hadd2.
    destruct Hadd2 as [Hadd2 Hadd2'].
    apply Hadd2'. auto.
    
  Qed.


(* trying a different approach. *)

  Definition dist_from_complete i :=
    AG.cardinal (AG.diff (complete_ag (ag_objs i)) i).

  Require Recdef.

  Theorem ag_objs_equal : forall i,
    forall edge, RefSet.In (Edges.source edge) (ag_objs i) ->
      RefSet.In (Edges.target edge) (ag_objs i) ->
      forall A, AGProps.Add edge i A -> RefSet.Equal (ag_objs i) (ag_objs A).
  Proof.
    intros.
        generalize (AG_objs_equal (@AG_all_objs_ag_objs i) H H0 H1). intros Horig.
        unfold AG_all_objs in Horig.
    unfold ag_objs in *.
    (* cases (In_dec edge i) *)
    case (AGProps.In_dec edge i); intros Heq.
    (* In edge i -> equal A i *)
    generalize (AGAddEq.Add_Equal _ _ _ _ (Edge.eq_refl edge) Heq H1); intros.
    apply compat_op_ag_objs; auto.
    (* ~ In edge i -> remove edge A [=] i *)
    (* remove_fold_1 *)
    assert (RefSet.Equal 
      (obj_fold edge (AG.fold obj_fold (AG.remove edge A) RefSet.empty))
      (AG.fold obj_fold A RefSet.empty)).
    apply AGProps.remove_fold_1 with (f:=obj_fold) (s:=A); auto.
    exact RefSetFacts.Equal_ST.
    unfold SetoidList.transpose; intros; apply transpose_ag_objs_full.
    apply RefSetProps.equal_refl.
    eapply H1. left; apply Edge.eq_refl.
    eapply RefSetProps.equal_trans; [|apply H2].
    (* Add_remove_Equal pushed to FSetAddEq.v *)
    apply RefSetProps.equal_sym.
    rewrite <- (Edges.edge_rewrite edge).
    eapply obj_fold_simpl_eq; auto.
    eapply compat_op_ag_objs; auto.
    eapply AGAddEq.Add_remove_Equal; auto.
    rewrite (Edges.edge_rewrite edge); auto.
  Qed.


 (* in some cases, AG_all_objs may be too general, so we need properties about ag_objs_spec *)

  Theorem not_in_ag_objs_spec : forall o ag n,
   ag_objs_spec ag n -> ~ RefSet.In o n -> 
   forall o' rgt, ~ AG.In (Edges.mkEdge o o' rgt) ag /\ ~ AG.In (Edges.mkEdge o' o rgt) ag.
  Proof.
    intros.
    unfold ag_objs_spec in *.
    split;intro;apply H0;intuition eauto.
  Qed.

  Theorem not_in_ag_objs_spec_src : forall o ag n,
   ag_objs_spec ag n -> ~ RefSet.In o n -> 
   forall o' rgt, ~ AG.In (Edges.mkEdge o o' rgt) ag.
  Proof.
  intros.  
  destruct (not_in_ag_objs_spec H H0 o' rgt); auto.
  Qed.
 
  Theorem not_in_ag_objs_spec_tgt : forall o ag n,
   ag_objs_spec ag n -> ~ RefSet.In o n -> 
   forall o' rgt, ~ AG.In (Edges.mkEdge o' o rgt) ag.
  Proof.
  intros.  
  destruct (not_in_ag_objs_spec H H0 o' rgt); auto.
  Qed.

  Hint Resolve not_in_ag_objs_spec_src not_in_ag_objs_spec_tgt.

  Theorem ag_objs_spec_add : forall ag N, ag_objs_spec ag N -> 
   forall src tgt rgt ag', AGProps.Add (Edges.mkEdge src tgt rgt) ag ag' ->
   forall N', ag_objs_spec ag' N' ->
   forall x, RefSet.In x N' -> ~ Ref.eq x src -> ~ Ref.eq x tgt -> RefSet.In x N.
  Proof.
   intros.
   eapply H1 in H2.
   destruct H2 as [obj' [rgt' [H2 | H2]]]; eapply H0 in H2; simpl in *; (destruct H2 as [[H5 [H6 H7]]| H2]);
   try solve[first[apply Ref.eq_sym in H5; apply H3 in H5| apply Ref.eq_sym in H6; apply H4 in H6]; contradiction];
   eapply H; do 2 eapply ex_intro; [left|right]; apply H2.
  Qed.


  Theorem AG_all_objs_Add: forall A N src tgt rgt B N',
    AG_all_objs A N -> AGProps.Add (Edges.mkEdge src tgt rgt) A B ->
    RefSet.Subset N N' -> RefSet.In src N' -> RefSet.In tgt N' -> 
    AG_all_objs B N'.
  Proof.
    intros.
    red; intros.
    apply H0 in H4; simpl in *. destruct H4 as [[H4 [H5 H6]] | H4]; 
    [rewrite H4 in *; rewrite H5 in *; rewrite H6 in *; intuition| ].
    eapply H in H4; destruct H4 as [H4 H5].
    intuition.
  Qed.

    Theorem AG_cardinal_diff_inter_minus :
      forall s s', AG.cardinal (AG.diff s s') = AG.cardinal s - AG.cardinal (AG.inter s s').
    Proof.
      intros.
      apply Minus.plus_minus.
      apply sym_equal.
      rewrite Plus.plus_comm.
      apply AGProps.diff_inter_cardinal.
    Qed.


  Theorem compat_op_complete_ag : forall refs refs', RefSet.Equal refs refs' ->
    AG.Equal (complete_ag refs) (complete_ag refs').
  Proof.
    intros.
    unfold complete_ag.
    apply (RefSetFold.fold_foldEqual _ _ AGFacts.Equal_ST); auto.
    unfold RefSetFold.foldEqual; intros.
    apply compat_op_complete_ag_fold; auto.
    unfold SetoidList.transpose; intros.
    apply transpose_complete_ag_fold.
  Qed.

    Theorem minus_lt_compat_l:
      forall n m p, n < m -> m <= p -> p - m < p - n.
    Proof.
      intros n m p; generalize n m; clear n m; induction p as [|p IH].
      intros n m H H0; apply Le.le_n_O_eq in H0; 
        rewrite <- H0 in H; apply Lt.lt_n_O in H; contradiction.

      intros n m Hnm HmSp.
      generalize (Lt.lt_le_trans _ _ _ Hnm HmSp); intros HnSp.
      (* either m = p, or m < p *)
      generalize (Lt.le_lt_or_eq _ _ HmSp); intros Hcase.
      destruct Hcase.
      (* m < S p, apply IH *)
      apply Le.le_S_n in H.
      rewrite <- Minus.minus_Sn_m; [rewrite <- Minus.minus_Sn_m|]; auto with arith.
      (* m = S p, reduce to 0 <= m - n , reduce to m <= n, auto*)
      rewrite <- H.
      rewrite Minus.minus_diag.
      unfold lt.
      rewrite H.
      rewrite <- Minus.minus_Sn_m;  auto with arith.
    Qed.

    Theorem AG_cardinal_inter_diff_minus:
      forall s s', AG.cardinal (AG.inter s s') = AG.cardinal s - AG.cardinal (AG.diff s s').
    Proof.
      intros.
      apply Minus.plus_minus.
      apply sym_equal.
      apply AGProps.diff_inter_cardinal.
    Qed.
    Theorem AG_subset_diff_add:
      forall s s' x, AG.Subset s s' -> ~ AG.In x s -> AG.In x s' -> 
        AG.Subset (AG.diff s' (AG.add x s)) (AG.diff s' s).
    Proof.
      intros.
      unfold AG.Subset; intros a Hin.
      AGFacts.set_iff.
      split. apply (AG.diff_1 Hin); auto.
      generalize (AG.diff_2 Hin); intros H2.
      intro Hf.
      apply H2.
      AGFacts.set_iff; tauto.
    Qed.

    Theorem subset_complete_AG: forall i N, AG_all_objs i N ->
      forall C, complete_AG N C -> AG.Subset i C.
    Proof.
      intros.
      unfold AG_all_objs in *; unfold complete_AG in *; unfold AG.Subset; intros edge H1.
      rewrite <- (Edges.edge_rewrite edge) in *.
      generalize (H _ _ _ H1); intros Hcase; destruct Hcase.
      apply H0; auto.
    Qed.
    Theorem subset_complete_ag: forall i, AG.Subset i (complete_ag (ag_objs i)).
    Proof.
      intros.
      apply subset_complete_AG with (N:=(ag_objs i)); 
        [apply AG_all_objs_ag_objs |
          apply fold_AG_complete_ag].
    Qed. 
    Theorem transfer_nonempty: forall A B, transfer A B -> exists edge, AG.In edge A.
    Proof.
      intros.
      destruct H; eapply ex_intro; apply H.
    Qed.

 Function potAcc_fun (i:AG.t) {measure dist_from_complete i}: AG.t :=
    match findTransferEdge i with
      | None => i
      | Some edge => potAcc_fun (AG.add edge i)
    end.
 Proof.
    intros i edge H.
    unfold dist_from_complete.
    generalize (AGProps.diff_inter_cardinal (complete_ag (ag_objs i)) i); intros Hcard1.
    generalize (AGProps.diff_inter_cardinal (complete_ag (ag_objs (AG.add edge i))) (AG.add edge i)); intros Hcard2.
    let rewrite_diff := 
      fun Hcard => 
        apply sym_eq in Hcard; 
          rewrite Plus.plus_comm in Hcard;
            apply Minus.plus_minus in Hcard
              in
              rewrite_diff Hcard1; rewrite_diff Hcard2.
    generalize (findTransferEdge_general i); intros HtransEdgeP.
    unfold findTransferEdge_A_P in HtransEdgeP.
    rewrite H in HtransEdgeP.
    destruct HtransEdgeP as [Hcomplete Hrest].
    destruct Hrest as [Hnotin Htrans].
    generalize (Htrans _ (AGProps.Add_add i edge)); clear Htrans; intros Htrans.
    rewrite <- (Edges.edge_rewrite edge) in Hcomplete.
    apply complete_AG_conv_complete_ag in Hcomplete.
    destruct Hcomplete.

    (* note, we can't actually rewrite ag_objs, but we can prove equality.
       This is good enough as it lets us rewrite cardinality over equal sets. *)
    (* from here, we can rewrite (ag_objs (AG.add edge i)) into (ag_objs i),
       if (source edge) and (target edge) are in (ag_objs i) *)
    (* (source edge) and (target edge) are in (ag_objs i) because
       findTransferEdge_A_P i (complete_ag (ag_objs i)) (findTransferEdge i) holds.  (findTransferEdge i) matches Some edge.
       by the findTransferEdge_A_P_i, that edge is in (complete_ag (ag_objs i)). *)
    (* rewrite each value for it's result in the goal. *)
    (* We now have:
       let e:= edge in
       let card_compl := card (compl (objs i)) in
       (card_compl - (card (inter (compl (objs i)) (add e i)))) < 
       (card_compl - (card (inter (compl (objs i)) i) *)
    (* apply Minus.minus_le_compat_l to factor out card_compl *)
    (* now we have
       S (card (inter (compl (objs i))) i) <= 
         (card (inter (compl (objs i))) (add e i)) 
         *)
    (* There should be a theorem about factoring intersection into union, or we make one *)
    (* this should boil down to factoring out (compl (objs i)) and since e is in (compl (objs i)),
       the intersection is precicely one larger. *)
    generalize (ag_objs_equal H0 H1 (AGProps.Add_add i edge)); intros Heq.
    apply compat_op_complete_ag in Heq.
    generalize (AGProps.Equal_cardinal Heq); intros HeqCard.

    repeat rewrite AG_cardinal_diff_inter_minus.
    rewrite <- HeqCard.

    idtac.
    apply minus_lt_compat_l.
    (* 1. minus step: (card (inter compl i) < (card (inter (compl+e) i)) *)
    generalize (AGProps.inter_equal_1 (AG.add edge i) Heq); intros Hinter1.
    rewrite <- (AGProps.Equal_cardinal Hinter1); clear Hinter1.

    idtac.
    repeat rewrite AG_cardinal_inter_diff_minus.
    apply minus_lt_compat_l.
    (* 2. minus step: (card (diff compl (add e i))) < (card (diff compl i)) *)
    (* s [<=] s' -> ~ In x s -> In x s' -> diff s' (add x s) [<=] diff s' s *)

    idtac.
    apply AGProps.subset_cardinal_lt with edge; auto.
    (* 3. subset_cardinal_lt: subset case *)
    apply AG_subset_diff_add; auto.
    (* 4. AG_subset_diff_add subset case *)

    idtac.
    apply subset_complete_ag.
    (* 4. AG_subset_diff_add in case of course it's complete *)
    generalize (fold_AG_complete_ag (Edges.right edge) H0 H1);
      rewrite (Edges.edge_rewrite edge); auto.
    (* 3. subset_cardinal_lt: In e (diff compl i) *)
    (* follows from In e compl /\ ~ In e i *)
    apply AG.diff_3; auto;
      generalize (fold_AG_complete_ag (Edges.right edge) H0 H1);
        rewrite (Edges.edge_rewrite edge); auto.
    (* 3. subset_cardinal_lt: ~ In e (diff compl (add e i)) *)
    (* follows from In e compl /\ ~ In e i *)
    AGFacts.set_iff.
    intro H2; destruct H2 as [_ H3]; apply H3; left; apply Edge.eq_refl.
    (* 2. minus precondition: card (diff compl i) < card compl *)
    (* should follow from subset_cardinal_lt, and subset_diff *)

    idtac.
    apply AGProps.subset_cardinal; auto.
    apply AGProps.subset_diff; auto.
    (* 1. minus precondition: card (inter compl+e (add e i)) <= card compl *)
    (* (add e i) [<=] compl -> (inter compl (add e i)) [=] (add e i) *)
    generalize (AGProps.inter_subset_equal (@subset_complete_ag (AG.add edge i))); intros HinterC.
    generalize (AGProps.inter_sym (AG.add edge i) (complete_ag (ag_objs (AG.add edge i))));
      intros Hinter2.
    eapply AGProps.equal_trans in Hinter2; [| apply AGProps.equal_sym in HinterC; apply HinterC].
    apply AGProps.Equal_cardinal in Hinter2. 
    rewrite <- Hinter2.
    clear Hinter2 HinterC.
    rewrite HeqCard.
    apply AGProps.subset_cardinal.
    apply subset_complete_ag.
  Qed.

  Theorem transfer_potTransfer_potTransfer: forall a b c, transfer a b -> potTransfer b c -> potTransfer a c.
  Proof.
    intros.
    induction H0; eauto.
  Qed.

  Theorem potTransfer_potAcc_fun : forall i, potTransfer i (potAcc_fun i).
  Proof.
    intros.
    apply potAcc_fun_ind.
    (* base case *)
    intros i' H. 
    apply potTransfer_base.
    apply AGProps.equal_refl.
    (* step *)
    intros i' edge H H1.
    generalize (findTransferEdge_general i'); intros Hf.
    rewrite H in Hf.
    simpl in Hf.
    destruct Hf as [H2 Hf]; destruct Hf as [H3 H4].
    generalize (H4 _ (AGProps.Add_add i' edge)); intros Htrans.
    eapply transfer_potTransfer_potTransfer; auto.
  Qed.

  Theorem option_inequal: forall A:Type, Some A <> None.
  Proof.
    intros.
    intro.
    discriminate H.
  Qed.

  Theorem findTransferEdge_none_maxTransfer: forall i, 
    findTransferEdge i = None -> maxTransfer i.
  Proof.
    intros.
    generalize (findTransferEdge_general i); intros.
    unfold findTransferEdge_A_P in *.
    rewrite H in H0.
    (* okay, we know from not_in_complete_not_transfer,
       that we only need to consider the complete ag *)
    unfold maxTransfer.
    intros.
    generalize 
      (@not_in_complete_not_transfer
        _ _ (@AG_all_objs_ag_objs i) 
        _ (@fold_AG_complete_ag (ag_objs i))
        a); intros.
    unfold AG.Equal.
    intros edge.
    (* I am here *)
    split.
    apply transfer_subset; auto.
    intros.
    (* either there is an edge to add in the complete graph, or not *)
    case (complete_case (@AG_all_objs_ag_objs i) 
      (@fold_AG_complete_ag (ag_objs i)) a); intros Hcompl.
    (* edge exists *)
    destruct Hcompl as [edge' Hcompl]; destruct Hcompl as [HcAdd HcIn].    
    (* either edge' is in i or not *)
    case (AGProps.In_dec edge' i); intros.
    (* In edge' i *)
    (* case eq_dec edge edge' *)
    case (Edge.eq_dec edge edge'); intros.
    apply AG.In_1 with (y:=edge) in i0; apply Edge.eq_sym in e; eauto.
    (* edge <> edge' -> In edge i *)
    generalize (HcAdd edge); intros HedgeAdd.
    destruct HedgeAdd as [Hadd _ ].
    apply Hadd in H3.
    destruct H3; auto.
    apply (@Edge.eq_sym edge' edge) in H3; contradiction.
    (* ~ In edge' i, apply H0. *)
    absurd (transfer i a); auto.
    apply H0 with edge'; auto.
    (* edges does not exist *)
    absurd (transfer i a); auto.
  Qed.

  Definition willMaxTransfer (i i':AG.t) :=
    match findTransferEdge i' with
      | None => maxTransfer i'
      | Some edge => False
    end.
  
  Theorem willMaxTransfer_potAcc_fun: forall i, willMaxTransfer i (potAcc_fun i).
  Proof.
    intros.
    apply potAcc_fun_ind.
    (* base case *)
    intros. unfold willMaxTransfer; intros.
    rewrite e.
    apply findTransferEdge_none_maxTransfer; auto.
    (* inductive step *)
    intros.
    unfold willMaxTransfer in *; intros.
    assumption.
  Qed.

  Definition willNotFindTransfer (i i':AG.t) := findTransferEdge i' = None.

  Theorem willNotFindTransfer_potAcc_fun:
    forall i, willNotFindTransfer i (potAcc_fun i).
  Proof.
    intros.
    apply potAcc_fun_ind.
    (* base case *)
    intros; unfold willNotFindTransfer; intros.
    rewrite e; trivial.
    (*ind step*)
    intros.
    unfold willNotFindTransfer in *.
    assumption.
  Qed.
    

  Theorem potAcc_potAcc_fun: forall i, potAcc i (potAcc_fun i).
  Proof.
    intros.
    unfold potAcc.
    split.
    apply potTransfer_potAcc_fun.
    generalize (willNotFindTransfer_potAcc_fun i); intros H.
    unfold willNotFindTransfer in H.
    generalize (findTransferEdge_none_maxTransfer H).
    intros.
    generalize (maxTransfer_maxPotTransfer (potAcc_fun i)); intros Htrans.
    destruct Htrans; auto.
  Qed.
    
  Theorem exists_potAcc: forall (i:AG.t), exists max:AG.t, potAcc i max.
  Proof.
    intros.
    eapply ex_intro with (potAcc_fun i).
    apply potAcc_potAcc_fun.
  Qed.

    Theorem potTransfer_eq: forall i i' p p', AG.Equal i i' -> AG.Equal p p' -> potTransfer i p -> potTransfer i' p'.
    Proof.
      intros.
      induction H1.
      constructor 1.
      apply AG.eq_trans with i; [apply AG.eq_sym; auto|].
      apply AG.eq_trans with c; auto.

      apply potTransfer_transitive with i.  apply potTransfer_base; apply AG.eq_sym; auto.
      constructor 2 with b; auto.  
      eapply transfer_equality; eauto.
    Qed.

  Theorem potAcc_eq_potAcc_fun: forall i p, potAcc i p <-> AG.Equal p (potAcc_fun i).
  Proof.
    intros; split; intros.
    destruct H as [Hptrans Hmax].
    generalize (potAcc_potAcc_fun i); intros [Hptrans' Hmax'].
    generalize (potTransfer_lub Hptrans Hptrans'); intros [c [HptransC HptransC']].
    unfold maxPotTransfer in *.
    generalize (Hmax _ HptransC'); intros HeqC'.
    generalize (Hmax' _ HptransC); intros HeqC.
    apply AG.eq_trans with c; [|apply AG.eq_sym]; auto.

    generalize (potAcc_potAcc_fun i); intros [Hptrans Hmax].
    split.

    idtac.
    eapply potTransfer_eq; eauto.

    unfold maxPotTransfer in *.
    eapply AG.eq_sym in H.
    intros.
    apply AG.eq_trans with (potAcc_fun i); [apply AG.eq_sym; apply H|].
    apply Hmax.
    eapply potTransfer_eq; eauto.
  Qed.
  
  Theorem potAcc_dec: forall i p, {potAcc i p} + {~ potAcc i p}.
  Proof.
    intros.
    generalize (potAcc_eq_potAcc_fun i p); intros [H H'].
    case (AG.eq_dec p (potAcc_fun i)); intros Hcase; 
      [left; eapply H' in Hcase | right; intro; apply Hcase; eapply H]; auto.
  Qed.

  Theorem transfer_add_lub: forall (i a b:AG.t) edge,
    transfer i a -> AGProps.Add edge i b -> exists c:AG.t, AGProps.Add edge a c /\ transfer b c.
  Proof.
    intros i a b edge Tia Aib.
    generalize (transfer_edge Tia); intro Aia. 
    destruct Aia as [Eia Aia].
    assert (exists c:AG.t, AGProps.Add edge a c) as Hadd; eauto.
    destruct Hadd as [c Hadd].
    apply ex_intro with c.
    split; [eauto|].
    eapply transfer_monotonic; eauto.
    eapply AGAddEq.Add_lub; eauto.
  Qed.

  Hint Resolve transfer_add_lub.

(* move to FSetAddEq *)
    Theorem Add_preserves_Subset: forall x A A' B B',
      AG.Subset A B -> AGProps.Add x A A' -> AGProps.Add x B B' -> AG.Subset A' B'.
    Proof.
      intros.
      intros x' Hin.
      eapply H0 in Hin; destruct Hin as [Hin|Hin].
      assert (Edge.eq x x'); eauto; clear Hin.
      apply Edges.eq_equal in H2; rewrite <- H2; clear H2.
      eapply H1; eauto.

      eapply H1; eauto.
    Qed.

  Theorem transfer_subset_lub: forall (i a b:AG.t),
    transfer i a -> AG.Subset i b -> exists c, AG.Subset a c /\ transfer b c.
  Proof.
    intros i a b Tia Sib.
    generalize (transfer_edge Tia); intros [Eia Aia].
    assert (exists c:AG.t, AGProps.Add Eia b c /\ transfer b c) as [c [Abc Tbc]]; eauto.
    eapply ex_intro with c; split; eauto.

    eapply Add_preserves_Subset; eauto.
  Qed.

  Hint Resolve Add_preserves_Subset.

  Hint Resolve transfer_subset_lub.

  Theorem potTransfer_subset_lub: forall (i a b:AG.t),
    potTransfer i a -> AG.Subset i b -> exists c, AG.Subset a c /\ potTransfer b c.
  Proof.
    intros.
    induction H.
    (* base *)
    eapply ex_intro with b; split; eauto.
    intros edge Hin; eapply H0; eapply H; eauto.
    (* step *)
    rename b0 into a'; rename c into a.
    destruct IHpotTransfer as [c [Sa'c Pbc]].
    (* what we can potTransfer to is some c' where transfer c c' by the same edge transfer a' a. *)
    generalize (transfer_edge H1); intros [Eia' Aia'].
    assert (exists c', AGProps.Add Eia' c c' /\ transfer c c') as [c' [Acc' Tcc']]; eauto.
  Qed.

Hint Resolve potTransfer_subset_lub.

Theorem potAcc_monotonic: forall i i' p p',
    AG.Subset i i' -> potAcc i p -> potAcc i' p' -> AG.Subset p p'.
Proof.
   intros i i' p p' Sii' Pip Pi'p'.
   destruct Pip as [Pip Mp]; destruct Pi'p' as [Pi'p' Mp'].
   generalize (potTransfer_subset_lub Pip Sii'); intros [c [Spc Pi'c]].
   (* by potTransfer_lub: exists c', potTransfer c c' /\ potTransfer p' c'.
      by Mp' and above: c' [=] p'
      by potTransfer_subset: c [<=] c' so c [<=] p'
      by subset_trans and Spc: p [<=] p' *)
   generalize (potTransfer_lub Pi'p' Pi'c); intros [c' [Pcc' Pp'c']].
   apply AGProps.subset_trans with c'; [eapply AGProps.subset_trans; eauto|].
   apply AGProps.subset_equal.  apply AG.eq_sym. eapply Mp'; eauto.
Qed.

Definition ag_add_commute F := forall ag ag' x, AGProps.Add x ag ag' -> AGProps.Add x (F ag) (F ag').


Theorem transfer_commute_monotonic: forall Fa, ag_add_commute Fa -> ag_nondecr Fa -> 
forall i a, transfer i a -> transfer (Fa i) (Fa a).
Proof.
    intros Fa Hcomm Hmono i a Tia.
    generalize (transfer_edge Tia); intros [Eia Aia].
    generalize (Hcomm i a Eia); intros HAFiFa.
    generalize (HAFiFa Aia); clear HAFiFa; intros HAFiFa.
    eauto.
Qed.

Hint Resolve transfer_commute_monotonic.

Definition ag_equiv Fa := forall ag ag', AG.Equal ag ag' -> AG.Equal (Fa ag) (Fa ag').

  Theorem Add_notEmpty : forall ag ag' edge, AGProps.Add edge ag' ag -> ~ AG.Empty ag.
  Proof.
    intros.
    unfold AG.Empty in *.
    intro Hnot.
    eapply Hnot.
    eapply H.
    left.
    eauto.
  Qed.

  Require Bool.

  Theorem compat_P_In : forall A:AG.t, SetoidList.compat_P Edge.eq (fun edge => AG.In edge A).
  Proof.
    unfold SetoidList.compat_P.
    intros.
    unfold Proper; unfold respectful. unfold Basics.impl. intros.
    apply AG.In_1 with x; auto.
  Qed.  
  Hint Resolve compat_P_In.

  Theorem not_Empty_exists_In : forall ag, ~ AG.Empty ag -> exists x, AG.In x ag.
  Proof.
    intros.
    generalize (AGDep.exists_ (fun x => (AGProps.In_dec x ag)) ag). intros Hcase.
    destruct Hcase.

idtac.
  unfold AG.Exists in e.
  generalize (e (@compat_P_In ag)).
  intros [x [Hadd Hadd']]; eauto.

  generalize (n (@compat_P_In ag)); intros.
  unfold AG.Exists in *. 
  unfold AG.Empty in *.
  firstorder.
  Qed.

Definition ag_potTransfer_fn_req Fa := ag_add_commute Fa /\ ag_nondecr Fa /\ ag_equiv Fa.

Theorem potTransfer_commute_monotonic: forall Fa, ag_potTransfer_fn_req Fa ->
forall i a, potTransfer i a -> potTransfer (Fa i) (Fa a).
Proof. 
  intros Fa [Hcomm[ Hmono Hequiv]] i a Pia.
  induction Pia; eauto.
Qed.

Theorem potAcc_commute_monotonic: forall Fa, ag_potTransfer_fn_req Fa ->
forall i p, potAcc i p -> forall p2, potAcc (Fa i) p2 <-> potAcc (Fa p) p2.
Proof.
  intros Fa Hfn i p [Pip Mp] p2.
  generalize (potTransfer_commute_monotonic Hfn Pip); intros PFiFp.
  split; intros [Pnew Mp2].

  generalize (potTransfer_lub PFiFp Pnew); intros [c [Pnew_1 Pnew_2]].
  apply Mp2 in Pnew_1; apply AG.eq_sym in Pnew_1.
  split; auto.
  apply potTransfer_base in Pnew_1.
  eapply potTransfer_transitive; eauto.

  split; auto.
  eapply potTransfer_transitive; eauto.
Qed.

Theorem add_add_commute: forall x, ag_add_commute (AG.add x).
Proof.
  unfold ag_add_commute; intros x ag ag' y H.
  eapply AGAddEq.Add_lub; try eapply H; try eapply AGProps.Add_add.
Qed.

Definition ag_subset_commute Fa := forall ag ag', AG.Subset ag ag' -> AG.Subset (Fa ag) (Fa ag').

Theorem ag_subset_add_commute: forall Fa, ag_add_commute Fa -> ag_equiv Fa -> ag_subset_commute Fa.
Proof.
  unfold ag_subset_commute in *; unfold ag_add_commute in *; unfold ag_equiv in *.
  intros Fa Hcomm Hequiv ag ag' H.
  generalize (AGAddEq.subset_fold_add_Equal _ _ H); intros Heq.
  generalize (Hequiv _ _ Heq); clear Heq; intros Heq.
  apply AGProps.subset_equal in Heq.
  eapply AGProps.subset_trans; [clear Heq|eauto].
  (* start induction *)
  eapply AGProps.fold_rec_nodep.
  (* base *)
  apply AGProps.subset_refl.
  (* step *)
  clear H.
  intros x a Hin Hsub. clear Hin.
  generalize (Hcomm _ _ _ (AGProps.Add_add a x)); intros H.
  eapply AGProps.subset_trans; [eapply Hsub | intros edge HinE; eapply H; intuition].
Qed.

  Definition potTransferLT (I A B:AG.t) := potTransfer I A /\ potTransfer I B /\ potTransfer A B.

End MakeSeqAcc.
