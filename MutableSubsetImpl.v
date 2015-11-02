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
Require Import MutabilityImpl.
Require Import Mutation.
Require Import AccessExecutionImpl.
Require Import Morphisms.
Require Import Basics.
(* type_remove *)
Require Import MutableSubset.

Module MakeMutableSubset (Ref:ReferenceType) (RefS: RefSetType Ref)(Edges: AccessEdgeType Ref) (AccessGraph:AccessGraphType Ref Edges) (Seq:SeqAccType Ref RefS Edges AccessGraph) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) (SemDefns: SemanticsDefinitionsType Ref Cap Ind Obj Sys) (Sem: SemanticsType Ref RefS Cap Ind Obj Sys SemDefns) (Exe: ExecutionType Ref RefS Cap Ind Obj Sys SemDefns Sem) (Mut: MutationType Ref RefS Cap Ind Obj Sys SemDefns Sem Exe) : MutableSubsetType Ref RefS Edges AccessGraph Seq Cap Ind Obj Sys SemDefns Sem Exe Mut.

Module Mutable := MakeMutability Ref RefS Edges AccessGraph Seq.
Module AE := MakeAccessExecution Ref RefS Edges AccessGraph Seq Cap Ind Obj Sys SemDefns Sem Exe.

Import Mutable.
Import Mut.
Import AE.
Import RefS.


(* toss into SequentialAccess.v *)
  Theorem potAcc_self_loop: 
    forall i p, Seq.potAcc i p ->
      forall n, Seq.ag_objs_spec p n ->
        forall x, RefSet.In x n ->
          forall r, AG.In (Edges.mkEdge x x r) p.
  Proof.
    intros i p Hpa n Hn x Hin r.
    destruct Hpa as [Htrans Hmax].
    eapply Hn in Hin. destruct Hin as [obj [rgt [Hin|Hin]]];

    [eapply Seq.transfer_self_src in Hin; [|apply AGProps.Add_add] 
      | eapply Seq.transfer_self_tgt in Hin; [|apply AGProps.Add_add]];
    (eapply Seq.maxTransfer_maxPotTransfer in Hmax; eapply Hmax in Hin;
        rewrite Hin; eapply AGFacts.add_iff; intuition eauto).
  Qed.



Theorem mutable_reduce:
forall p Nr p', AG_attenuating Nr p p' ->
forall E, RefSet.Subset E Nr ->
forall m, mutable_spec p (RefSet.inter E Nr) m ->
forall m', mutable_spec p' E m' ->
RefSet.Subset (RefSet.inter m' Nr) m.
Proof.
  intros p Nr p' Hred E HE m Hm m' Hm' x Hin.
  eapply RefSetFacts.inter_iff in Hin; destruct Hin as [HinM' HinNr].
  eapply Hm' in HinM'; clear Hm'; eapply Hm; clear Hm.
  destruct HinM' as [HinE | Hex];[left; eapply RefSetFacts.inter_iff; intuition auto|].
  destruct Hex as [e [HinE Hedge]].
  eapply AG_attenuating_converse_iff in Hred.
  destruct Hedge as [Hedge | [Hedge | [Hedge | Hedge]]];
    (eapply Hred in Hedge; auto; destruct Hedge as [Heq|Hin];
      [unfold Ref.eq in Heq; rewrite Heq in *; left; eapply RefSetFacts.inter_iff; intuition auto
        | right; eapply ex_intro; split; [eapply RefSetFacts.inter_iff; intuition eauto | intuition auto]]).
Qed.


      Ltac rewrite_case_option opt some Hcase := 
        case (option_sumbool opt); intros Hcase; [|destruct Hcase as [some Hcase]]; 
        rewrite Hcase in *; simpl in *.



Definition obj_existed n s := forall x, RefSet.In x n <-> (SC.is_alive x s \/ SC.is_dead x s).

Require Import Sumbool_dec.

Definition existed_f s := Sys.MapS.fold 
  (fun k v a => 
    let lbl := (SC.tupleGetLabel v) in 
      if (orb (true_bool_of_sumbool (ObjectLabel.eq_dec lbl alive))
        (true_bool_of_sumbool (ObjectLabel.eq_dec lbl dead)))  then
          (RefSet.add k a)
        else
          a )
  s RefSet.empty.

  Theorem existed_f_iff: forall x s,
    RefSet.In x (existed_f s) <-> (SC.is_alive x s \/ SC.is_dead x s).
  Proof.
    intros x s.
    unfold existed_f.
    eapply Sys_Props.fold_rec_bis; intros.
  (* compat *)
  eapply iff_trans; [apply H0 | clear H0].
  split; intros [Hlbl|Hlbl]; intuition (eapply SC.isLabel_eq;
    try solve [apply Hlbl
      | apply Ref.eq_refl 
      | apply ObjectLabel.eq_refl
      | eapply Sys_MapEquiv.Equal_eq; apply H
      | eapply Sys.eq_sym; eapply Sys_MapEquiv.Equal_eq; apply H]).
  (* base *)
  eapply iff_trans; [eapply RefSetFacts.empty_iff|].
  split; intros; try contradiction.
  unfold SC.is_alive in *; unfold SC.is_dead in *;
  unfold SC.is_label in *; unfold SC.getLabel in *;
  unfold SC.getObjTuple in *;
  rewrite Sys_Facts.empty_o in H; simpl in H; intuition.
  (* step *)
  destruct e as [[[obj lbl] typ] sch]; simpl in *.

   Ltac solver_21 x m' H0 := solve 
          [rewrite Sys_Facts.add_eq_o; simpl in *;[apply ObjectLabel.eq_refl|apply eq_refl]
            | rewrite Sys_Facts.add_neq_o; simpl in *; unfold Sys.P.t in *;
              let tuple := fresh "tuple" in
                let Hcase2 := fresh "Hcase" in
                  rewrite_case_option (Sys.MapS.find x m') tuple Hcase2;
              solve [contradiction
                | auto
                | intros Hnot; rewrite Hnot in *; eapply Sys_Facts.not_find_in_iff in H0; 
                  rewrite H0 in *; discriminate Hcase2]].

  Ltac solver_23 x m' H0 H1 k:=
     let Hx := fresh "Hx" in 
      split; intros Hx;
        unfold SC.is_alive in *; unfold SC.is_dead in *; 
          unfold SC.is_label in *; unfold SC.getLabel in *; unfold SC.getObjTuple in *;
            [eapply RefSetFacts.add_iff in Hx; destruct Hx as [Heq | Hin];
              solve [rewrite Heq in *; left; solver_21 x m' H0 
                | rewrite Heq in * ; right; solver_21 x m' H0 
                | eapply H1 in Hin; destruct Hin as [Halive |Hdead]; [left|right]; solver_21 x m' H0 ]
              |
  (* and the inverse *)
                case (Ref.eq_dec k x); intros HCase;
                  eapply RefSetFacts.add_iff; 
                    [left; solve[auto]
                      |right;
                        apply H1; destruct Hx as [Hx|Hx] ; [left|right];
                          (let tuple := fresh "tuple" in let Hcase2 := fresh "Hcase2" in
                            rewrite Sys_Facts.add_neq_o in Hx; auto; 
                              rewrite_case_option (Sys.MapS.find x m') tuple Hcase2;
                              try contradiction; auto)]
            ].
  
  case (ObjectLabel.eq_dec lbl alive); intros Hcase; simpl in *;
    [rewrite Hcase in *; solver_23 x m' H0 H1 k 
      |case (ObjectLabel.eq_dec lbl dead); intros Hcase'; simpl in *;
        [rewrite Hcase' in *; solver_23 x m' H0 H1 k|]].

  destruct lbl;
  try solve [generalize (Hcase (eq_refl _)); contradiction
    |generalize (Hcase' (eq_refl _ )); contradiction].

  (* contradictions all around when k = x *)
  case (Ref.eq_dec k x); intros Hcase3.

  unfold Ref.eq in Hcase3; rewrite Hcase3 in *;
  eapply Sys_Facts.not_find_in_iff in H0;
  unfold SC.is_alive in *; unfold SC.is_dead in *; 
    unfold SC.is_label in *; unfold SC.getLabel in *; unfold SC.getObjTuple in *;
  unfold Sys.P.t in *; rewrite H0 in *; simpl in *;
  split; intros H2;
    [eapply H1 in H2; intuition contradiction
      |  rewrite Sys_Facts.add_eq_o in H2; 
    [simpl in *; destruct H2 as [H2 | H2]; unfold ObjectLabel.eq in H2; discriminate H2
      |solve[auto]]].

  (* k <> x *)
  unfold SC.is_alive in *; unfold SC.is_dead in *; 
    unfold SC.is_label in *; unfold SC.getLabel in *; unfold SC.getObjTuple in *;
  rewrite Sys_Facts.add_neq_o; [|auto]; simpl.
  unfold Sys.P.t in *.
  rewrite_case_option (Sys.MapS.find x m') tuple Hcase2; auto.
Qed.


Theorem obj_existed_eq_existed_f : forall n s, obj_existed n s <-> RefSet.eq n (existed_f s).
Proof.
  intros n s; split; intros H x; (eapply iff_trans; [eapply H|clear H]).
eapply iff_sym.
eapply existed_f_iff.
eapply existed_f_iff.
Qed.

Theorem obj_existed_eq_iff: 
  forall s s', Sys.eq s s' -> forall n, obj_existed n s -> forall n', obj_existed n' s' -> RefSet.eq n n'.
Proof.
  intros s s' Heq n Hn n' Hn'.
  eapply RefSetEqEqual.eq_Equal. unfold RefSet.Equal; intros a.
  eapply iff_trans; [apply Hn| eapply iff_trans; [|apply iff_sym; apply Hn']].
  clear Hn Hn'.
  unfold SC.is_alive; unfold SC.is_dead.
  intuition (eapply SC.isLabel_eq; solve [eauto| apply Ref.eq_refl | apply ObjectLabel.eq_refl]). 
Qed.


(* TODO : Fix implicit arguments of the theorems below *)
(* follows a similar pattern to objs_not_unborn_op *)
Theorem remains_existed_op:  forall Ex s, obj_existed Ex s ->
  forall op s', Sys.eq (Sem.do_op op s) s' -> forall Ex', obj_existed Ex' s' -> RefSet.Subset Ex Ex'.
Proof.
  intros Ex s Hex op s' Hexe Ex' Hex'.
  intros x Hx.
  eapply Hex'.
  eapply Hex in Hx.
  clear Hex Hex'.
  unfold SC.is_alive in *; unfold SC.is_dead in *.
  destruct op; simpl in *.
  Implicit Arguments is_label_read [a t s s'].
  Implicit Arguments is_label_write [a t s s'].
  destruct Hx as [Hx | Hx]; eapply (is_label_read Hexe) in Hx; intuition.
  destruct Hx as [Hx | Hx]; eapply (is_label_write Hexe) in Hx; intuition.
  Implicit Arguments is_label_fetch_valid [a t c i s s'].
  Implicit Arguments is_label_fetch_invalid [a t c i s s'].
  case (SemDefns.fetch_preReq_dec t t0 s); intros Hcase;
      [ destruct Hx as [Hx | Hx]; eapply (is_label_fetch_valid Hexe Hcase) in Hx; intuition 
        | destruct Hx as [Hx | Hx]; eapply (is_label_fetch_invalid Hexe Hcase) in Hx; intuition].
  Implicit Arguments is_label_store_valid [a t c i s s'].
  Implicit Arguments is_label_store_invalid [a t c i s s'].
  case (SemDefns.store_preReq_dec t t0 s); intros Hcase;
      [ destruct Hx as [Hx | Hx]; eapply (is_label_store_valid Hexe Hcase) in Hx; intuition 
        | destruct Hx as [Hx | Hx]; eapply (is_label_store_invalid Hexe Hcase) in Hx; intuition].  
  Implicit Arguments is_label_revoke_valid [a t c s s'].
  Implicit Arguments is_label_revoke_invalid [a t c s s'].
  case (SemDefns.revoke_preReq_dec t t0 s); intros Hcase;
      [ destruct Hx as [Hx | Hx]; eapply (is_label_revoke_valid Hexe Hcase) in Hx; intuition 
        | destruct Hx as [Hx | Hx]; eapply (is_label_revoke_invalid Hexe Hcase) in Hx; intuition].  
  Implicit Arguments is_label_send_valid [a t c i s s'].
  Implicit Arguments is_label_send_invalid [a t c i s s'].
  case (SemDefns.send_preReq_dec t t0 s); intros Hcase;
      [ destruct Hx as [Hx | Hx]; eapply (is_label_send_valid Hexe Hcase) in Hx; intuition 
        | destruct Hx as [Hx | Hx]; eapply (is_label_send_invalid Hexe Hcase) in Hx; intuition].  
  Implicit Arguments is_label_allocate_invalid [a t c i s s'].
  Ltac solver_50 x t0 := case (Ref.eq_dec x t0); intros; try contradiction; auto.

  case (SemDefns.allocate_preReq_dec t t0 s); intros Hcase;
    [ | destruct Hx as [Hx | Hx]; eapply (is_label_allocate_invalid Hexe Hcase) in Hx; intuition].
  case (Ref.eq_dec x t0); intros Hcase2; [ unfold Ref.eq in Hcase2; rewrite Hcase2 in * |].
  left; eapply is_label_allocate_valid; eauto 1.
  case (Ref.eq_dec t0 t0); intros Hcase3;
  solve [generalize (Hcase3 (Ref.eq_refl _)); intros; contradiction
    | split; solve [apply ObjectLabel.eq_refl | destruct Hcase; intuition]].
  destruct Hx as [Hx | Hx]; [left|right];
    (eapply is_label_allocate_valid; eauto 1).
  (* I don't know why I'm getting an ill-typed term when separating cases, but it's very confusing 
     It probably has to do with why Ref.eq_dec is unfolding to to some inner module of RefSetFoldOrder 
     The prover may just be in a bad state ATM. *)
  case (Ref.eq_dec x t0); intros; try contradiction; auto.
  case (Ref.eq_dec x t0); intros; try contradiction; auto.
  
  Implicit Arguments is_label_destroy_invalid [a t s s'].
  case (SemDefns.destroy_preReq_dec t t0 s); intros Hcase;
    [ | destruct Hx as [Hx | Hx]; eapply (is_label_destroy_invalid Hexe Hcase) in Hx; intuition].
  generalize Hcase; intros Hcase'.
  destruct Hcase' as [[[Halive Hactive] Htalive] Hright].
  rewrite_case_option (SC.getCap t0 t s) cap Hcap; try contradiction.

  Require Import OptionMap2.

  case (option_map_eq_dec RefSetFoldOrder.FEq.Props.FM.eq_dec 
      (Some x) (SemDefns.option_target (SC.getCap t0 t s)));
      intros Hcase2.

  right; eapply is_label_destroy_valid; eauto 1.
  unfold SemDefns.target_is_alive in Htalive.
  rewrite Hcap in *; simpl in *; rewrite <- Hcase2 in *; simpl in *.
  destruct option_map_eq_dec as [Hcase2' | Hcase2']; simpl in *; 
    try solve [generalize (Hcase2' (Ref.eq_refl _)); contradiction
    | intuition; solve [apply ObjectLabel.eq_refl| apply Halive]].
  

  destruct Hx as [Hx | Hx]; [left|right];
    (eapply is_label_destroy_valid; eauto 1).
  (* Same problem *)
  destruct option_map_eq_dec; try contradiction; auto.
  destruct option_map_eq_dec; try contradiction; auto.
Qed.

Theorem remains_existed: forall Ex s, obj_existed Ex s -> 
  forall opList s', Exe.execute_def s opList s' ->
  forall Ex', obj_existed Ex' s' ->
    RefSet.Subset Ex Ex'.
Proof.
  intros Ex s Hex opList s' Hexe. 
  induction Hexe; intros Ex' Hex'.
  (* base *)
  intros x Hx; eapply obj_existed_eq_iff; [apply Sys.eq_sym; apply H | apply Hex' | apply Hex | apply Hx].
  (* step *)
  eapply RefSetProps.subset_trans.
  apply IHHexe. apply obj_existed_eq_existed_f. apply RefSet.eq_refl.
  eapply remains_existed_op; [ | apply H | apply Hex'].
  apply obj_existed_eq_existed_f. apply RefSet.eq_refl.
Qed.

Theorem not_unborn_obj_existed: forall n s, obj_existed n s -> objs_not_unborn n s.
Proof.
  unfold objs_not_unborn; unfold obj_existed; intros.
  eapply H in H0.
  unfold SC.is_alive in *; unfold SC.is_unborn in *; unfold SC.is_dead in *.
  unfold SC.is_label in *; unfold SC.getLabel in *;
    unfold SC.getObjTuple in *.
  case (option_sumbool (Sys.MapS.find x s)); intros Hcase; 
    [|destruct Hcase as [[[[obj lbl] typ] sch]  Hcase]]; rewrite Hcase in *; simpl in *;
  intuition; try solve[rewrite H1 in H2; discriminate H2].
Qed.

Theorem obj_existed_potAcc_op:
  forall p p_objs, Seq.ag_objs_spec p p_objs ->
    forall Ex s, obj_existed Ex s -> RefSet.Subset p_objs Ex ->
      forall op p'_objs, Seq.ag_objs_spec (potAcc_op op s p) p'_objs ->
        forall s', Sys.eq (Sem.do_op op s) s' -> 
          forall Ex', obj_existed Ex' s' ->
            RefSet.Subset  p'_objs Ex'.
Proof.
  intros p p_objs Hp_objs Ex s Hex Happrox op p'_objs Hpotop s' Hop Ex' Hex' x Hx.
  generalize (remains_existed_op  _ _ Hex _ _ Hop _ Hex'); intros Hsub.
  destruct op; simpl in *; unfold id_ag in *;
    unfold endow_dep in *; try (revert Hpotop; case (SemDefns.allocate_preReq_dec t t0 s); intros Hcase Hpotop);
    try solve [ eapply ag_objs_spec_equiv in Hp_objs; [ | apply Hpotop | apply AG.eq_refl];
      eapply Hsub; eapply Happrox; eapply Hp_objs; eapply Hx].
  eapply ag_objs_spec_endow in Hpotop; [ | apply Hp_objs].
  generalize Hcase; intros [[Halive Hactive] Hunborn].
  (* by cases through add:
     x = t : t is alive, therefore it is in Ex and by approx in Ex'
     (x <> t):
       x = t0 : t is unborn, but we should know that it is added in exactly this case 
       (x <> t0) : out of adds, x must be in p_objs, and by subset qed.
       *)

  (* start with the asertion that t <> t0 *)
  case (Ref.eq_dec t t0); intros Heqcase; [
    unfold Ref.eq in Heqcase; rewrite Heqcase in *;
      destruct Hcase as [[Halive' Hactive'] Hunborn'];
        eapply SC.is_label_iff_getLabel in Halive;
          eapply SC.is_label_iff_getLabel in Hunborn;
            rewrite Halive in Hunborn;
              discriminate Hunborn |].
  
  case (Ref.eq_dec x t); intros Hcase1.
  (* x = t *)
  unfold Ref.eq in Hcase1; rewrite  Hcase1 in *.
  eapply Hex'. left.
  eapply is_label_allocate_valid; [ apply Hop | apply Hcase |].
  destruct Ref.eq_dec; intros; try contradiction; auto.
  (* x <> t *)
  case (Ref.eq_dec x t0); intros Hcase2.
  (* x = t0 *)
  unfold Ref.eq in Hcase2; rewrite  Hcase2 in *.
  eapply Hex'. left.
  eapply is_label_allocate_valid; [ apply Hop | apply Hcase |].
  destruct Ref.eq_dec as [Hcase3 | Hcase3] ; intros;
  try (generalize (Hcase3 (Ref.eq_refl _)); intro; contradiction).
  intuition (try apply ObjectLabel.eq_refl; try apply Hunborn).
  (* x <> t0 *)
  eapply Hpotop in Hx.
  eapply RefSetFacts.add_iff in Hx;
    destruct Hx as [Hx | Hx]; try (apply Ref.eq_sym in Hx; contradiction).
  eapply RefSetFacts.add_iff in Hx;
    destruct Hx as [Hx | Hx]; try (apply Ref.eq_sym in Hx; contradiction).
  eapply Happrox in Hx.
  eapply Hsub; auto.
Qed.


  
(* The entire objects properties should go into Sys, and into the Exe support library *)
(* I'm not convinced these are necessary anymore *)

(* Definition objects (S:Sys.t) N := forall e, (RefSet.In e N <-> Sys.MapS.In e S). *)

(* Require Import List. *)

(* Definition objects_f (S:Sys.t) := fold_right RefSet.add RefSet.empty (fst (split (Sys.MapS.elements S))). *)

(* Theorem objects_iff: forall N S, objects S N <-> RefSet.Equal (objects_f S) N. *)
(* Proof. *)
(* Admitted. *)

(* Theorem objects_exe_subset: forall S N, objects S N -> *)
(* forall opList S', Exe.execute_def S opList S' -> *)
(* forall N', objects S N' -> RefSet.Subset N N'. *)
(* Proof. *)
(* Admitted.  *)

(* Theorem existed_subset_objects : forall S N, objects S N -> *)
(*   forall Ex, obj_existed Ex S -> *)
(* RefSet.Subset Ex N. *)
(* Proof. *)
(* Admitted. *)
(* Hint Resolve existed_subset_objects. *)

(* Theorem obj_existed_unborn: forall objs s, objects s objs -> *)
(*   forall existed, obj_existed existed s -> *)
(*     forall n, RefSet.In n objs -> ~ RefSet.In n existed -> *)
(*       SC.is_unborn n s. *)
(* Proof. *)
(* Admitted. *)
(* Hint Resolve obj_existed_unborn. *)

(* Theorem ag_objs_subset_objects : forall s d, dirAcc_spec s d -> *)
(*   forall objs, Seq.ag_objs_spec d objs -> *)
(*   forall objs, objects s objs -> *)
(*     RefSet.Subset objs objs. *)
(* Proof. *)
(* Admitted. *)

(* 
Theorem mutable_reduce_2:
forall s Ex, obj_existed Ex s->
forall d, dirAcc_spec s d ->
forall p, Seq.potAcc d p ->
forall p' Ex', AG_attenuating_auth Ex Ex' p p' ->
forall E m, mutable_spec p (RefSet.inter E Ex) m ->
forall m', mutable_spec p' E m' ->
RefSet.Subset (RefSet.inter m' Ex) m.
 
*)


(* endow spec
  Seq.potAcc ag p -> Seq.ag_objs_spec p N -> ~ RefSet.In n N -> 
  AG.Equal (insert a n p) ag' -> Seq.potAcc ag' p' -> 
  forall src tgt rgt, 
   AG.In (Edges.mkEdge src tgt rgt) p' ->
    (AG.In (Edges.mkEdge src tgt rgt) p \/ 
     AG.In (Edges.mkEdge src a rgt) p /\ Ref.eq tgt n \/ 
     AG.In (Edges.mkEdge a tgt rgt) p /\ Ref.eq src n \/
     Ref.eq src n /\ Ref.eq tgt a \/
     Ref.eq src a /\ Ref.eq tgt n \/
     Ref.eq src n /\ Ref.eq tgt n \/
     Ref.eq src a /\ Ref.eq tgt a).
*)

(* This is just the endow_spec property for p to p' *)

Definition AG_project a n p p' := forall src tgt rgt, 
   AG.In (Edges.mkEdge src tgt rgt) p' <->
    (AG.In (Edges.mkEdge src tgt rgt) p \/ 
     AG.In (Edges.mkEdge src a rgt) p /\ Ref.eq tgt n \/ 
     AG.In (Edges.mkEdge a tgt rgt) p /\ Ref.eq src n \/
     Ref.eq src n /\ Ref.eq tgt a \/
     Ref.eq src a /\ Ref.eq tgt n \/
     Ref.eq src n /\ Ref.eq tgt n \/
     Ref.eq src a /\ Ref.eq tgt a).


Theorem Proper_AG_project : Proper (Ref.eq ==> Ref.eq ==> AG.eq ==> AG.eq ==> iff) AG_project.
Proof.
  unfold Proper; unfold respectful; unfold AG_project; intros; split; 
    (intros; generalize (H3 src tgt rgt); clear H3; intros H3;
      eapply iff_trans;
        [solve [eapply H2 | eapply iff_sym; eapply H2]|clear H2];
        rewrite H3; clear H3;
          rewrite H1;
  (* unfolding is faster, but won't work if it's opaque *)
            unfold Ref.eq in *;
              rewrite H; rewrite H0; clear H H0;
                eapply iff_refl).
Qed.



(* Move thses 4  Ltac to appropriate places, and move endow_spec* to Attenuation.v *)
      Ltac edge_simpl := 
        try rewrite Edges.source_rewrite in *; try rewrite Edges.target_rewrite in *; 
          try rewrite Edges.right_rewrite in *.
      Ltac cap_simpl :=
        try rewrite CC.mkCap_target in *; try rewrite CC.mkCap_rights in *.
  Ltac simpl_ag_add_cap :=
  repeat progress (
    match goal with
      | [ |- AG.In ?E (ag_add_cap ?S ?C ?R) ] => 
        eapply ag_add_cap_spec; [eapply AG.eq_refl|]; edge_simpl; cap_simpl;
          try solve [left; intuition 
            (try apply Ref.eq_refl; try apply AccessRight.eq_refl; try apply in_all_rights)];
          right
  end).

  Ltac solve_edge_insert Htrans Hinsert := 
  eapply Seq.potTransfer_subset; [apply Htrans|];
  eapply Hinsert; unfold insert;
  simpl_ag_add_cap.


Theorem endow_spec_2: forall a n ag p ag' p' N, 
  Seq.potAcc ag p -> Seq.ag_objs_spec p N -> ~ RefSet.In n N -> 
  AG.Equal (insert a n p) ag' -> Seq.potAcc ag' p' -> 
  forall src tgt rgt, 
    (AG.In (Edges.mkEdge src tgt rgt) p \/ 
     AG.In (Edges.mkEdge src a rgt) p /\ Ref.eq tgt n \/ 
     AG.In (Edges.mkEdge a tgt rgt) p /\ Ref.eq src n \/
     Ref.eq src n /\ Ref.eq tgt a \/
     Ref.eq src a /\ Ref.eq tgt n \/
     Ref.eq src n /\ Ref.eq tgt n \/
     Ref.eq src a /\ Ref.eq tgt a) ->
   AG.In (Edges.mkEdge src tgt rgt) p'.
Proof.
  intros a n ag p ag' p' N Hpa Hobjs Hnin Heq Hpa' src tgt rgt Hin.
  destruct Hpa' as [Htr' Hmax'].
  (* 
     This can be handled directly by cases:
     Generally, we know that In e p -> in e p'
     The refl and inter edges are handled by the edges added by insert.
     The projection edges can be handled by leveraging an edge on insert
     *)
  assert (AG.Subset p p') as Hsubset by
  (intros e HinE; eapply Seq.potTransfer_subset; [apply Htr' |]; 
  eapply Heq; unfold insert; eapply ag_add_cap_nondecr;
      [eapply ag_add_cap_nondecr; apply AGProps.subset_refl
      | apply HinE]).


  

  destruct Hin as [Hin | Hin].
  apply Hsubset; auto.

  destruct Hin as [[Hin HeqTgtN]| Hin].
  rewrite HeqTgtN in *.
  eapply Hsubset in Hin.

  destruct rgt.
  (*weak*)
  eapply Hmax'; [ eapply Seq.potTransfer_trans; [eapply Seq.potTransfer_base; apply AG.eq_refl|] 
    | eapply AGProps.Add_add; left; eapply Edges.edge_equal; solve[apply Ref.eq_refl|apply AccessRight.eq_refl]].
  eapply Seq.transfer_weak;
    [eapply Hin
      |solve_edge_insert Htr' Heq
      |intuition; eauto
      |eapply AGProps.Add_add; eauto].
  (*read*)
  eapply Hmax'; [ eapply Seq.potTransfer_trans; [eapply Seq.potTransfer_base; apply AG.eq_refl|] 
    | eapply AGProps.Add_add; left; eapply Edges.edge_equal; solve[apply Ref.eq_refl|apply AccessRight.eq_refl]].
  eapply Seq.transfer_read;
    [eapply Hin
      |solve_edge_insert Htr' Heq
      |eapply AGProps.Add_add; eauto].
  (* write *)
  eapply Hmax'; [ eapply Seq.potTransfer_trans; [eapply Seq.potTransfer_base; apply AG.eq_refl|] 
    | eapply AGProps.Add_add; left; eapply Edges.edge_equal; solve[apply Ref.eq_refl|apply AccessRight.eq_refl]].
  eapply Seq.transfer_write with (src:=a) (tgt:=src) (tgt':=n);
    [|solve_edge_insert Htr' Heq |eapply AGProps.Add_add; eauto].
  (* we place (a src wr) in p' by transfer_write *)
  eapply Hmax'; [ eapply Seq.potTransfer_trans; [eapply Seq.potTransfer_base; apply AG.eq_refl|] 
    | eapply AGProps.Add_add; left; eapply Edges.edge_equal; solve[apply Ref.eq_refl|apply AccessRight.eq_refl]].
  eapply Seq.transfer_write with (src:=src) (tgt:= a) (tgt':= src);
    [eapply Hin
    | 
    | eapply AGProps.Add_add; eauto].
  (* we place (src src wr) in p' by transfer_src_self *)
  eapply Hmax'; [ eapply Seq.potTransfer_trans; [eapply Seq.potTransfer_base; apply AG.eq_refl|] 
    | eapply AGProps.Add_add; left; eapply Edges.edge_equal; solve[apply Ref.eq_refl|apply AccessRight.eq_refl]].
  eapply Seq.transfer_self_src with (src:=src) (tgt:=a);
    [apply Hin | eapply AGProps.Add_add;eauto].
  (* send *)
  eapply Hmax'; [ eapply Seq.potTransfer_trans; [eapply Seq.potTransfer_base; apply AG.eq_refl|] 
    | eapply AGProps.Add_add; left; eapply Edges.edge_equal; solve[apply Ref.eq_refl|apply AccessRight.eq_refl]].
  eapply Seq.transfer_write with (src:=a) (tgt:=src) (tgt':=n);
    [| solve_edge_insert Htr' Heq  |eapply AGProps.Add_add; eauto].
  (* we place (a src wr) in p' by transfer_send *)
  eapply Hmax'; [ eapply Seq.potTransfer_trans; [eapply Seq.potTransfer_base; apply AG.eq_refl|] 
    | eapply AGProps.Add_add; left; eapply Edges.edge_equal; solve[apply Ref.eq_refl|apply AccessRight.eq_refl]].
  eapply Seq.transfer_send with (src:=src) (tgt:= a) (tgt':= src);
    [eapply Hin
    |
    | eapply AGProps.Add_add; eauto].
  (* we place (src src wr) in p' by trans_src_self *)
  eapply Hmax'; [ eapply Seq.potTransfer_trans; [eapply Seq.potTransfer_base; apply AG.eq_refl|] 
    | eapply AGProps.Add_add; left; eapply Edges.edge_equal; solve[apply Ref.eq_refl|apply AccessRight.eq_refl]].
  eapply Seq.transfer_self_src with (src:=src) (tgt:=a);
    [apply Hin | eapply AGProps.Add_add;eauto].

  destruct Hin as [[Hin HeqSrcN]| Hin].
  rewrite HeqSrcN in *.
  eapply Hsubset in Hin.
  eapply Hmax'; [ eapply Seq.potTransfer_trans; [eapply Seq.potTransfer_base; apply AG.eq_refl|] 
    | eapply AGProps.Add_add; left; eapply Edges.edge_equal; solve[apply Ref.eq_refl|apply AccessRight.eq_refl]].
  eapply Seq.transfer_write with (src:=a) (tgt:=n);
    [| apply Hin | eapply AGProps.Add_add;eauto].
  solve_edge_insert Htr' Heq.

  do 2 (destruct Hin as [[Heq1 Heq2]| Hin]; [rewrite Heq1 in *; rewrite Heq2 in *; solve_edge_insert Htr' Heq|]).

  destruct Hin as [[Heq1 Heq2]| [Heq1 Heq2]];
    (rewrite Heq1 in *; rewrite Heq2 in *;
      eapply Hmax'; [ eapply Seq.potTransfer_trans; [eapply Seq.potTransfer_base; apply AG.eq_refl|] 
        | eapply AGProps.Add_add; left; eapply Edges.edge_equal; solve[apply Ref.eq_refl|apply AccessRight.eq_refl]];
      eapply Seq.transfer_self_src with (rgt:=rgt);
        [| eapply AGProps.Add_add;eauto];
        solve_edge_insert Htr' Heq).
  
Qed.


Theorem endow_spec : forall a n ag p ag' p' N, 
  Seq.potAcc ag p -> Seq.ag_objs_spec p N -> ~ RefSet.In n N -> 
  AG.Equal (insert a n p) ag' -> Seq.potAcc ag' p' -> 
  forall src tgt rgt, 
    ((AG.In (Edges.mkEdge src tgt rgt) p \/ 
     AG.In (Edges.mkEdge src a rgt) p /\ Ref.eq tgt n \/ 
     AG.In (Edges.mkEdge a tgt rgt) p /\ Ref.eq src n \/
     Ref.eq src n /\ Ref.eq tgt a \/
     Ref.eq src a /\ Ref.eq tgt n \/
     Ref.eq src n /\ Ref.eq tgt n \/
     Ref.eq src a /\ Ref.eq tgt a) <->
   AG.In (Edges.mkEdge src tgt rgt) p').
Proof.
  (* while not pretty, being exact is far faster than asking eauto *)
  intros; split; intros; 
    [eapply endow_spec_2;
      [apply H
        | apply H0
        | apply H1
        | apply H2
        | apply H3
        | apply H4]
      | eapply endow_spec_1;
        [apply H
          | apply H0
          | apply H1
          | apply H2
          | apply H3
          | apply H4]].  
Qed.



Theorem AG_project_endow : forall ag p, Seq.potAcc ag p -> forall N, Seq.ag_objs_spec p N ->
  forall n, ~ RefSet.In n N -> forall a ag', AG.Equal (insert a n p) ag' -> forall p', Seq.potAcc ag' p' -> 
    AG_project a n p p'.
Proof.
  unfold AG_project; intros.
  eapply iff_sym; eapply endow_spec; eauto.
Qed.

Hint Resolve AG_project_endow.

(* This is no longer true.  However, it's only used for AG_lineage judgements, which are largely ignored *)

(* Theorem AG_project_subset: forall a o p p', AG_project a o p p' -> *)
(*   forall p'', AG.Subset p'' p' -> AG_project a o p p''. *)
(* Proof. *)
(*   unfold AG_project; intros; intuition eauto.  *)
(* Qed. *)

(* The AG_lineage property has a second set of objs its reasoning over.
   N is the set of objs that are considered alive.
   p is the set of edges we project from.
   N is the set of objs we project to.
   p'' is the set of objs we have currently projected to *)

Inductive AG_lineage N p N'' p'' : Prop :=
| AG_lineage_base : forall objs, Seq.ag_objs_spec p objs -> 
  RefSet.Subset objs N ->
  RefSet.eq N N'' ->
  AG.eq p'' p -> 
  AG_lineage N p N'' p''
| AG_lineage_step : forall N' p', AG_lineage N p N' p' -> 
  forall a, RefSet.In a N' -> 
  forall o, ~ RefSet.In o N' -> 
  AG_project a o p' p'' ->
  RefSetProps.Add o N' N'' -> 
  AG_lineage N p N'' p''.


  (* Theorem AG_lineage_subset: forall N N' p p', AG_lineage N p N' p' -> *)
  (*   forall p'2, AG.Subset p'2 p' -> AG_lineage N p N' p'2. *)
  (* Proof. *)
  (*   intros N N' p p' Hred p'2 Hsub. *)
  (*   induction Hred. *)
  (*   (* base *) *)
  (*   eapply AG_lineage_base; [ apply H | apply H0 | apply H1 | eapply AGProps.subset_trans; eauto]. *)
  (*   (* step *) *)
  (*   eapply AG_lineage_step; *)
  (*     [apply Hred *)
  (*       | apply H *)
  (*       | apply H0 *)
  (*       | eapply AG_project_subset; [apply H1 | auto] *)
  (*       | apply H2]. *)
  (* Qed. *)

  Theorem Proper_ag_objs_spec: Proper (AG.eq ==> RefSet.eq ==> iff) Seq.ag_objs_spec.
  Proof.
    unfold Proper; unfold respectful; unfold iff; intros;split;intros;
      unfold Seq.ag_objs_spec in *;
        (intro e; generalize (H1 e); clear H1; intros H1;
          eapply iff_trans; [eapply RefSet.eq_sym in H0; solve [eapply H0|eapply RefSet.eq_sym in H0; eapply H0] |
            eapply iff_trans; [eapply H1 |
              split; intros [obj [rgt [Ho | Ho]]];
                do 2 eapply ex_intro; intuition (apply H; apply Ho)]]).
  Qed.

    Theorem AG_lineage_impl: 
      forall N N', RefSet.eq N N' ->
      forall M M', RefSet.eq M M' ->
      forall p p', AG.eq p p' ->
      forall s s', AG.eq s s' ->
        AG_lineage N p M s -> AG_lineage N' p' M' s'.
    Proof.
      intros.
      revert H H0 H1 H2.
      revert N' M' p' s'.
      induction H3; intros N2 M2 p2 s2 HeqN HeqM HeqP HeqS.
      (* base *)
      econstructor 1.
      eapply Proper_ag_objs_spec;
        [eapply AG.eq_sym; apply HeqP
        |eapply RefSet.eq_refl
        |eapply H].
      rewrite <- HeqN; auto.
      rewrite <- HeqN; rewrite <- HeqM; auto.
      rewrite <- HeqS; rewrite <- HeqP; auto.

      (* step *)
      econstructor 2.
      eapply IHAG_lineage;
        [auto
          | apply RefSet.eq_refl
          | auto
          | apply AG.eq_refl].
      apply H.
      apply H0.
      eapply Proper_AG_project;
        [apply Ref.eq_refl
          | apply Ref.eq_refl
          | apply AG.eq_refl
          | apply AG.eq_sym; apply HeqS
          | apply H1].
      intros o'; eapply iff_trans; [apply iff_sym; eapply HeqM|  eapply H2].
    Qed.

  Theorem Proper_AG_lineage: Proper (RefSet.eq ==> AG.eq ==> RefSet.eq ==> AG.eq ==> iff) AG_lineage.
  Proof.
    unfold Proper; unfold respectful; unfold iff; intros; split; intros.
    eapply AG_lineage_impl; eauto.
    eapply AG.eq_sym in H2; eapply AG.eq_sym in H0;
      eapply RefSet.eq_sym in H1; eapply RefSet.eq_sym in H.
    eapply AG_lineage_impl; eauto.
  Qed.


Theorem AG_lineage_trans: forall N N' p p', AG_lineage N p N' p' -> 
  forall N'' p'', AG_lineage N' p' N'' p'' -> 
    AG_lineage N p N'' p''.
Proof.
  intros N N' p p' Hred1 N'' p'' Hred2.
  induction Hred2.
  (* base *)

  (* This proof relies on the notion that AG_attenuating_auth_via has the same property as AG_project_subset
     and that it is respectful of equivalence. *)

  eapply Proper_AG_lineage;
    [apply RefSet.eq_refl
      | apply AG.eq_refl
      | apply RefSet.eq_sym; apply H1
      | apply H2
      |apply Hred1
    ].

  (* step *)
  econstructor 2;
    [apply IHHred2
      | apply H
      | apply H0
      | apply H1
      | apply H2].
 Qed.

(* identical to AG_attenuating_insert with the additional constraints:
   In a objs 
      This condition should propigate up until endow_dep, where it can be satisfied by allocate_preReq_dec
   (ag_objs p) [<=] objs 
      This condition should propigate up to potAcc_op, where it will be satisfied by objs_not_unborn objs s

   Having proved this, we believe it extends to potAcc_execute 
*)

(*
    Seq.potAcc ag p -> 
    Seq.ag_objs_spec p N ->
    ~ RefSet.In n N ->
    ~ RefSet.In n objs ->
    AG.Equal (insert a n p) ag' ->
    Seq.potAcc ag' p' ->
    AG_attenuating objs p p'.
*)

  Theorem AG_lineage_insert:
    forall ag p, Seq.potAcc ag p -> 
    forall objs, Seq.ag_objs_spec p objs ->
    forall N, RefSet.Subset objs N ->
    forall n, ~ RefSet.In n N ->
    forall a, RefSet.In a N ->
    forall ag', AG.Equal (insert a n p) ag' ->
    forall p', Seq.potAcc ag' p' ->
    forall N', RefSetProps.Add n N N' ->
      AG_lineage N p N' p'.
  Proof.
    intros ag p Hpa objs Hobjs N HN n Hn a Ha ag' Hag' p' Hpa' N' Hadd.

    econstructor 2;
    solve [ econstructor 1; solve [ eauto | apply RefSet.eq_refl | apply AG.eq_refl] | eauto].
  Qed.

  (* TODO: move to Sequential Access *)
  Theorem weak_self_loop: 
    forall p, Seq.maxTransfer p ->
      forall n, Seq.ag_objs_spec p n ->
        forall x, RefSet.In x n ->
          AG.In (Edges.mkEdge x x wk) p.
  Proof.
    intros.
    eapply potAcc_self_loop;
      solve [ constructor; [eapply Seq.potTransfer_base; auto| eapply Seq.maxTransfer_maxPotTransfer; auto]
        |eauto].
  Qed.

  Implicit Arguments weak_self_loop [p n x].


  Theorem mutable_subset_objs: 
    forall A N, Seq.ag_objs_spec A N ->
    forall N', RefSet.Subset N N' ->
    forall E, RefSet.Subset E N' ->
    forall M, mutable_spec A E M -> RefSet.Subset M N'.
  Proof.
    intros; intros m Hin.
    eapply H2 in Hin; clear H2.
    case (RefSetProps.In_dec m E); intros Hin';
    (destruct Hin as [Hin|Hexists]; try contradiction; try solve[eauto]).
    eapply H0; destruct Hexists as [e [Hin [Hedge | [Hedge | [Hedge | Hedge]]]]];
    eapply H; do 2 eapply ex_intro; intuition (eapply Hedge).
  Qed.
  Implicit Arguments mutable_subset_objs [A N N' E M].


(* The intention of this theorem is to accurately capture mutable through a projection in a single step *)
Theorem mutable_project_not_in:
forall p, Seq.maxTransfer p ->
forall objs, Seq.ag_objs_spec p objs ->
forall N, RefSet.Subset objs N ->
forall E, RefSet.Subset E N ->
forall a, RefSet.In a N ->
forall o, ~ RefSet.In o N -> 
forall p', AG_project a o p p' ->
forall m, mutable_spec p E m -> ~ RefSet.In a m ->
forall m', mutable_spec p' m m' ->
RefSet.Subset m' m.
Proof.
  intros p Hmax objs Hobjs N HN E HE a Hnina o Hnino p' Hproj m Hm Hinam m' Hm'.
  unfold mutable_spec in *; unfold AG_project in *.
  intros x Hinx.

  eapply Hm' in Hinx; clear Hm'; clear m'.

  (* In x m *)
  case (RefSetProps.In_dec x m); intros HinXM; 
    (destruct Hinx as [HinM | [e [HinM Hedges]]]); try contradiction; auto.
  (* In e m *)
  apply Hm. 
  (* at this point, we know that ~ In a m, which means
     ~ In a E /\
     ~ exists e, ... *)
  (* more importantly, we can infer that ~ a [=] e *)
  assert (~ Ref.eq e a) as HneqAE;
    [let H := fresh "H" in intro; rewrite <- H in Hinam; contradiction|].

  assert (~ Ref.eq e o) as HneqEO;
    [let Hnot := fresh "Hnot" in intros Hnot; rewrite Hnot in HinM;
      eapply mutable_subset_objs in HinM; eauto; try contradiction|].

  (* Here is where the problem explodes into case analysis.  Because we need to perform very similar case
     analysis twice, we will need to geenralize the search.*)
  (* we are currently exploring the space *)

  
  (* same reasoning as in mutable_project_in, with a few differences:
     The in p case must exist by transitivity in p.
     e[=]o cases can't exist by In e m.
     e[=]a cases can't exist, see above
     The only remaining case is:

     AG.In (Edges.mkEdge e a tx) p /\ Ref.eq x o
     However, a is not mutable in p, so this edge should not exist.
 *)  
  destruct Hedges as [Hedge | [Hedge | [Hedge | Hedge]]]; eapply Hproj in Hedge; clear Hproj;
    (case (RefSetProps.In_dec x E); intros HninE; [left; auto| right];

  (destruct Hedge as [Hedge | [[Hedge Heq] | [[Hedge Heq] | [[Heq Heq'] | [[Heq Heq'] | [[Heq Heq'] | [Heq Heq']]]]]]]; try contradiction));  eapply Hm in HinM.

  (* In (e x tx) p, transitive case *)
  
  (* eliminate the subset cases *)
  case (RefSetProps.In_dec e E); intros HinE; destruct HinM as [HinM|HinM]; 
    try solve 
      [ intuition eauto
        | contradiction
      ].

  destruct HinM as [e' [HinE' Hedges]]. eapply ex_intro; split ;[ apply HinE'|].
  destruct Hedges as [Hedge' | [Hedge' | [Hedge' | Hedge']]].
  (* send case *)

  left.
  assert (AG.In (Edges.mkEdge e e' tx) p) as Hedge2;
    [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
      eapply Seq.transfer_send_reply; [|eapply AGProps.Add_add]; eauto
        |].
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.

  (* write case *)
  do 2 right ;left.
  
  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.

  (* weak case *)

  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.  

  (* read case *)
  
  do 3 right.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.  

  (* In (e a send) p /\ x [=] o, should not occur *)
  assert (RefSet.In a m); [|contradiction].
  eapply Hm.
  case (RefSetProps.In_dec e E); intros HinE; destruct HinM as [HinM | [e' [HinE' Hedges]]]; 
    try solve [contradiction | intuition eauto].
  right; eapply ex_intro; split; [eapply HinE' |].

  destruct Hedges as [Hedge' | [Hedge' | [Hedge' | Hedge']]].
  (* at this point, the tactics below are identical to the tactics above *)

  (* send case *)

  left.
  assert (AG.In (Edges.mkEdge e e' tx) p) as Hedge2;
    [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
      eapply Seq.transfer_send_reply; [|eapply AGProps.Add_add]; eauto
        |].
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.

  (* write case *)
  do 2 right ;left.
  
  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.

  (* weak case *)

  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.  

  (* read case *)
  
  do 3 right.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.  


  (* In (e x wr) p, transitive case *)
  
  (* this tactic set differs from (e x tx) in two regards:
     1. select on write authority at all times, not send
     2. apply transfer_write instead of transfer_send.
     *)

  (* eliminate the subset cases *)
  case (RefSetProps.In_dec e E); intros HinE; destruct HinM as [HinM|HinM]; 
    try solve 
      [ intuition eauto
        | contradiction
      ].

  destruct HinM as [e' [HinE' Hedges]]. eapply ex_intro; split ;[ apply HinE'|].
  destruct Hedges as [Hedge' | [Hedge' | [Hedge' | Hedge']]].
  (* send case *)

  right; left.
  assert (AG.In (Edges.mkEdge e e' tx) p) as Hedge2;
    [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
      eapply Seq.transfer_send_reply; [|eapply AGProps.Add_add]; eauto
        |].
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.

  (* write case *)
  do 2 right ;left.
  
  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [ | | eapply AGProps.Add_add]; eauto.

  (* weak case *)

  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [ | | eapply AGProps.Add_add]; eauto.  

  (* read case *)
  
  do 3 right.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [ | | eapply AGProps.Add_add]; eauto.  

  (* In (e a wr) p /\ x [=] o, should not occur *)
  assert (RefSet.In a m); [|contradiction].
  eapply Hm.
  case (RefSetProps.In_dec e E); intros HinE; destruct HinM as [HinM | [e' [HinE' Hedges]]]; 
    try solve [contradiction | intuition eauto].
  right; eapply ex_intro; split; [eapply HinE' |].

  destruct Hedges as [Hedge' | [Hedge' | [Hedge' | Hedge']]].
  (* again, at this point, the tactics below are identical to the tactics above *)

  (* send case *)

  right; left.
  assert (AG.In (Edges.mkEdge e e' tx) p) as Hedge2;
    [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
      eapply Seq.transfer_send_reply; [|eapply AGProps.Add_add]; eauto
        |].
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.

  (* write case *)
  do 2 right ;left.
  
  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [ | | eapply AGProps.Add_add]; eauto.

  (* weak case *)

  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [ | | eapply AGProps.Add_add]; eauto.  

  (* read case *)
  
  do 3 right.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [ | | eapply AGProps.Add_add]; eauto.  

  (* In (x e wk) p, transitive case *)


  (* eliminate the subset cases *)
  case (RefSetProps.In_dec e E); intros HinE; destruct HinM as [HinM|HinM]; 
    try solve 
      [ intuition eauto 7
        | contradiction
      ].

  destruct HinM as [e' [HinE' Hedges]]. eapply ex_intro; split ;[ apply HinE'|].
  destruct Hedges as [Hedge' | [Hedge' | [Hedge' | Hedge']]].
  (* send case *)

  do 2 right; left.

  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_weak; [ | | | eapply AGProps.Add_add]; eauto.

  (* write case *)
  do 2 right ;left.
  
  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_weak; [ | | | eapply AGProps.Add_add]; eauto.

  (* weak case *)

  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_weak; [ | | | eapply AGProps.Add_add]; eauto.  

  (* read case *)
  
  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_weak; [| | | eapply AGProps.Add_add]; intuition eauto 1.
  (* here the tactic becomes more specific:
     eauto is shallow, and we need intuition to determine cases of weak. *)


  (* In (e a wk) p /\ x [=] o, should not occur *)
  assert (RefSet.In a m); [|contradiction].
  eapply Hm.
  case (RefSetProps.In_dec e E); intros HinE; destruct HinM as [HinM | [e' [HinE' Hedges]]]; 
    try solve [contradiction | intuition eauto 7].
  right; eapply ex_intro; split; [eapply HinE' |].

  destruct Hedges as [Hedge' | [Hedge' | [Hedge' | Hedge']]].
  (* again, at this point, the tactics below are identical to the tactics above *)

  (* send case *)

  do 2 right; left.

  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_weak; [ | | | eapply AGProps.Add_add]; eauto.

  (* write case *)
  do 2 right ;left.
  
  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_weak; [ | | | eapply AGProps.Add_add]; eauto.

  (* weak case *)

  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_weak; [ | | | eapply AGProps.Add_add]; eauto.  

  (* read case *)
  
  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_weak; [| | | eapply AGProps.Add_add]; intuition eauto 1.

  (* In (x e rd) p, transitive case *)


  (* eliminate the subset cases *)
  case (RefSetProps.In_dec e E); intros HinE; destruct HinM as [HinM|HinM]; 
    try solve 
      [ intuition eauto 7
        | contradiction
      ].

  destruct HinM as [e' [HinE' Hedges]]. eapply ex_intro; split ;[ apply HinE'|].
  destruct Hedges as [Hedge' | [Hedge' | [Hedge' | Hedge']]].
  (* send case *)

  do 2 right; left.

  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_read; [ | | eapply AGProps.Add_add]; eauto.

  (* write case *)
  do 2 right ;left.
  
  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_read; [ | | eapply AGProps.Add_add]; eauto.

  (* weak case *)

  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_read; [ | | eapply AGProps.Add_add]; eauto.  

  (* read case *)
  
  do 3 right.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_read; [| | eapply AGProps.Add_add]; intuition eauto 1.

  (* In (e a rd) p /\ x [=] o, should not occur *)
  assert (RefSet.In a m); [|contradiction].
  eapply Hm.
  case (RefSetProps.In_dec e E); intros HinE; destruct HinM as [HinM | [e' [HinE' Hedges]]]; 
    try solve [contradiction | intuition eauto 7].
  right; eapply ex_intro; split; [eapply HinE' |].

  destruct Hedges as [Hedge' | [Hedge' | [Hedge' | Hedge']]].
  (* again, at this point, the tactics below are identical to the tactics above *)
  (* send case *)

  do 2 right; left.

  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_read; [ | | eapply AGProps.Add_add]; eauto.

  (* write case *)
  do 2 right ;left.
  
  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_read; [ | | eapply AGProps.Add_add]; eauto.

  (* weak case *)

  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_read; [ | | eapply AGProps.Add_add]; eauto.  

  (* read case *)
  
  do 3 right.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_read; [| | eapply AGProps.Add_add]; intuition eauto 1.

Qed.

Implicit Arguments mutable_project_not_in [p objs N E a o p' m m'].



  Theorem mutable_nondec: forall p e m, mutable_spec p e m -> RefSet.Subset e m.
  Proof.
    intros p e m Hmut x Hin; eapply Hmut; intuition auto.
  Qed.
  Hint Resolve mutable_nondec.



Theorem mutable_project_not_in_eq:
forall p, Seq.maxTransfer p ->
forall objs, Seq.ag_objs_spec p objs ->
forall N, RefSet.Subset objs N ->
forall E, RefSet.Subset E N ->
forall a, RefSet.In a N ->
forall o, ~ RefSet.In o N -> 
forall p', AG_project a o p p' ->
forall m, mutable_spec p E m -> ~ RefSet.In a m ->
forall m', mutable_spec p' m m' ->
RefSet.eq m' m.
Proof.
  intros p Hmax objs Hobjs N HN E HE a Hnina o Hnino p' Hproj m Hm Hinam m' Hm'.
  intros x; split;[eapply mutable_project_not_in; eauto | eapply mutable_nondec; eauto].
Qed.

Implicit Arguments mutable_project_not_in_eq [p objs N E a o p' m m'].

Theorem mutable_maximal:
forall p, Seq.maxTransfer p ->
forall E m, mutable_spec p E m ->
forall m', mutable_spec p m m' ->
RefSet.Subset m' m.
Proof.
  intros p Hmax E m Hm m' Hm' e Hin.
  eapply Hm' in Hin.
  case (RefSetProps.In_dec e m); intros HnotEltM;
    (destruct Hin as [Hin|[e' [Helt'M Helt'Edge]]]);
    try solve[contradiction|auto].

  (* everything else must be a contradiciton, though we might not prove it that way *)
  eapply Hm in Helt'M.
  destruct Helt'M as [Hin|[e'2 [Helt'E Helt'Edge2]]].

  (* In e' E : direct*)
  eapply Hm.
  right. eapply ex_intro. intuition eauto 2.

  (* ~ In e'2 E : transitive*)
  eapply Hm.
  right. eapply ex_intro with e'2.
  split; auto.

  (* we really need an automated transfer_step tactic, these are going to end up being the same strategy
     as the previous two theorems *)

  destruct Helt'Edge2 as [Hedge | [Hedge | [ Hedge | Hedge]]];
    (destruct Helt'Edge as [Hedge' | [Hedge' | [ Hedge' | Hedge']]]).

  (* send send *)

  (* The goal of this edge is to prove the membership of an edge in a maximal accessgraph
     using Seq.transfer and a single intermediate.  If you need more than one intermediate object,
     you will not be able to use this tactic.  Goals and hypotheses must be of the form:
     AG.In (Edges.mkEdge x y r) p with hypothesis:
     Hmax : Seq.maxTransfer p 
     Invocation is inteneded to be called within intuition.*)

  Ltac use_maxTransfer_add Hmax := eapply Hmax; [| eapply AGFacts.add_iff; left; auto].

  Ltac solve_weak_self Hmax Hedge :=
    solve [eapply weak_self_loop; 
      [eapply Hmax
        | eapply Seq.ag_objs_spec_ag_objs
        | eapply Seq.ag_objs_spec_ag_objs; do 2 eapply ex_intro; intuition (apply Hedge)]].
  
  Ltac transfer_solve n :=
    match n with
      O => fail
      | S ?n' =>
        match goal with
  (* the base case, always apply an edge you have in context *)
          [ Hmax: Seq.maxTransfer ?p , Hedge: AG.In (Edges.mkEdge ?x ?y ?r) ?p |- AG.In (Edges.mkEdge ?x ?y ?r) ?p ] => 
          solve [apply Hedge]
  (* send_reply, immediately invert *)
          | [ Hmax : Seq.maxTransfer ?p , Hedge : AG.In (Edges.mkEdge ?x ?y tx) ?p |- AG.In (Edges.mkEdge ?y ?x tx) ?p ] =>
            solve 
            [
              use_maxTransfer_add Hmax;
              eapply Seq.transfer_send_reply; [ eapply Hedge | eapply AGProps.Add_add]
            ]
  (* weak self loop src, immediate*)
          | [ Hmax: Seq.maxTransfer ?p , Hedge: AG.In (Edges.mkEdge ?x ?y ?r) ?p |- AG.In (Edges.mkEdge ?x ?x wk) ?p ] =>
            solve_weak_self Hmax Hedge
  (* weak self loop tgt, immediate*)
          | [ Hmax: Seq.maxTransfer ?p , Hedge: AG.In (Edges.mkEdge ?y ?x ?r) ?p |- AG.In (Edges.mkEdge ?x ?x wk) ?p ] =>
            solve_weak_self Hmax Hedge
            
  (* explore via transfer_send *)
          | [ Hmax: Seq.maxTransfer ?p |- AG.In (Edges.mkEdge ?x ?y ?r) ?p ] => 
            solve 
            [
              use_maxTransfer_add Hmax; 
              eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; transfer_solve n'
            ]

        end
    end.

  Unset Ltac Debug.

  left.

  Ltac use_transfer_send := eapply Seq.transfer_send; [| | eapply AGProps.Add_add].
  Ltac use_transfer_send_reply := eapply Seq.transfer_send_reply; [| eapply AGProps.Add_add].
  Ltac use_transfer_write := eapply Seq.transfer_write; [ | | eapply AGProps.Add_add].
  Ltac use_transfer_weak := eapply Seq.transfer_weak; [ | | | eapply AGProps.Add_add].
  Ltac use_transfer_read := eapply Seq.transfer_read; [ | | eapply AGProps.Add_add].
  
  (* send - send case *)
  use_maxTransfer_add Hmax; use_transfer_send.
  use_maxTransfer_add Hmax; use_transfer_send_reply.
  apply Hedge.
  apply Hedge'.
  

  (* send -write case *)
  do 2 right ;left.

  use_maxTransfer_add Hmax; use_transfer_write.
  use_maxTransfer_add Hmax; use_transfer_send.
  use_maxTransfer_add Hmax; use_transfer_send_reply.
  eapply Hedge.
  eapply Hedge'.
  solve_weak_self Hmax Hedge.


  (* send - weak case *)

  do 2 right; left.
  use_maxTransfer_add Hmax; use_transfer_weak.
  apply Hedge'.
  
  use_maxTransfer_add Hmax; use_transfer_send.
  apply Hedge.  
  solve_weak_self Hmax Hedge.
  intuition trivial.

  (* send - read case *)
  
  do 2 right; left.
  use_maxTransfer_add Hmax; use_transfer_read.
  apply Hedge'.
  
  use_maxTransfer_add Hmax; use_transfer_send.
  apply Hedge.  
  solve_weak_self Hmax Hedge.

  (* write - send case *)
  
  do 2 right; left.
  use_maxTransfer_add Hmax; use_transfer_send.
  apply Hedge'.
  
  use_maxTransfer_add Hmax; use_transfer_write.
  apply Hedge.
  solve_weak_self Hmax Hedge.

  (* write - write case *)
  do 2 right; left.
  use_maxTransfer_add Hmax; use_transfer_write.
  apply Hedge'.
  
  use_maxTransfer_add Hmax; use_transfer_write.
  apply Hedge.
  solve_weak_self Hmax Hedge.
  
  (* write - weak case *)
  do 2 right; left.
  use_maxTransfer_add Hmax; use_transfer_weak.
  apply Hedge'.
  
  use_maxTransfer_add Hmax; use_transfer_write.
  apply Hedge.
  solve_weak_self Hmax Hedge.  
  intuition trivial.

  (* write - read case *)
  do 2 right; left.
  use_maxTransfer_add Hmax; use_transfer_read.
  apply Hedge'.
  
  use_maxTransfer_add Hmax; use_transfer_write.
  apply Hedge.
  solve_weak_self Hmax Hedge.  

  (* weak - send case *)
  do 2 right; left.
  use_maxTransfer_add Hmax; use_transfer_send.
  apply Hedge'.
  
  use_maxTransfer_add Hmax; use_transfer_weak.
  apply Hedge.
  solve_weak_self Hmax Hedge. 
  intuition trivial.

  (* weak - write case *)
  do 2 right; left.
  use_maxTransfer_add Hmax; use_transfer_write.
  apply Hedge'.
  
  use_maxTransfer_add Hmax; use_transfer_weak.
  apply Hedge.
  solve_weak_self Hmax Hedge. 
  intuition trivial.

  (* weak - weak case *)
  do 2 right; left.
  use_maxTransfer_add Hmax; use_transfer_weak.
  apply Hedge'.
  
  use_maxTransfer_add Hmax; use_transfer_weak.
  apply Hedge.
  solve_weak_self Hmax Hedge. 
  intuition trivial.
  intuition trivial.

  (* weak - read case *)
  do 2 right; left.
  use_maxTransfer_add Hmax; use_transfer_read.
  apply Hedge'.
  
  use_maxTransfer_add Hmax; use_transfer_weak.
  apply Hedge.
  solve_weak_self Hmax Hedge. 
  intuition trivial.

  (* read - send case *)
  do 2 right; left.
  use_maxTransfer_add Hmax; use_transfer_send.
  apply Hedge'.
  
  use_maxTransfer_add Hmax; use_transfer_read.
  apply Hedge.
  solve_weak_self Hmax Hedge. 

  (* read - write case *)
  do 2 right; left.
  use_maxTransfer_add Hmax; use_transfer_write.
  apply Hedge'.
  
  use_maxTransfer_add Hmax; use_transfer_read.
  apply Hedge.
  solve_weak_self Hmax Hedge. 

  (* read - weak case *)
  do 2 right; left.
  use_maxTransfer_add Hmax; use_transfer_weak.
  apply Hedge'.
  
  use_maxTransfer_add Hmax; use_transfer_read.
  apply Hedge.
  solve_weak_self Hmax Hedge. 
  intuition trivial.

  (* read - read case *)
  do 3 right.
  use_maxTransfer_add Hmax; use_transfer_read.
  apply Hedge'.
  apply Hedge.

Qed.

Theorem mutable_maximal_subset:
forall p, Seq.maxTransfer p ->
forall E m, mutable_spec p E m ->
forall p', AG.Subset p' p ->
forall m', mutable_spec p' m m' ->
RefSet.Subset m' m.
Proof.
  intros p Hmax E m Hm p' Hsub m' Hm'.
  generalize (mutable_maximal _ Hmax _ _ Hm _ (mutable_spec_mutable _ _ )).
  generalize (mutable_spec_mutable p m).
  generalize (mutable p m); intros m2 Hm2 Hsub2.

  eapply mutable_spec_subset in Hm'; [ | apply RefSetProps.subset_refl| apply Hsub| apply Hm2].
  eapply RefSetProps.subset_trans; eauto.
Qed.

Theorem AG_project_eq :
  forall a a', Ref.eq a a' ->
  forall n n', Ref.eq n n' ->
  forall p p', AG.eq p p' ->
  forall p2, AG_project a n p p2 ->
  forall p2', AG_project a' n' p' p2' ->
  AG.eq p2 p2'.
Proof.
  intros a a' HeqA n n' HeqN p p' HeqP p2 Hproj p2' Hproj'.
  eapply Proper_AG_project in Hproj';
    [ clear a' HeqA n' HeqN p' HeqP
      | apply HeqA
      | apply HeqN
      | apply HeqP
      | apply AG.eq_refl
    ].
  intros edge; generalize (Edges.edge_rewrite edge); intros HeqEdge; rewrite <- HeqEdge; revert HeqEdge.
  generalize (Edges.source edge) (Edges.target edge) (Edges.right edge); intros src tgt rgt HeqEdge.
  eapply iff_trans; [eapply Hproj| apply iff_sym; apply Hproj'].
Qed.

   Theorem Proper_potAcc : Proper (AG.eq ==> AG.eq ==> iff) Seq.potAcc.
   Proof.
     unfold Proper; unfold respectful; intros.
     split; intros; eapply potAcc_eq_iff;  eauto; try ( apply AG.eq_sym; auto).
   Qed.


(* We need to know that AG_project is maximal, we can use the definition of endow to give us this as it's 
   now in a iff relationship. Additionally, this may make the mutable_subset predicates easier to prove *)

Theorem AG_project_maximal:
forall p, Seq.maxTransfer p ->
forall objs, Seq.ag_objs_spec p objs ->
forall N, RefSet.Subset objs N ->
forall o, ~ RefSet.In o N -> 
forall a p', AG_project a o p p' ->
Seq.maxTransfer p'.
Proof.
  intros p Hmax objs Hobjs N Hn o HinO a p' Hproj.
  generalize (Seq.exists_potAcc (insert a o p)); intros [p'2 Hp'2].

  eapply AG_project_eq in Hproj;
    [ eapply Proper_potAcc in Hp'2;
      [ destruct Hp'2 as [Htrans' Hmax']; apply Seq.maxTransfer_maxPotTransfer; apply Hmax'
        | apply AG.eq_refl
        | apply AG.eq_sym; apply Hproj
      ]
      | apply Ref.eq_refl
      | apply Ref.eq_refl
      | apply AG.eq_refl
      | eapply AG_project_endow ;
        [ apply maxTransfer_potAcc_refl; apply Hmax
          | apply Hobjs
          | rewrite <- Hn in HinO; apply HinO
          | apply AG.eq_refl
          | apply Hp'2
        ]
    ].
Qed.
    
Implicit Arguments AG_project_maximal [p objs N a o p'].

(* The intention of this theorem is to accurately capture mutable through mutable lineage in a single step *)
Theorem mutable_project_in_eq:
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
RefSet.eq m' E'.
Proof.
  intros p Hmax objs Hobjs N HN E HE a Hnina o Hnino p' Hproj m Hm Hinam m' Hm' E' Hadd.
  generalize (mutable_nondec _ _ _ Hm'); intros Hmsub.
  generalize (AG_project_maximal Hmax Hobjs HN Hnino Hproj); intros Hmax'.
  unfold mutable_spec in *; unfold AG_project in *.
  intros x.

  (* next two lines differ from above theorem *)
  rewrite (Hadd x); clear Hadd; clear E'.
  (* case on o [=] x *)
  case (Ref.eq_dec x o); intros HneqO. split; intros H; [auto|].
  destruct H as [_|Hin]; [| eapply Hmsub;auto].
  (* case on In x m *)
  case (RefSetProps.In_dec x m); intros HinXM; [ eapply Hmsub; eauto|].
  
  eapply Hm'. right.
  apply ex_intro with a.
  split; [auto|].
  rewrite HneqO in *.
  right; left.
  eapply Hproj.
  intuition.

  (* o [<>] x *)
  split; intros Hinx.
  
  right.





 (* Below here is the previous version *)

  eapply Hm' in Hinx; clear Hm'.

  (* In x m case now requires negation *)
  case (RefSetProps.In_dec x m); intros HinXM; 
    (destruct Hinx as [HinM | [e [HinM Hedges]]]); try contradiction; auto.
  (* In e m *)
  apply Hm. 

  (* rather than claiming that e [<>] a, we can claim this for x, and probably unify both proofs *)

  assert (~ Ref.eq x a) as HneqAE;
    [let H := fresh "H" in intro; rewrite H in HinXM; contradiction|].

  assert (~ Ref.eq e o) as HneqEO;
    [let Hnot := fresh "Hnot" in intros Hnot; rewrite Hnot in HinM;
      eapply mutable_subset_objs in HinM; eauto; try contradiction|].
  
  destruct Hedges as [Hedge | [Hedge | [Hedge | Hedge]]]; eapply Hproj in Hedge; clear Hproj;
    (case (RefSetProps.In_dec x E); intros HninE; [left; auto| right];

  (destruct Hedge as [Hedge | [[Hedge Heq] | [[Hedge Heq] | [[Heq Heq'] | [[Heq Heq'] | [[Heq Heq'] | [Heq Heq']]]]]]]; try contradiction));  eapply Hm in HinM.

  (* 4 subgoals remain.  The x[=] o cases have been handled by the add and decidability.
     These are identical to the transitive cases in the previous theorem *)

  (* In (e x tx) p, transitive case *)
  
  (* eliminate the subset cases *)
  case (RefSetProps.In_dec e E); intros HinE; destruct HinM as [HinM|HinM]; 
    try solve 
      [ intuition eauto
        | contradiction
      ].

  destruct HinM as [e' [HinE' Hedges]]. eapply ex_intro; split ;[ apply HinE'|].
  destruct Hedges as [Hedge' | [Hedge' | [Hedge' | Hedge']]].
  (* send case *)

  left.
  assert (AG.In (Edges.mkEdge e e' tx) p) as Hedge2;
    [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
      eapply Seq.transfer_send_reply; [|eapply AGProps.Add_add]; eauto
        |].
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.

  (* write case *)
  do 2 right ;left.
  
  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.

  (* weak case *)

  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.  

  (* read case *)
  
  do 3 right.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.  


  (* In (e x wr) p, transitive case *)
  
  (* this tactic set differs from (e x tx) in two regards:
     1. select on write authority at all times, not send
     2. apply transfer_write instead of transfer_send.
     *)

  (* eliminate the subset cases *)
  case (RefSetProps.In_dec e E); intros HinE; destruct HinM as [HinM|HinM]; 
    try solve 
      [ intuition eauto
        | contradiction
      ].

  destruct HinM as [e' [HinE' Hedges]]. eapply ex_intro; split ;[ apply HinE'|].
  destruct Hedges as [Hedge' | [Hedge' | [Hedge' | Hedge']]].
  (* send case *)

  right; left.
  assert (AG.In (Edges.mkEdge e e' tx) p) as Hedge2;
    [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
      eapply Seq.transfer_send_reply; [|eapply AGProps.Add_add]; eauto
        |].
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [ | | eapply AGProps.Add_add]; eauto.

  (* write case *)
  do 2 right ;left.
  
  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [ | | eapply AGProps.Add_add]; eauto.

  (* weak case *)

  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [ | | eapply AGProps.Add_add]; eauto.  

  (* read case *)
  
  do 3 right.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [ | | eapply AGProps.Add_add]; eauto.  

  (* In (x e wk) p, transitive case *)


  (* eliminate the subset cases *)
  case (RefSetProps.In_dec e E); intros HinE; destruct HinM as [HinM|HinM]; 
    try solve 
      [ intuition eauto 7
        | contradiction
      ].

  destruct HinM as [e' [HinE' Hedges]]. eapply ex_intro; split ;[ apply HinE'|].
  destruct Hedges as [Hedge' | [Hedge' | [Hedge' | Hedge']]].
  (* send case *)

  do 2 right; left.

  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_weak; [ | | | eapply AGProps.Add_add]; eauto.

  (* write case *)
  do 2 right ;left.
  
  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_weak; [ | | | eapply AGProps.Add_add]; eauto.

  (* weak case *)

  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_weak; [ | | | eapply AGProps.Add_add]; eauto.  

  (* read case *)
  
  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_weak; [| | | eapply AGProps.Add_add]; intuition eauto 1.
  (* here the tactic becomes more specific:
     eauto is shallow, and we need intuition to determine cases of weak. *)



  (* In (x e rd) p, transitive case *)

  (* eliminate the subset cases *)
  case (RefSetProps.In_dec e E); intros HinE; destruct HinM as [HinM|HinM]; 
    try solve 
      [ intuition eauto 7
        | contradiction
      ].

  destruct HinM as [e' [HinE' Hedges]]. eapply ex_intro; split ;[ apply HinE'|].
  destruct Hedges as [Hedge' | [Hedge' | [Hedge' | Hedge']]].
  (* send case *)

  do 2 right; left.

  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_send; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_read; [ | | eapply AGProps.Add_add]; eauto.

  (* write case *)
  do 2 right ;left.
  
  assert (RefSet.In e' objs) as HinE'2; [eapply Hobjs; do 2 eapply ex_intro; intuition eauto 1|].
  generalize (weak_self_loop Hmax Hobjs HinE'2); intros HinW.

  assert (AG.In (Edges.mkEdge e e' wk) p) as Hedge2;
  [eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_write; [| |eapply AGProps.Add_add]; eauto |]. 
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_read; [ | | eapply AGProps.Add_add]; eauto.

  (* weak case *)

  do 2 right; left.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_read; [ | | eapply AGProps.Add_add]; eauto.  

  (* read case *)
  
  do 3 right.
  eapply Hmax; [| eapply AGFacts.add_iff; left; auto];
    eapply Seq.transfer_read; [| | eapply AGProps.Add_add]; intuition eauto 1.


  (* in x m *)
  destruct Hinx as [Hcont | Hinx]; [rewrite Hcont in HneqO; contradiction HneqO; apply Ref.eq_refl
    | apply Hmsub; apply Hinx].
Qed.

Implicit Arguments mutable_project_in_eq [p objs N E a o p' m m' E'].

(* This theorem now exists for backward compatability *)
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
Proof.
  intros p Hmax objs Hobjs N HN E HE a Hnina o Hnino p' Hproj m Hm Hinam m' Hm' E' Hadd.
  eapply RefSetProps.subset_equal; eapply mutable_project_in_eq; eauto.
Qed.

Implicit Arguments mutable_project_in [p objs N E a o p' m m' E'].



(* This proof states that nothing in N was added when considering mutable *)
Theorem mutable_project:
forall p, Seq.maxTransfer p ->
forall objs, Seq.ag_objs_spec p objs ->
forall N, RefSet.Subset objs N ->
forall E, RefSet.Subset E N ->
forall a, RefSet.In a N ->
forall o, ~ RefSet.In o N -> 
forall p', AG_project a o p p' ->
forall m, mutable_spec p E m ->
forall m', mutable_spec p' m m' -> 
RefSet.Subset (RefSet.inter m' N) m.
Proof.
  intros p Hmax objs Hobjs N HN E HE a Hina o Hnino p' Hproj m Hm m' Hm' elt Helt.
  eapply RefSetFacts.inter_iff in Helt; destruct Helt as [HeltM' HeltN].

  case (RefSetProps.In_dec a m); intros Hcase.

  generalize (RefSetProps.Add_add m o); generalize (RefSet.add o m); intros E' HE'.
  generalize (mutable_project_in Hmax Hobjs HN HE Hina Hnino Hproj Hm Hcase Hm' HE'); intros Hsub.
  destruct HE' with elt as [Hcase2 _].
  apply Hcase2 in Hsub; clear Hcase2; auto.
  destruct Hsub as [Heq | Hin]; auto.
  rewrite Heq in *; contradiction.

  generalize (mutable_project_not_in Hmax Hobjs HN HE Hina Hnino Hproj Hm Hcase Hm'); intros Hsub.
  eapply Hsub; auto.

Qed.

(* this is a generalized form of potAcc_approx_dirAcc_dep, which can subsume dirAcc_approx_dep as well.
   It will allow us to generate inductive sequences for both potAcc_execute and dirAcc_execute. *)
Definition general_approx_dirAcc_dep (Fg: AG.t -> AG.t) (Fsa Fsa': Sys.t -> AG.t -> AG.t) :=
  forall s s', Sys.eq s s' -> 
  forall s'', Sys.eq s' s'' ->
  forall i, dirAcc_spec s i -> 
  forall i', AG.Subset i i' -> 
  forall p', AG.Subset (Fg i') p' -> 
    AG.Subset (Fg (Fsa s' i')) (Fsa' s'' p').

Theorem general_approx_dirAcc_dep_potAcc :
  forall Fsa Fp, potAcc_approx_dirAcc_dep Fsa Fp -> general_approx_dirAcc_dep Seq.potAcc_fun Fsa Fp.
Proof.
  intros Fsa Fp Hpa.
  unfold general_approx_dirAcc_dep. intros.
  eapply Hpa.
  apply H.
  apply H0.
  apply H1.
  apply H2.
  apply Seq.potAcc_potAcc_fun.
  apply Seq.potAcc_potAcc_fun.
  auto.
Qed.

Theorem general_approx_dirAcc_dep_refl:
  forall Fsa, Proper (Sys.eq ==> AG.eq ==> AG.eq) Fsa -> 
    (forall s, Seq.ag_subset_commute (Fsa s)) ->
      general_approx_dirAcc_dep (fun a=>a) Fsa Fsa.
Proof.
  unfold general_approx_dirAcc_dep; intros.
  rewrite H2.
  eapply H0; auto.
Qed.

Hint Resolve general_approx_dirAcc_dep_refl general_approx_dirAcc_dep_potAcc.

(* While requiring Fsa and Fsa' to be Proper over equivalence is not strictly necessary for approximation,
   it will be necessary when defining useful approximations over executions. *)
Definition approx_dirAcc_dep Fg Fsa Fsa' := 
  general_approx_dirAcc_dep Fg Fsa Fsa' /\
  ag_nondecr Fg /\
  Seq.ag_equiv Fg /\
  Proper (Sys.eq ==> AG.eq ==> AG.eq) Fsa /\
  Proper (Sys.eq ==> AG.eq ==> AG.eq) Fsa'.



Theorem approx_dirAcc_dep_refl:
  forall Fsa, Proper (Sys.eq ==> AG.eq ==> AG.eq) Fsa -> 
    (forall s, Seq.ag_subset_commute (Fsa s)) ->
    approx_dirAcc_dep (fun a=>a) Fsa Fsa.
Proof.
  unfold approx_dirAcc_dep;
    unfold ag_nondecr;
      unfold Seq.ag_subset_commute;
        unfold Seq.ag_equiv;
          intuition eauto.
Qed.

Theorem ag_potTransfer_fn_req_dirAcc_op: forall op s, Seq.ag_potTransfer_fn_req (dirAcc_op op s).
Proof.
  intros op s; destruct op; simpl;
  intuition eauto.
  case (SemDefns.fetch_preReq_dec t t0 s); intuition (eauto ;apply potTransfer_fn_req_fetch).
  case (SemDefns.store_preReq_dec t t0 s); intuition (eauto ;apply potTransfer_fn_req_store).
  case (SemDefns.send_preReq_dec t t0 s); intuition (eauto ;apply potTransfer_fn_req_send).
  case (SemDefns.allocate_preReq_dec t t0 s); intuition (eauto ;apply potTransfer_fn_req_allocate).
Qed.

Hint Resolve ag_potTransfer_fn_req_dirAcc_op.

Theorem ag_potTransfer_fn_req_dirAcc_execute: forall opList s,  Seq.ag_potTransfer_fn_req (dirAcc_execute opList s).
Proof.
  intros opList s; induction opList; eauto.
  simpl. unfold compose.
  generalize (ag_potTransfer_fn_req_dirAcc_op a (Exe.execute s opList)); intros Hdaop.
  unfold Seq.ag_potTransfer_fn_req in *.
  unfold Seq.ag_add_commute in *;
  unfold ag_nondecr in *;
  unfold Seq.ag_equiv in *;
  intuition; intros; eauto.
Qed.

Hint Resolve ag_potTransfer_fn_req_dirAcc_execute.

Theorem approx_dirAcc_dep_dirAcc_execute:
  forall opList, approx_dirAcc_dep (fun a=>a) (dirAcc_execute opList) (dirAcc_execute opList).
Proof.
  intros.
  eapply approx_dirAcc_dep_refl.
  eapply dirAcc_execute_spec_proper; eapply dirAcc_execute_spec_dirAcc_execute.
  intros; generalize (ag_potTransfer_fn_req_dirAcc_execute opList s); intros.
  intros; eapply Seq.ag_subset_add_commute; unfold Seq.ag_potTransfer_fn_req in *; intuition eauto.
Qed.


  Theorem potAcc_equiv : forall ag ag', AG.Equal ag ag' ->
    forall p, Seq.potAcc ag p -> 
      forall p', Seq.potAcc ag' p' -> AG.Equal p p'.
  Proof.
    intros.
    eapply Proper_potAcc in H0; [| apply AG.eq_sym; apply H |apply AG.eq_refl].
    destruct H1 as [Ht' Hm']; destruct H0 as [Ht Hm].
    generalize (Seq.potTransfer_lub Ht Ht'); intros [c [Ht2' Ht2]].
    eapply Hm in Ht2; eapply Hm' in Ht2'.
    eauto.
  Qed.

  Hint Resolve potAcc_equiv.

Theorem approx_dirAcc_dep_potAcc:
  forall Fsa, Proper (Sys.eq ==> AG.eq ==> AG.eq) Fsa -> 
  forall Fp, Proper (Sys.eq ==> AG.eq ==> AG.eq) Fp -> 
    potAcc_approx_dirAcc_dep Fsa Fp -> approx_dirAcc_dep Seq.potAcc_fun Fsa Fp.
Proof.
  unfold approx_dirAcc_dep; intros;
    unfold ag_nondecr;
      unfold Seq.ag_subset_commute;
        unfold Seq.ag_equiv;
         intuition eauto 2;
           generalize (Seq.potAcc_potAcc_fun ag'); 
             generalize (Seq.potAcc_fun ag'); intros p' Hp';
               generalize (Seq.potAcc_potAcc_fun ag); 
                 generalize (Seq.potAcc_fun ag); intros p Hp;
                   eauto 2.

  eapply AGProps.subset_trans;[apply H2|
  eapply Seq.potTransfer_subset; destruct Hp'; auto].
  
Qed.


Require Import Coq.Relations.Relation_Definitions.

(* This is probably not nearly general enough, nor using correct nomenclature *)

Definition indexed {A B:Type} (R: relation A) (R': relation B) (ind: A -> B -> Prop) := 
  forall (a a':A), (R a a') -> forall (b:B), ind a b -> forall b', ind a' b' -> (R' b b').




Inductive mutable_execute Fg (exe_spec: list Sem.operation -> (Sys.t -> AG.t -> AG.t) -> Prop) :
   list Sem.operation -> Sys.t -> RefSet.t -> RefSet.t -> Prop :=
| mutable_execute_nil: forall Fdx, dirAcc_execute_spec nil Fdx -> 
  indexed eq eq exe_spec ->
    forall Ftx, exe_spec nil Ftx -> approx_dirAcc_dep Fg Fdx Ftx -> 
    forall s i, dirAcc_spec s i ->
      forall E M, mutable_spec (Ftx s (Fg i)) E M -> mutable_execute Fg exe_spec nil s E M
| mutable_execute_cons: forall opList Fdx, dirAcc_execute_spec opList Fdx ->
  indexed eq eq exe_spec ->
    forall Ftx, exe_spec opList Ftx -> approx_dirAcc_dep Fg Fdx Ftx ->
    forall s i, dirAcc_spec s i ->
    forall E M, mutable_execute Fg exe_spec opList s E M ->
      forall op Fdx', dirAcc_execute_spec (cons op opList) Fdx' ->
        forall Ftx', exe_spec (cons op opList) Ftx' -> approx_dirAcc_dep Fg Fdx' Ftx' ->
            forall M', mutable_spec (Ftx' s (Fg i)) M M' -> mutable_execute Fg exe_spec (cons op opList) s E M'.

Definition mutable_dirAcc_execute := mutable_execute (fun a => a) dirAcc_execute_spec.
Definition mutable_potAcc_execute := mutable_execute Seq.potAcc_fun potAcc_execute_spec.


Theorem indexed_dirAcc_execute_spec: indexed eq eq dirAcc_execute_spec.
Proof.
  unfold indexed; intros;
  eapply dirAcc_execute_spec_eq_iff in H0;
  eapply dirAcc_execute_spec_eq_iff in H1;
  rewrite H0; rewrite H1; rewrite H; auto.
Qed.

Theorem indexed_potAcc_execute_spec: indexed eq eq potAcc_execute_spec.
Proof.
  unfold indexed; intros;
  eapply potAcc_execute_spec_eq_iff in H0;
  eapply potAcc_execute_spec_eq_iff in H1;
  rewrite H0; rewrite H1; rewrite H; auto.
Qed.


Theorem exists_mutable_dirAcc_execute: forall opList s E, exists m, mutable_dirAcc_execute opList s E m.
Proof.
  intros opList s E.
  induction opList.
  (* base *)
  eapply ex_intro; econstructor.
  
  eapply dirAcc_execute_spec_dirAcc_execute.
  eapply indexed_dirAcc_execute_spec.
  econstructor.

  unfold dirAcc_execute; unfold id_ag;
  eapply approx_dirAcc_dep_refl; eauto.
  
  intros; unfold Seq.ag_subset_commute; eauto.

  eapply dirAcc_spec_dirAcc.
  eapply mutable_spec_mutable.
  
  (* step *)

  destruct IHopList as [m Hm].
  eapply ex_intro.
  econstructor.

  unfold mutable_dirAcc_execute in *.
  eapply dirAcc_execute_spec_dirAcc_execute.
  eapply indexed_dirAcc_execute_spec.
  eapply dirAcc_execute_spec_dirAcc_execute.

  eapply approx_dirAcc_dep_dirAcc_execute.
  eapply dirAcc_spec_dirAcc.
  apply Hm.
  apply dirAcc_execute_spec_dirAcc_execute.
  apply dirAcc_execute_spec_dirAcc_execute.
  eapply approx_dirAcc_dep_dirAcc_execute.
  eapply mutable_spec_mutable.
Qed.

Theorem Proper_ag_add_cap: Proper (Ref.eq ==> Cap.eq ==> AG.eq ==> AG.eq) ag_add_cap.
Proof.
  unfold Proper; unfold respectful; intros.
  eapply ag_add_cap_equiv; auto.
Qed.
Hint Resolve Proper_ag_add_cap.

Theorem Proper_mkCap : Proper (Ref.eq ==> ARSet.eq ==> Cap.eq) Cap.mkCap.
Proof.
  unfold Proper; unfold respectful; intros.
  eapply CC.mkCap_equiv; eauto.
Qed.
Hint Resolve Proper_mkCap.

Theorem Proper_insert: Proper (Ref.eq ==> Ref.eq ==> AG.eq ==> AG.eq) insert.
Proof.
  unfold Proper; unfold respectful; intros.
  unfold insert.
  eapply Proper_ag_add_cap; [auto | eapply Proper_mkCap; auto |
    eapply Proper_ag_add_cap; [auto | eapply Proper_mkCap; auto | auto]].
Qed.
Hint Resolve Proper_insert.

Theorem Proper_potAcc_fun : Proper (AG.eq ==> AG.eq) Seq.potAcc_fun.
Proof.
  unfold Proper; unfold respectful; intros.
  eapply potAcc_equiv; solve [ eapply H| apply Seq.potAcc_potAcc_fun].
Qed.
Hint Resolve Proper_potAcc_fun.

Theorem Proper_endow: Proper (Ref.eq ==> Ref.eq ==> AG.eq ==> AG.eq) endow.
Proof.
  unfold Proper; unfold respectful; intros.
  unfold endow.
  eapply Proper_potAcc_fun.
  eapply Proper_insert; auto.
Qed.
Hint Resolve Proper_endow.

Theorem Proper_endow_dep: Proper (Ref.eq ==> Ref.eq ==> Sys.eq ==> AG.eq ==> AG.eq) endow_dep.
Proof.
  unfold Proper; unfold respectful; intros.
  unfold endow_dep.
  case (SemDefns.allocate_preReq_dec y y0 y1); intros c;
    (case (SemDefns.allocate_preReq_dec x x0 x1); intros c');
    try solve[eauto
      | eapply Proper_endow; eauto
      | eapply SemDefns.allocate_preReq_eq_iff in c; eauto; contradiction
      | eapply SemDefns.allocate_preReq_eq_iff in c';
        first [apply AG.eq_sym | apply Sys.eq_sym | apply Ref.eq_sym | idtac]; eauto; contradiction
    ].
Qed.
Hint Resolve Proper_endow_dep.

Theorem Proper_potAcc_op: Proper (eq ==> Sys.eq ==> AG.eq ==> AG.eq) potAcc_op.
Proof.
  unfold Proper; unfold respectful; intros.
  rewrite H in *; clear H; clear x.
  destruct y; simpl; eauto.
  eapply Proper_endow_dep; auto; try apply Ref.eq_refl.
Qed.
Hint Resolve Proper_potAcc_op.

Theorem Proper_potAcc_execute: Proper (eq ==> Sys.eq ==> AG.eq ==> AG.eq) potAcc_execute.
Proof.
  unfold Proper; unfold respectful; intros.
  rewrite H in *; clear H; clear x.
  induction y; simpl.
  unfold id_ag; auto.
  
  eapply Proper_potAcc_op;  auto.
  eapply execute_proper_1; auto.
Qed.
Hint Resolve Proper_potAcc_execute.

Theorem Proper_dirAcc_execute: Proper (eq ==> Sys.eq ==> AG.eq ==> AG.eq) dirAcc_execute.
Proof.
  unfold Proper; unfold respectful; intros.
  rewrite H in *; clear H; clear x.
  induction y; simpl.
  unfold id_ag; auto.
  
  eapply Proper_dirAcc_op; auto.
  eapply execute_proper_1; auto.
Qed.
Hint Resolve Proper_dirAcc_execute.

Theorem exists_mutable_potAcc_execute: forall opList s E, exists m, mutable_potAcc_execute opList s E m.
Proof.
  intros opList s E.
  induction opList.
  (* base *)
  eapply ex_intro; econstructor 1.
  
  eapply dirAcc_execute_spec_dirAcc_execute.
  eapply indexed_potAcc_execute_spec.
  eapply potAcc_execute_spec_potAcc_execute.

  eapply approx_dirAcc_dep_potAcc; auto.

  eapply potAcc_execute_approx; 
    [eapply dirAcc_execute_spec_dirAcc_execute
      | eapply potAcc_execute_spec_potAcc_execute].
  
  eapply dirAcc_spec_dirAcc.
  eapply mutable_spec_mutable.

  (* step *)

  destruct IHopList as [m Hm].
  eapply ex_intro.
  unfold mutable_potAcc_execute in *.
  econstructor.

  eapply dirAcc_execute_spec_dirAcc_execute.
  eapply indexed_potAcc_execute_spec.
  eapply potAcc_execute_spec_potAcc_execute.

  eapply approx_dirAcc_dep_potAcc; eauto.

  eapply potAcc_execute_approx; 
    [eapply dirAcc_execute_spec_dirAcc_execute
      | eapply potAcc_execute_spec_potAcc_execute].
  eapply dirAcc_spec_dirAcc.
  eapply Hm.
  apply dirAcc_execute_spec_dirAcc_execute.
  apply potAcc_execute_spec_potAcc_execute.
  eapply approx_dirAcc_dep_potAcc; eauto.
  eapply potAcc_execute_approx; 
    [eapply dirAcc_execute_spec_dirAcc_execute
      | eapply potAcc_execute_spec_potAcc_execute].
  eapply mutable_spec_mutable.
Qed.

Theorem mutable_execute_equiv: 
  forall s s', Sys.eq s s' ->
    forall E E', RefSet.eq E E' ->
      forall Fg opList exe_spec m, mutable_execute Fg exe_spec opList s E m -> 
        forall m', mutable_execute Fg exe_spec opList s' E' m' ->
        RefSet.eq m m'.
Proof.
  intros s s' HeqS E E' HeqE Fg opList exe_spec.
  induction opList; intros m Hm m' Hm'; inversion Hm; inversion Hm'.
  (* base *)
  eapply mutable_spec_eq_iff; try solve[ eauto].
  assert (Ftx0 = Ftx) as Hftx; [eapply H9; eauto|rewrite Hftx in *].
  destruct H11 as [Hgen [Hmon [Hequiv [Hprop Hprop']]]].
  eapply Hprop'; eauto.
  eapply Hequiv.
  eapply dirAcc_spec_eq; eauto.

  (* step *)
  eapply mutable_spec_eq_iff; eauto.
  assert (Ftx' = Ftx'0) as Hftx;[eapply H2; [auto | apply H8 | apply H23]|rewrite Hftx in *].
  
  destruct H9 as [Hgen [Hmon [Heq [Hproper1 Hproper2]]]].
  eapply Hproper2; eauto.
  eapply Heq. eapply dirAcc_spec_eq; eauto.
Qed.

Hint Resolve mutable_execute_equiv.

(* quick specialization of above *)
Theorem mutable_dirAcc_execute_equiv :
  forall s s', Sys.eq s s' ->
    forall E E', RefSet.eq E E' ->
      forall opList m, mutable_dirAcc_execute opList s E m -> 
        forall m', mutable_dirAcc_execute opList s' E' m' ->
        RefSet.eq m m'.
Proof.
  intros; eauto.
Qed.

Theorem mutable_potAcc_execute_equiv :
  forall s s', Sys.eq s s' ->
    forall E E', RefSet.eq E E' ->
      forall opList m, mutable_potAcc_execute opList s E m -> 
        forall m', mutable_potAcc_execute opList s' E' m' ->
        RefSet.eq m m'.
Proof.
  intros; eauto.
Qed.

Theorem mutable_execute_subset:
  forall Fg Fg' exe_spec exe_spec',
    forall opList s E m, mutable_execute Fg exe_spec opList s E m -> 
      forall E', RefSet.Subset E E' ->
      forall m', mutable_execute Fg' exe_spec' opList s E' m' -> 
        (forall opl FXa, exe_spec opl FXa -> forall FXb, exe_spec' opl FXb -> 
          forall s s', Sys.eq s s' -> forall i, dirAcc_spec s i -> 
            forall a, AG.Subset i a -> forall a', AG.Subset a a' ->
            AG.Subset (FXa s (Fg a)) (FXb s' (Fg' a'))) -> 
        RefSet.Subset m m'.
Proof.
  intros Fa Fb EXEa EXEb opList s E m Hm E' Hesub m' Hm' Hsub.
  revert s E E' Hesub m m' Hm Hm'.
  induction opList; intros s E E' Hesub m m' Hm Hm';
    inversion Hm; inversion Hm'.
  rename Ftx into FXa; rename Ftx0 into FXb; rename Fdx0 into Fdx'.
  (* base *)
  eapply mutable_spec_subset; 
    [ apply Hesub
      | 
      | apply H13
      | apply H4
    ].

  eapply Hsub; eauto 3;
    try solve [apply Sys.eq_refl | apply AGProps.subset_equal; eapply dirAcc_spec_eq; eauto 2; try apply Sys.eq_refl].

(* step *)
  eapply mutable_spec_subset;
    [eapply IHopList; eauto
      |
      | apply H28
      | apply H13
    ].
  eapply Hsub; eauto 3;
    try solve [apply Sys.eq_refl | apply AGProps.subset_equal; eapply dirAcc_spec_eq; eauto 2; try apply Sys.eq_refl].
Qed.

Theorem Proper_mutable_execute_impl : Proper (eq ==> eq ==> eq ==> Sys.eq ==> RefSet.eq ==> RefSet.eq ==> impl) mutable_execute.
Proof.
  unfold Proper; unfold respectful; unfold impl.
  intros x y H x0 y0 H0 x1. induction x1; intros;

  (* base *)
  rewrite <- H in *;
  rewrite <- H0 in *;
  rewrite <- H1 in *;
    inversion H5;
  econstructor; eauto 3.

  eapply dirAcc_spec_iff; eauto 2; try apply AG.eq_refl.
  eapply Proper_mutable_spec; eauto.
  destruct H9 as [Hgen [Heq [Hmon [Hprop Hprop']]]].
  eapply Hprop'; eauto; try apply AG.eq_refl.

  (* step. *)
  eapply dirAcc_spec_iff; eauto 2; try apply AG.eq_refl.
  eapply IHx1.
  5: apply H13.
  apply eq_refl.
  apply H2.
  apply H3.
  apply RefSet.eq_refl.

  eapply Proper_mutable_spec; eauto 2; try apply RefSet.eq_refl.
  destruct H16 as [Hgen [Heq [Hmon [Hprop Hprop']]]].
  eapply Hprop'; eauto; try apply AG.eq_refl.
Qed.

Theorem Proper_mutable_execute : Proper (eq ==> eq ==> eq ==> Sys.eq ==> RefSet.eq ==> RefSet.eq ==> iff) mutable_execute.
Proof.
  split; eapply Proper_mutable_execute_impl; eauto 2; try (apply RefSet.eq_sym; eauto 2).
Qed.

Hint Resolve Proper_mutable_execute.

  Theorem preReq_dirAcc:
    forall a t s, SemDefns.preReq a t s ->
      forall i, dirAcc_spec s i ->
        exists cap, SC.getCap t a s = Some cap /\ 
          forall r, ARSet.In r (Cap.rights cap) -> AG.In (Edges.mkEdge a (Cap.target cap) r) i.
  Proof.
    intros a t s [[Halive Hactive] HtargetAlive] i Hda.
    unfold SemDefns.target_is_alive in *.
    
  case (option_sumbool (SC.getCap t a s)); intros HcaseCap; [|destruct HcaseCap as [cap HcaseCap]];
    rewrite HcaseCap in *; simpl in HtargetAlive; try contradiction.
  eapply ex_intro; split; [auto| intros r Hin; eapply dirAcc_simpl; eauto; try eapply Ref.eq_refl].
  
  Qed.    

Theorem mutable_execute_dirAcc_subset_potAcc:
  forall s s', Sys.eq s s' ->
    forall E E', RefSet.Subset E E' ->
      forall opList m, mutable_dirAcc_execute opList s E m -> 
        forall m', mutable_potAcc_execute opList s' E' m' ->
          RefSet.Subset m m'.
Proof.
  intros.
  unfold mutable_dirAcc_execute in *.
  unfold mutable_potAcc_execute in *.

  eapply Proper_mutable_execute in H2; eauto 1; try apply RefSet.eq_refl.
  
  eapply mutable_execute_subset. apply H1. apply H0. apply H2.

  (* and finally what ammounts to potAcc_execute_approx *)
  intros.
  generalize (potAcc_execute_approx _ _ H3 _ H4); intros Happrox.
  generalize (ag_potTransfer_fn_req_dirAcc_execute opl s0); intros [Hcomm [_ Hequiv]].
  eapply Seq.ag_subset_add_commute in Hcomm; eauto 2.

  (* rewrite dirAcc_ and potAcc_execute *)
  eapply dirAcc_execute_spec_eq_iff in H3; rewrite H3 in *.
  eapply potAcc_execute_spec_eq_iff in H4; rewrite H4 in *.

  (* dirAcc_execute is commutative with subset with a [<=] a' *)
  eapply AGProps.subset_trans; [eapply Hcomm; apply H8|].

  (* potAcc (via potTransfer) is a superset *)
  eapply AGProps.subset_trans; [eapply Seq.potTransfer_subset; eapply Seq.potAcc_potAcc_fun|].

  (* potAcc_approx_dirAcc_dep is approximating *)
  eapply Happrox;
    [eapply Sys.eq_refl
      | eapply H5
      | eapply H6
      | eapply AGProps.subset_trans; [ apply H7|apply H8]
      | eapply Seq.potAcc_potAcc_fun
      | eapply Seq.potAcc_potAcc_fun
      | eapply AGProps.subset_refl
    ].
Qed.

Theorem mutable_dirAcc_execute_approx_mutated :
  forall s s', Sys.eq s s' ->
    forall E E', RefSet.eq E E' ->
      forall opList m, mutated_def E s opList m ->
        forall m', mutable_dirAcc_execute opList s' E' m' ->
          RefSet.Subset m m'.
Proof.


  intros s s' HeqS E E' HeqE opList; revert s s' HeqS E E' HeqE; induction opList; 
    intros s s' HeqS E E' HeqE m Hm m' Hm'; inversion Hm; inversion Hm'.
  (* base *)
  (* rewrite dirAcc_execute *)
  eapply dirAcc_execute_spec_eq_iff in H0; rewrite H0 in *;
    eapply dirAcc_execute_spec_eq_iff in H3; rewrite H3 in *;
    rewrite H in *; rewrite HeqE in *; eauto 3.
  (* step *)
  eapply dirAcc_execute_spec_eq_iff in H7; rewrite H7 in *;
    eapply dirAcc_execute_spec_eq_iff in H9; rewrite H9 in *;
      eapply dirAcc_execute_spec_eq_iff in H13; rewrite H13 in *;
        eapply dirAcc_execute_spec_eq_iff in H14; rewrite H14 in *.
  (* clear generated equations *)
  clear op H opList0 H0 n3 H3 Fdx H7 Ftx H9 Fdx' H13 Ftx' H14 op0 H5 opList1 H6 H15 s0 H16 E0 H17 M' H18.
  
  (* generalize IH, should apply in future *)
  generalize (IHopList _ _ HeqS _ _ HeqE _ H1 _ H12); intros IH.
  inversion H4.
  (* We can probably get by using inversion *)
  (* we need theorems allowing us to rewrite mutated_def and mutated_op_def as mutated and mutated_op. 
     This will allow us to replace m in the proof by (mutated_op n2 s'0 a) *)

  (* case with no change *)
  rewrite <- H.
  eapply RefSetProps.subset_trans; [ apply IH |].
  eapply mutable_nondec; eauto 2.

  (* case with change *)
  rewrite <- H in *; clear n' H n0 H7.
  rename n2 into n.

  rewrite <- H6.  

  (* the source of mutation is in read_from *)
  unfold RefSet.Exists in H3.
  destruct H3 as [src [HinSrc HrfSrc]].

  (* we introduce all mutated objects as the target, since by IH, all but the new target will discharge
     through subset transitivity .*)
  intros tgt Hin.
  eapply RefSetFacts.union_iff in Hin.

  (* cases: In tgt n /\ ~ In tgt n
     IH: n [<=] M
     H20: mutable_spec (dirAcc_execute (a :: opList) s' i) M m'
     by mutable_nondec H20, M [<=] m'.  Use subset_trans, qed.
     
     The following tactic solves all of these cases, the remaining case is:

     case ~ In tgt n /\ In tgt wt 
     *)

  case (RefSetProps.In_dec tgt n); intros Hcase; destruct Hin as [Hin | Hin]; 
    try solve [contradiction | eapply mutable_nondec in H19; eauto].
  rename a into op.

  (* instantiate dirAcc s'0 *)
  generalize (dirAcc_spec_dirAcc s'0); generalize (dirAcc s'0); intros i'0 Hda'0.


  (* invert read_from and wrote_to, eliminate all but the 16 non-contradictory cases,
     use Empty on invalid operations to eliminate 8 of those cases *)
  inversion H5; inversion H0; rewrite <- H7 in H15;
  inversion H15 as [[H' H'2]];  rewrite H' in *; rewrite H'2 in *; try contradiction;
    eapply H3 in Hin; try contradiction;
  eapply H14 in HrfSrc.

  (* read *)


  (* propagate prereqs *)
  destruct H13 as [HpreReq HopReq].
  unfold Sem.add_option_target in HrfSrc.
  unfold SemDefns.option_hasRight in HopReq.
  eapply preReq_dirAcc in HpreReq; [destruct HpreReq as [cap [Hcap Hda]]|eauto].

  rewrite Hcap in *; simpl in HrfSrc; simpl in HopReq.
  unfold CC.hasRight in HopReq.


  
  (* so how do we prove that one of these edges is available?
     we know that dirAcc_op is non_decreasing, so if something is in opList, it is in op:opList.
     From preReqs, we can place the invoked edge in (dirAcc s'0)
     From the invoked edge, we can place self weak on the actor in (dirAcc s'0)
     From dirAcc_execute_approx, we can place both of these in (dirAcc_execute opList s' i)
     From dirAcc_op_monotonic (or similar) we can place them in (dirAcc_execute (op::opList) s' i)
     *)

  (* rewrite src and tgt by cases. *)
  eapply RefSetFacts.singleton_iff in Hin; rewrite <- Hin in *.
  destruct HopReq as [HopReq | HopReq]; apply Hda in HopReq;
  (* reduce cases on Hin and HrfSrc *)
    (eapply RefSetFacts.add_iff in HrfSrc;
      destruct HrfSrc as [HrfSrc | HrfSrc]; [|eapply RefSetFacts.singleton_iff in HrfSrc]; rewrite <- HrfSrc in *
       );
    try solve [ contradiction
      |

  (* use dirAcc_execute_approx to lift from dirAcc to dirAcc_execute *)
  eapply dirAcc_execute_approx in HopReq;
    [
      | apply dirAcc_execute_spec_dirAcc_execute
      | apply H11
      | eapply dirAcc_spec_iff;
        [ eapply Sys.eq_trans;
          [eapply execute_proper_1;
            [apply Sys.eq_sym; apply HeqS
              |apply eq_refl]
            | eapply Exe.execute_spec; eapply H2]
          | eapply AG.eq_refl
          | eapply Hda'0]
      | eapply AGProps.subset_refl
      | eapply Sys.eq_refl];


  (* apply mutable_spec and select on the case with src in dirAcc *)
  eapply H19;
  right; eapply ex_intro with src; rewrite <- HrfSrc in *;
  split; [eauto|];

  (* use dirAcc_op nondecreasing to lift the edge through dirAcc_op *)
  edestruct ag_potTransfer_fn_req_dirAcc_op as [Haddcomm [Hmon Heq]];
  eapply Hmon in HopReq;[|eapply AGProps.subset_refl];
  intuition eauto 2].

  (* write *)

  (* propagate prereqs *)
  destruct H13 as [HpreReq HopReq].
  unfold Sem.add_option_target in HrfSrc.
  unfold Sem.add_option_target in Hin.
  unfold SemDefns.option_hasRight in HopReq.
  eapply preReq_dirAcc in HpreReq; [destruct HpreReq as [cap [Hcap Hda]]|eauto].

  rewrite Hcap in *; simpl in *.
  unfold CC.hasRight in HopReq.

  (* rewrite src and tgt by cases. *)
  
  try eapply RefSetProps.singleton_equal_add in Hin.
  eapply RefSetFacts.singleton_iff in Hin; rewrite <- Hin in *.
  (* no destruct *) apply Hda in HopReq.
  (* reduce cases on Hin and HrfSrc *)
  eapply RefSetFacts.singleton_iff in HrfSrc; rewrite <- HrfSrc in *; 
    try solve [ contradiction
      |

  (* use dirAcc_execute_approx to lift from dirAcc to dirAcc_execute *)
  eapply dirAcc_execute_approx in HopReq;
    [
      | apply dirAcc_execute_spec_dirAcc_execute
      | apply H11
      | eapply dirAcc_spec_iff;
        [ eapply Sys.eq_trans;
          [eapply execute_proper_1;
            [apply Sys.eq_sym; apply HeqS
              |apply eq_refl]
            | eapply Exe.execute_spec; eapply H2]
          | eapply AG.eq_refl
          | eapply Hda'0]
      | eapply AGProps.subset_refl
      | eapply Sys.eq_refl];


  (* apply mutable_spec and select on the case with src in dirAcc *)
  eapply H19;
  right; eapply ex_intro with src; rewrite <- HrfSrc in *;
  split; [eauto|];

  (* use dirAcc_op nondecreasing to lift the edge through dirAcc_op *)
  edestruct ag_potTransfer_fn_req_dirAcc_op as [Haddcomm [Hmon Heq]];
  eapply Hmon in HopReq;[|eapply AGProps.subset_refl];
  intuition eauto 2].

  (* fetch *)

  (* propagate prereqs *)
  destruct H13 as [HpreReq HopReq].
  unfold Sem.add_option_target in HrfSrc.
  unfold Sem.add_option_target in Hin.
  unfold SemDefns.option_hasRight in HopReq.
  eapply preReq_dirAcc in HpreReq; [destruct HpreReq as [cap [Hcap Hda]]|eauto].

  rewrite Hcap in *; simpl in *.
  unfold CC.hasRight in HopReq.

  (* rewrite src and tgt by cases. *)
  
  eapply RefSetFacts.singleton_iff in Hin; rewrite <- Hin in *.
  destruct HopReq as [HopReq | HopReq]; apply Hda in HopReq;
  (* reduce cases on Hin and HrfSrc *)
    (eapply RefSetFacts.add_iff in HrfSrc;
      destruct HrfSrc as [HrfSrc | HrfSrc]; [|eapply RefSetFacts.singleton_iff in HrfSrc]; rewrite <- HrfSrc in *
       );
    try solve [ contradiction
      |

  (* use dirAcc_execute_approx to lift from dirAcc to dirAcc_execute *)
  eapply dirAcc_execute_approx in HopReq;
    [
      | apply dirAcc_execute_spec_dirAcc_execute
      | apply H11
      | eapply dirAcc_spec_iff;
        [ eapply Sys.eq_trans;
          [eapply execute_proper_1;
            [apply Sys.eq_sym; apply HeqS
              |apply eq_refl]
            | eapply Exe.execute_spec; eapply H2]
          | eapply AG.eq_refl
          | eapply Hda'0]
      | eapply AGProps.subset_refl
      | eapply Sys.eq_refl];


  (* apply mutable_spec and select on the case with src in dirAcc *)
  eapply H19;
  right; eapply ex_intro with src; rewrite <- HrfSrc in *;
  split; [eauto|];

  (* use dirAcc_op nondecreasing to lift the edge through dirAcc_op *)
  edestruct ag_potTransfer_fn_req_dirAcc_op as [Haddcomm [Hmon Heq]];
  eapply Hmon in HopReq;[|eapply AGProps.subset_refl];
  intuition eauto 2].
  
  (* store *)

(* propagate prereqs *)
  destruct H13 as [HpreReq HopReq].
  unfold Sem.add_option_target in HrfSrc.
  unfold Sem.add_option_target in Hin.
  unfold SemDefns.option_hasRight in HopReq.
  eapply preReq_dirAcc in HpreReq; [destruct HpreReq as [cap [Hcap Hda]]|eauto].

  rewrite Hcap in *; simpl in *.
  unfold CC.hasRight in HopReq.

  (* rewrite src and tgt by cases. *)
  
  try eapply RefSetProps.singleton_equal_add in Hin.
  eapply RefSetFacts.singleton_iff in Hin; rewrite <- Hin in *.
  (* no destruct *) apply Hda in HopReq.
  (* reduce cases on Hin and HrfSrc *)
  eapply RefSetFacts.singleton_iff in HrfSrc; rewrite <- HrfSrc in *; 
    try solve [ contradiction
      |

  (* use dirAcc_execute_approx to lift from dirAcc to dirAcc_execute *)
  eapply dirAcc_execute_approx in HopReq;
    [
      | apply dirAcc_execute_spec_dirAcc_execute
      | apply H11
      | eapply dirAcc_spec_iff;
        [ eapply Sys.eq_trans;
          [eapply execute_proper_1;
            [apply Sys.eq_sym; apply HeqS
              |apply eq_refl]
            | eapply Exe.execute_spec; eapply H2]
          | eapply AG.eq_refl
          | eapply Hda'0]
      | eapply AGProps.subset_refl
      | eapply Sys.eq_refl];


  (* apply mutable_spec and select on the case with src in dirAcc *)
  eapply H19;
  right; eapply ex_intro with src; rewrite <- HrfSrc in *;
  split; [eauto|];

  (* use dirAcc_op nondecreasing to lift the edge through dirAcc_op *)
  edestruct ag_potTransfer_fn_req_dirAcc_op as [Haddcomm [Hmon Heq]];
  eapply Hmon in HopReq;[|eapply AGProps.subset_refl];
  intuition eauto 2].

  (* revoke *)


  (* propagate prereqs *)
  destruct H13 as [HpreReq HopReq].
  unfold Sem.add_option_target in HrfSrc.
  unfold Sem.add_option_target in Hin.
  unfold SemDefns.option_hasRight in HopReq.
  eapply preReq_dirAcc in HpreReq; [destruct HpreReq as [cap [Hcap Hda]]|eauto].

  rewrite Hcap in *; simpl in *.
  unfold CC.hasRight in HopReq.

  (* rewrite src and tgt by cases. *)
  
  try eapply RefSetProps.singleton_equal_add in Hin.
  eapply RefSetFacts.singleton_iff in Hin; rewrite <- Hin in *.
  (* no destruct *) apply Hda in HopReq.
  (* reduce cases on Hin and HrfSrc *)
  eapply RefSetFacts.singleton_iff in HrfSrc; rewrite <- HrfSrc in *; 
    try solve [ contradiction
      |

  (* use dirAcc_execute_approx to lift from dirAcc to dirAcc_execute *)
  eapply dirAcc_execute_approx in HopReq;
    [
      | apply dirAcc_execute_spec_dirAcc_execute
      | apply H11
      | eapply dirAcc_spec_iff;
        [ eapply Sys.eq_trans;
          [eapply execute_proper_1;
            [apply Sys.eq_sym; apply HeqS
              |apply eq_refl]
            | eapply Exe.execute_spec; eapply H2]
          | eapply AG.eq_refl
          | eapply Hda'0]
      | eapply AGProps.subset_refl
      | eapply Sys.eq_refl];


  (* apply mutable_spec and select on the case with src in dirAcc *)
  eapply H19;
  right; eapply ex_intro with src; rewrite <- HrfSrc in *;
  split; [eauto|];

  (* use dirAcc_op nondecreasing to lift the edge through dirAcc_op *)
  edestruct ag_potTransfer_fn_req_dirAcc_op as [Haddcomm [Hmon Heq]];
  eapply Hmon in HopReq;[|eapply AGProps.subset_refl];
  intuition eauto 2].

  (* send *)


  (* propagate prereqs *)
  destruct H13 as [HpreReq HopReq].
  unfold Sem.add_option_target in HrfSrc.
  unfold Sem.add_option_target in Hin.
  unfold SemDefns.option_hasRight in HopReq.
  eapply preReq_dirAcc in HpreReq; [destruct HpreReq as [cap [Hcap Hda]]|eauto].

  rewrite Hcap in *; simpl in *.
  unfold CC.hasRight in HopReq.

  (* rewrite src and tgt by cases. *)
  
  try eapply RefSetProps.singleton_equal_add in Hin.
  eapply RefSetFacts.singleton_iff in Hin; rewrite <- Hin in *.
  (* no destruct *) apply Hda in HopReq.
  (* reduce cases on Hin and HrfSrc *)
  eapply RefSetFacts.singleton_iff in HrfSrc; rewrite <- HrfSrc in *; 
    try solve [ contradiction
      |

  (* use dirAcc_execute_approx to lift from dirAcc to dirAcc_execute *)
  eapply dirAcc_execute_approx in HopReq;
    [
      | apply dirAcc_execute_spec_dirAcc_execute
      | apply H11
      | eapply dirAcc_spec_iff;
        [ eapply Sys.eq_trans;
          [eapply execute_proper_1;
            [apply Sys.eq_sym; apply HeqS
              |apply eq_refl]
            | eapply Exe.execute_spec; eapply H2]
          | eapply AG.eq_refl
          | eapply Hda'0]
      | eapply AGProps.subset_refl
      | eapply Sys.eq_refl];


  (* apply mutable_spec and select on the case with src in dirAcc *)
  eapply H19;
  right; eapply ex_intro with src; rewrite <- HrfSrc in *;
  split; [eauto|];

  (* use dirAcc_op nondecreasing to lift the edge through dirAcc_op *)
  edestruct ag_potTransfer_fn_req_dirAcc_op as [Haddcomm [Hmon Heq]];
  eapply Hmon in HopReq;[|eapply AGProps.subset_refl];
  intuition eauto 2].

  (* allocate *)

  (* propagate prereqs *)
  (*destruct H13 as [Halive Hunborn].
  unfold Sem.add_option_target in HrfSrc.
  unfold Sem.add_option_target in Hin. *)

  (* rewrite src and tgt by cases. *)

  eapply RefSetFacts.singleton_iff in HrfSrc; rewrite <- HrfSrc in *.
  (* reduce cases on Hin and HrfSrc *)
  eapply RefSetFacts.add_iff in Hin;
      destruct Hin as [Hin | Hin]; [|eapply RefSetFacts.singleton_iff in Hin]; rewrite <- Hin in *;
  try solve [contradiction].


  (* apply mutable_spec and select on the case with src in dirAcc *)
  eapply H19;
  right; eapply ex_intro with src; rewrite <- HrfSrc in *;
  split; [eauto| rewrite <- H7; simpl].
  
  unfold allocate_dep_ag.
  unfold ag_add_caps_allocate.
  eapply Exe.execute_spec in H2.
  eapply Sys.eq_trans in H2; [|
    eapply execute_proper_1;
      [apply Sys.eq_sym; apply HeqS
        | auto]].

  eapply SemDefns.allocate_preReq_eq_iff in H; [| apply Ref.eq_refl
    | apply Ref.eq_refl
    | apply H2
      ].
  
  case (SemDefns.allocate_preReq_dec a n0 (Exe.execute s' opList)); intros Hallocate; try contradiction; clear Hallocate;
    unfold compose; simpl in *.

  left.

  eapply ag_add_cap_spec; [ apply AG.eq_refl|].
  left;split; [rewrite Edges.source_rewrite; apply Ref.eq_refl|].
  split; [rewrite CC.mkCap_target; rewrite Edges.target_rewrite; apply Ref.eq_refl|].
  rewrite CC.mkCap_rights. rewrite Edges.right_rewrite. eapply in_all_rights.


  (* destroy *)
  (* basically write *)
  (* propagate prereqs *)
  destruct H13 as [HpreReq HopReq].
  unfold Sem.add_option_target in HrfSrc.
  unfold Sem.add_option_target in Hin.
  unfold SemDefns.option_hasRight in HopReq.
  eapply preReq_dirAcc in HpreReq; [destruct HpreReq as [cap [Hcap Hda]]|eauto].

  rewrite Hcap in *; simpl in *.
  unfold CC.hasRight in HopReq.

  (* rewrite src and tgt by cases. *)
  
  eapply RefSetFacts.singleton_iff in Hin; rewrite <- Hin in *.
  (* no destruct *) apply Hda in HopReq.
  (* reduce cases on Hin and HrfSrc *)
  eapply RefSetFacts.singleton_iff in HrfSrc; rewrite <- HrfSrc in *; 

    try solve [ contradiction
      |

  (* use dirAcc_execute_approx to lift from dirAcc to dirAcc_execute *)
  eapply dirAcc_execute_approx in HopReq;
    [
      | apply dirAcc_execute_spec_dirAcc_execute
      | apply H11
      | eapply dirAcc_spec_iff;
        [ eapply Sys.eq_trans;
          [eapply execute_proper_1;
            [apply Sys.eq_sym; apply HeqS
              |apply eq_refl]
            | eapply Exe.execute_spec; eapply H2]
          | eapply AG.eq_refl
          | eapply Hda'0]
      | eapply AGProps.subset_refl
      | eapply Sys.eq_refl];


  (* apply mutable_spec and select on the case with src in dirAcc *)
  eapply H19;
  right; eapply ex_intro with src; rewrite <- HrfSrc in *;
  split; [eauto|];

  (* use dirAcc_op nondecreasing to lift the edge through dirAcc_op *)
  edestruct ag_potTransfer_fn_req_dirAcc_op as [Haddcomm [Hmon Heq]];
  eapply Hmon in HopReq;[|eapply AGProps.subset_refl];
  intuition eauto 2].

Qed.        


Theorem mutable_potAcc_execute_approx_mutated:
  forall s s', Sys.eq s s' ->
    forall E E', RefSet.Subset E E' ->
      forall opList m, mutated_def E s opList m -> 
        forall m', mutable_potAcc_execute opList s' E' m' ->
          RefSet.Subset m m'.
Proof.
  intros.
  generalize (exists_mutable_dirAcc_execute opList s' E); intros [x Hdax].
  eapply RefSetProps.subset_trans.
  eapply mutable_dirAcc_execute_approx_mutated; eauto; try apply RefSet.eq_refl.
  eapply mutable_execute_dirAcc_subset_potAcc;
    [eapply Sys.eq_refl
      | eapply H0
      | eapply Hdax
      | eapply H2].
Qed.


    Theorem obj_existed_impl :
      forall x y, RefSet.eq x y -> forall s t, Sys.eq s t -> obj_existed x s -> obj_existed y t.
    Proof.
      intros.
      intro e; split; intro He;
        [eapply H in He; eapply H1 in He | eapply H; eapply H1];
        (destruct He as [He | He];
          intuition (eapply SC.isLabel_eq; eauto; try apply Ref.eq_refl; try apply ObjectLabel.eq_refl)).
    Qed.

    Theorem Proper_obj_existed: Proper (RefSet.eq ==> Sys.eq ==> iff) obj_existed.
    Proof.
      unfold Proper; unfold respectful; intros; split; intros;
      eapply obj_existed_impl; eauto; try apply RefSet.eq_sym; eauto.
    Qed.

  Theorem obj_existed_potAcc_execute: 
  forall p p_objs, Seq.ag_objs_spec p p_objs ->
    forall Ex s, obj_existed Ex s -> RefSet.Subset p_objs Ex ->
      forall opList Fp, potAcc_execute_spec opList Fp ->
      forall p'_objs, Seq.ag_objs_spec (Fp s p) p'_objs ->
        forall s', Exe.execute_def s opList s' -> 
          forall Ex', obj_existed Ex' s' ->
            RefSet.Subset p'_objs Ex'.
  Proof.
    intros p p_objs Hp_objs Ex s Hex Hsub opList.
    induction opList; intros  Fp Hpexe p'_objs Hp'_objs s' Hexe Ex' Hex'; inversion Hexe; inversion Hpexe.
    (* base *)
    rewrite <- H2 in *.
    eapply obj_existed_eq_iff in Hex;[| apply Sys.eq_sym; apply H| apply Hex']; rewrite Hex. 
    eapply ag_objs_spec_equiv in Hp'_objs; [ | apply Hp_objs| apply AG.eq_refl]; rewrite <- Hp'_objs; auto.
    (* step *)
    rewrite <- H5 in *; simpl in *; unfold compose in *.
    rewrite <- H in *; clear H a.
    eapply obj_existed_potAcc_op.
    4: apply Hp'_objs.
    4: eapply Sys.eq_trans;[apply SemConv.do_op_eq;
      apply Exe.execute_spec; apply H1|apply H3].
    4: apply Hex'.
    apply Seq.ag_objs_spec_ag_objs.
    apply obj_existed_eq_existed_f; apply RefSet.eq_refl.
    
    eapply IHopList.
    apply H7.
    eapply Seq.ag_objs_spec_ag_objs.
    apply H1.
    eapply Proper_obj_existed.
    eapply RefSet.eq_refl.
    eapply Sys.eq_sym; eapply Exe.execute_spec; apply H1.
    eapply obj_existed_eq_existed_f; apply RefSet.eq_refl.
  Qed.

  Theorem ag_objs_spec_subset_existed : forall s ag, dirAcc_spec s ag ->
    forall objs, Seq.ag_objs_spec ag objs ->
      forall Ex, obj_existed Ex s ->
        RefSet.Subset objs Ex.
  Proof.
    intros s ag Hda objs Hobjs Ex Hex x Hin.
    eapply Hex; left.
    unfold SC.is_alive.
    unfold SC.is_label.
    unfold SC.getLabel.
    unfold SC.getObjTuple.

    eapply Hobjs in Hin; destruct Hin as [obj [rgt [Hin | Hin]]]; eapply Hda in Hin;
    destruct_dirAcc Hin s'' HeqS src_ref src lbl srcType srcSched HmapS 
    src' lbl' srcType' srcSched' HeqP Halive ind cap HmapSrc'
    cap_obj cap_lbl cap_type cap_sched HmapScap cap_obj' cap_lbl' cap_type' cap_sched' 
    HeqPcap HaliveCap rgt' HinR HeqEdge;

    [destructEdgeEq HeqEdge (Edges.mkEdge x obj rgt) HeqEdgeS HeqEdgeT HeqEdgeR |
    destructEdgeEq HeqEdge (Edges.mkEdge obj x rgt) HeqEdgeS HeqEdgeT HeqEdgeR];
      unfold Ref.eq in HeqEdgeS; unfold Ref.eq in HeqEdgeT;
        rewrite HeqEdgeS in *; rewrite HeqEdgeT in *;
    
    apply Sys_Facts.find_mapsto_iff in HmapS;
    apply Sys_Facts.find_mapsto_iff in HmapScap;
    [generalize (Sys_MapEquiv.find_eq _ _ _ _ (Ref.eq_refl x) HeqS)
      | generalize (Sys_MapEquiv.find_eq _ _ _ _ (Ref.eq_refl x) HeqS) ]; intros Hfind;
    [rewrite HmapS in Hfind | rewrite HmapScap in Hfind] ; simpl in *;


    destruct_tuple HeqPcap HeqSrcCap HeqLblCap HeqTypCap HeqScCap; simpl in *;
      destruct_tuple HeqP HeqSrc HeqLbl HeqTyp HeqSc; simpl in *;
    rewrite_case_option (Sys.MapS.find x s) tuple Hcase; try contradiction;

    destruct_tuple tuple obj'' lbl'' typ'' sch''; simpl in *;
    destruct Hfind as [[[_ Hlbl'] _]_];
    rewrite Hlbl';
    [rewrite HeqLbl|rewrite HeqLblCap];
    eapply ObjectLabel.eq_sym; auto.
  Qed.

  Theorem mutable_potAcc_execute_existed: 
    forall Ex s, obj_existed Ex s -> 
      forall E, RefSet.Subset E Ex ->
        forall opList m, mutable_potAcc_execute opList s E m ->
          forall s', Exe.execute_def s opList s' ->
            forall Ex', obj_existed Ex' s' ->
              RefSet.Subset m Ex'.
  Proof.
    intros Ex s Hex E He opList.
    induction opList; intros  m Hm s' Hexe Ex' Hex'.
    (* base *)
    inversion Hexe. clear s'0 H1.
    inversion Hm. clear H7 H8 H9.
    eapply obj_existed_eq_iff in Hex';
      [
        | apply H
        | apply Hex ].
    rewrite <- Hex'.
    inversion H2. rewrite <- H7 in *. simpl in *.

    (* generalize potAcc and objs *)
    revert H5; generalize (Seq.potAcc_potAcc_fun i); generalize (Seq.potAcc_fun i); intros p Hpa H5.
    generalize (Seq.ag_objs_spec_ag_objs i); generalize (Seq.ag_objs i); intros objs Hobjs.

    eapply mutable_subset_objs;
      [eapply ag_objs_spec_potTransfer; [apply Hobjs | apply Hpa]
        | eapply ag_objs_spec_subset_existed; eauto 1
        | apply He
        | apply H5
      ].

    (* step *)
    rename a into op.
    inversion Hexe. clear op0 H tail H0 s'' H2 Hexe.
    inversion Hm. clear op0 H opList0 H0 s0 H12 E0 H13 M' H14 Hm.
    rename Ex' into Ex''; rename Hex' into Hex'';
    rename s' into s''; rename s'0 into s';
    rename H1 into Hexe; rename H3 into Hs'';
    rename H2 into Hdax; rename H4 into Hindexed;
      rename H5 into Hpax; rename H6 into Happrox;
        rename H7 into Hda; rename H8 into HM;
          rename H9 into Hdax'; rename H10 into Hpax';
            rename H11 into Happrox';
              rename H15 into Hm.

    (* generalize obj_existd on s' *)
    generalize (obj_existed_eq_existed_f (existed_f s') s'); generalize (existed_f s'); intros Ex' [_ Heq];
    generalize (Heq (RefSet.eq_refl _)); clear Heq; intros Hex'.

    (* invert Hpax' and eliminate Ftx *)
    inversion Hpax'. rewrite <- H0 in *. clear op0 H op_list H1 H0. simpl in *.
    eapply Hindexed in H2; [| apply eq_refl].
    rewrite <- H2 in Happrox; [|eauto].
    rewrite <- H2 in Hpax; auto;
    clear Ftx H2.

    (* invert Hdax' and elminate Fdx *)

    inversion Hdax'. rewrite <- H0 in *. clear op0 H op_list H1 H0. simpl in *.
    eapply indexed_dirAcc_execute_spec  in H2; [| apply eq_refl].
    generalize (H2 _ Hdax); clear H2; intros Hdaxeq.
    rewrite <- Hdaxeq in Happrox.
    rewrite <- Hdaxeq in Hdax.
    clear Fdx Hdaxeq.
    rename Fp0 into Fdx; rename Fp into Fpx.
    clear Ftx' Fdx' Hdax'.

    unfold compose in *.

    generalize (IHopList _ HM _ Hexe _ Hex'); intros IH; clear IHopList.

    (* lay out all 3 sets of objs *)
    set (p := (Seq.potAcc_fun i)).
    generalize (Seq.ag_objs_spec_ag_objs i); generalize (Seq.ag_objs i); intros objs Hobjs.
    generalize Hobjs; intros Hobjs'.
    eapply ag_objs_spec_potTransfer with (B:=p) in Hobjs; [ | apply Seq.potAcc_potAcc_fun].
    set (p' := (Fpx s (Seq.potAcc_fun i))).
    generalize (Seq.ag_objs_spec_ag_objs p'); generalize (Seq.ag_objs p'); intros p'_objs Hp'_objs.
    set (p'' := (potAcc_op op (Exe.execute s opList) p' )).
    generalize (Seq.ag_objs_spec_ag_objs p''); generalize (Seq.ag_objs p''); intros p''_objs Hp''_objs.
    
    (* reduce the problem over mutable *)
    eapply mutable_subset_objs.
    4: apply Hm.
    3: eapply RefSetProps.subset_trans;
      [ apply IH
        | eapply remains_existed_op; [apply Hex'| apply Hs'' | apply Hex'']
      ].
    apply Hp''_objs.
    
    (* solve the step *)
    eapply obj_existed_potAcc_op.
    4: apply Hp''_objs.
    5: apply Hex''.

    2: eapply Proper_obj_existed; [ apply RefSet.eq_refl| eapply Exe.execute_spec; apply Hexe | apply Hex'].
    apply Hp'_objs.
    2: eapply Sys.eq_trans; [ eapply SemConv.do_op_eq;
      eapply Exe.execute_spec; apply Hexe | eapply Hs''].

    (* solve the remainder *)
    eapply obj_existed_potAcc_execute.
    5: apply Hp'_objs.
    2: apply Hex.
    5: apply Hex'.
    4: apply Hexe.
    3: apply Hpax.
    apply Hobjs.
    eapply ag_objs_spec_subset_existed.
    apply Hda.
    apply Hobjs'.
    apply Hex.
    Qed.


Theorem mutable_potAcc_execute_approx:
forall opList S E Mx, mutable_potAcc_execute opList S E Mx ->
forall D, dirAcc_spec S D ->
forall P, Seq.potAcc D P ->
forall Ex, obj_existed Ex S ->
RefSet.Subset E Ex ->
forall M, mutable_spec P E M ->
(RefSet.Subset (RefSet.inter Mx Ex) M).
Proof.
  intros opList.
  induction opList; intros S E Mx Hmx (* had inducted here *) D Hda P Hpa Ex Hex He M2 Hm2.
  inversion Hmx;
    rename H1 into Hpax; inversion Hpax as [Hpax1 Hpax2 | ]. 
  try rewrite <- Hpax2 in *; simpl in *.
  
  eapply RefSetProps.subset_trans.
  eapply RefSetProps.inter_subset_1.

  eapply mutable_spec_subset.
  3: apply Hm2.
  eapply RefSetProps.subset_refl.
  eapply AGProps.subset_equal.

  eapply dirAcc_spec_eq in H3.
  2: apply Sys.eq_refl.
  2: apply Hda.

  eapply potAcc_eq_iff in Hpa.
  2: apply H3.
  2: apply AG.eq_refl.
  eapply Seq.potAcc_eq_potAcc_fun in Hpa.
  eapply AG.eq_sym; eauto.

  auto.

(* step *)
  rename IHopList into IH.

  (* we need a very principled approach here, as things get complicated later on.
     clear all useless values, and name all hypotheses *)
  
  rename a into op.
  (* invert Hmx *)
  inversion Hmx.
  clear op0 H opList0 H0 M' H12 E0 H11 s H10 Hmx.
  rename H1 into Hdax; rename H2 into Hindexed;
    rename H3 into Hpax; rename H4 into Happrox;
      rename H5 into HdaI; rename H6 into HM;
        rename H7 into Hdax'; rename H8 into Hpax';
          rename H9 into Happrox'; rename H13 into HMx.
  (* invert Hpax', equate through indexed *)
  inversion Hpax';
  rewrite <- H0 in *;
  clear op0 H op_list H1 H0 Hpax';
  rename H2 into Hpax';
  generalize Hpax; let HFpEq := fresh "HFpEq" in intros HFpEq;
  eapply Hindexed in Hpax'; [eapply Hpax' in HFpEq; rewrite <- HFpEq in *| apply eq_refl];
  clear Hpax' HFpEq Ftx' Ftx.
  (* invert Hdax', equate through indexed *)
  inversion Hdax'.
  rewrite <- H0 in *.
  clear op0 H op_list H1 H0 Hdax'.
  rename H2 into Hdax'.
  generalize Hdax; let HFdxEq := fresh "HFdxEq" in intros HFdxEq;
  eapply indexed_dirAcc_execute_spec in Hdax'; [eapply Hdax' in HFdxEq; rewrite HFdxEq in *| apply eq_refl];
  clear Hdax' HFdxEq Fdx' Fp0.

  unfold compose in *.



  (* cases ! *)

  Ltac solve_inversion_step Hpax Hpax' Hindexed Hdax Hdax' Happrox HMx HM IH HM' Hda Hpa Hex He Hm2:=

  generalize Hpax; let HFpEq := fresh "HFpEq" in intros HFpEq;
  eapply Hindexed in Hpax'; [eapply Hpax' in HFpEq; rewrite HFpEq in *| apply eq_refl];
  (* clear Hpax' HFpEq Ftx; *)
  generalize Hdax; let HFdxEq := fresh "HFdxEq" in intros HFdxEq;
  eapply indexed_dirAcc_execute_spec in Hdax'; [eapply Hdax' in HFdxEq; rewrite HFdxEq in *| apply eq_refl];
  (* clear Hdax' HFdxEq Fdx0; *)

  destruct Happrox as [Hgen [Hmon [ Hequiv [HdaProper HpaProper]]]];
  eapply mutable_maximal_subset in HMx;
    [
      | eapply potAcc_execute_spec_potAcc;
        [ eapply Seq.maxTransfer_maxPotTransfer; eapply Seq.potAcc_potAcc_fun
          | apply Hpax]
      | apply HM 
      | eapply AGProps.subset_equal; eapply HpaProper; [ apply Sys.eq_refl |
        eapply Proper_potAcc_fun; eapply dirAcc_spec_eq; eauto 1; try apply Sys.eq_refl]
    ];

  intros x HinX;
  eapply RefSetFacts.inter_iff in HinX; destruct HinX as [HinXM' HinXEx];
  eapply HMx in HinXM';
  eapply IH;
    [ eapply HM'
      | apply Hda
      | apply Hpa
      | apply Hex
      | apply He
      | apply Hm2
      | eapply RefSetFacts.inter_iff; split; auto
    ].

  destruct op;
    try solve [
      inversion HM;
        [rename H5 into HopList;
          rewrite HopList in *; clear HopList;
            clear s H6 E0 H7 M0 H8 H0 H2; rename HM into HM';
              rename H into Hdax'; rename H1 into Hpax'; rename H3 into HdaI0; rename H4 into HM
          | rename H9 into HopList;
            rewrite <- HopList in *; clear HopList;
              clear s H10 E0 H11 M' H12 H0 H2 H H1 H7; rename HM into HM';
                rename H5 into Hdax'; rename H6 into Hpax'; 
                  rename H3 into HdaI0; rename H4 into HM0; rename H8 into HM
        ]; solve_inversion_step Hpax Hpax' Hindexed Hdax Hdax' Happrox HMx HM IH HM' Hda Hpa Hex He Hm2].
  
(* only allocate remains *)

(* reduce to endow to build a projction *)

simpl in *. unfold endow_dep in *.
revert HMx.

case (SemDefns.allocate_preReq_dec t t0 (Exe.execute S opList)); intros HpreReq HMx;
    try solve [
      inversion HM;
        [rename H5 into HopList;
          rewrite HopList in *; clear HopList;
            clear s H6 E0 H7 M0 H8 H0 H2; rename HM into HM';
              rename H into Hdax'; rename H1 into Hpax'; rename H3 into HdaI0; rename H4 into HM
          | rename H9 into HopList;
            rewrite <- HopList in *; clear HopList;
              clear s H10 E0 H11 M' H12 H0 H2 H H1 H7; rename HM into HM';
                rename H5 into Hdax'; rename H6 into Hpax'; 
                  rename H3 into HdaI0; rename H4 into HM0; rename H8 into HM
        ]; solve_inversion_step Hpax Hpax' Hindexed Hdax Hdax' Happrox HMx HM IH HM' Hda Hpa Hex He Hm2].


(* we still need to invert on HM to solve, as mutable_project requires a mutable_spec input *)
rename t0 into n; rename t into a.
 inversion HM;
  [rename H5 into HopList;
    rewrite HopList in *; 
      clear s H6 E0 H7 M0 H8 H0 H2; rename HM into HM';
        rename H into Hdax'; rename H1 into Hpax'; rename H3 into HdaI0; rename H4 into HM
    | rename H9 into HopList;
      rewrite HopList in *; 
        rename HM into HM';
          rename H5 into Hdax'; rename H6 into Hpax'; 
            rename H3 into HdaI0; rename H4 into HM0; rename H8 into HM]. 
  (* nil case *)
 
  generalize Hpax; let HFpEq := fresh "HFpEq" in intros HFpEq;
  eapply Hindexed in Hpax'; [eapply Hpax' in HFpEq; rewrite HFpEq in *| apply eq_refl];
  clear Hpax' HFpEq.

  generalize Hdax; let HFpEq := fresh "HFpEq" in intros HFpEq;
  eapply indexed_dirAcc_execute_spec in Hdax'; [eapply Hdax' in HFpEq; rewrite HFpEq in *| apply eq_refl];
  clear Hdax' HFpEq.
  
  destruct Happrox as [Hgen [Hmon [ Hequiv [HdaProper HpaProper]]]].
  destruct Happrox' as [Hgen' [Hmon' [ Hequiv' [HdaProper' HpaProper']]]].
  (* reusable ag_objs_spec *)
  generalize (Seq.ag_objs_spec_ag_objs (Fp S (Seq.potAcc_fun i0)));
    generalize (Seq.ag_objs (Fp S (Seq.potAcc_fun i0))); intros objs Hobjs.

  (* generate a few structures *)
  (* s' *)
  assert (exists s', Exe.execute_def S opList s') as [s' Hexe'].
  eapply ex_intro; eapply Exe.execute_spec; eapply Sys.eq_refl.
  (* Ex' *)
  assert (exists Ex', obj_existed Ex' s') as [Ex' Hex'].
  eapply ex_intro; eapply obj_existed_eq_existed_f; eapply RefSet.eq_refl.
  (* D [=] i [=] i0' *)
  eapply dirAcc_spec_eq in Hda; [ rename Hda into HeqI0; rename HdaI0 into Hda | apply Sys.eq_refl | apply HdaI0].
  eapply dirAcc_spec_eq in HdaI; [  | apply Sys.eq_refl | apply Hda].
  (* allocate prereqs in s' *)
  destruct HpreReq as [[Halive Hactive] Hunborn].
  unfold SC.is_alive in *; unfold SC.is_unborn in *.
  eapply SC.isLabel_eq in Halive;
    [ | apply Ref.eq_refl| apply ObjectLabel.eq_refl | apply Exe.execute_spec; apply Hexe'].
  eapply SC.isLabel_eq in Hunborn;
    [ | apply Ref.eq_refl| apply ObjectLabel.eq_refl | apply Exe.execute_spec; apply Hexe'].

 (* ~ In n Ex' *)
  assert (~ RefSet.In n Ex') as HninN.
  intros Hnot.
  eapply Hex' in Hnot.
  eapply SC.is_label_iff_getLabel in Hunborn.
  unfold SC.is_alive in Hnot; unfold SC.is_dead in Hnot.
  destruct Hnot  as [Hnot | Hnot];
    eapply SC.is_label_iff_getLabel in Hnot;
      rewrite Hunborn in Hnot; discriminate Hnot.



  (* generalize obj_existed_potAcc_execute *)
  
  assert (RefSet.Subset objs Ex') as Hobjs'.

  eapply obj_existed_potAcc_execute;
    [ eapply ag_objs_spec_potTransfer; 
      [ apply Seq.ag_objs_spec_ag_objs
        | eapply Seq.potAcc_potAcc_fun
      ]
      | apply Hex
      | eapply ag_objs_spec_subset_existed;
        [ apply Hda
          | apply Seq.ag_objs_spec_ag_objs
          | apply Hex
        ]
      | apply Hpax
      | apply Hobjs
      | apply Hexe'
      | apply Hex'
    ].

  (* change potAcc over i0 *)
  eapply potAcc_eq_iff in Hpa; [ | apply AG.eq_sym; apply HeqI0 | apply AG.eq_refl].

  generalize (IH _ _ _ HM' _ Hda _ Hpa _ Hex He _ Hm2); intros IH'.

  eapply mutable_project in HMx;
    [ intros x HinX;
      eapply RefSetFacts.inter_iff in HinX; destruct HinX as [HinXM' HinXEx];
        let IH' := fresh "IH'" in generalize (IH _ _ _ HM' _ Hda _ Hpa _ Hex He _ Hm2 x); intros IH';
          apply IH'; clear IH';
            eapply RefSetFacts.inter_iff; split; auto;
              eapply HMx;
                eapply RefSetFacts.inter_iff; split; auto
      |  eapply potAcc_execute_spec_potAcc;
        [ eapply Seq.maxTransfer_maxPotTransfer; eapply Seq.potAcc_potAcc_fun
          | apply Hpax]
      | eapply Hobjs
      |
      |
      |
      |
      | eapply AG_project_endow;
        [ eapply maxTransfer_potAcc_refl;
          eapply potAcc_execute_spec_potAcc;
            [eapply Seq.maxTransfer_maxPotTransfer; eapply Seq.potAcc_potAcc_fun
              |eapply Hpax]
          | apply Hobjs
          | (* delay *)
          | eapply Proper_insert; [apply Ref.eq_refl|apply Ref.eq_refl
            | eapply HpaProper; [apply Sys.eq_refl
              | eapply Proper_potAcc_fun; apply HdaI]]
          | eapply Seq.potAcc_potAcc_fun
        ]; intros Hnot; apply Hobjs' in Hnot; contradiction
      | apply HM
    ].

  (* tail of first subgoal *)
  eapply remains_existed;
  [ apply Hex
  | apply Hexe'
  | apply Hex'
  | auto ].

  (* already verified objs exist *)
  auto.

  eapply RefSetProps.subset_trans; [ apply He|
    eapply remains_existed;
      [apply Hex
        | apply Hexe'
        | apply Hex'
      ]
  ].
  
  (* alive a *)
  eapply Hex'; left; auto.

  (* also previously verified *)
  auto.


  (* cons case *)

  clear s H10 E0 H11 M' H12 H0 H2 H H1 H7.


  generalize Hpax; let HFpEq := fresh "HFpEq" in intros HFpEq;
  eapply Hindexed in Hpax'; [eapply Hpax' in HFpEq; rewrite HFpEq in *| apply eq_refl];
  clear Hpax' HFpEq.

  generalize Hdax; let HFpEq := fresh "HFpEq" in intros HFpEq;
  eapply indexed_dirAcc_execute_spec in Hdax'; [eapply Hdax' in HFpEq; rewrite HFpEq in *| apply eq_refl];
  clear Hdax' HFpEq.
  
  destruct Happrox as [Hgen [Hmon [ Hequiv [HdaProper HpaProper]]]].
  destruct Happrox' as [Hgen' [Hmon' [ Hequiv' [HdaProper' HpaProper']]]].
  (* reusable ag_objs_spec *)
  generalize (Seq.ag_objs_spec_ag_objs (Fp S (Seq.potAcc_fun i0)));
    generalize (Seq.ag_objs (Fp S (Seq.potAcc_fun i0))); intros objs Hobjs.

  (* generate a few structures *)
  (* s' *)
  assert (exists s', Exe.execute_def S opList s') as [s' Hexe'].
  eapply ex_intro; eapply Exe.execute_spec; eapply Sys.eq_refl.
  (* Ex' *)
  assert (exists Ex', obj_existed Ex' s') as [Ex' Hex'].
  eapply ex_intro; eapply obj_existed_eq_existed_f; eapply RefSet.eq_refl.
  (* D [=] i [=] i0' *)
  eapply dirAcc_spec_eq in Hda; [ rename Hda into HeqI0; rename HdaI0 into Hda | apply Sys.eq_refl | apply HdaI0].
  eapply dirAcc_spec_eq in HdaI; [  | apply Sys.eq_refl | apply Hda].
  (* allocate prereqs in s' *)
  destruct HpreReq as [[Halive Hactive] Hunborn].
  unfold SC.is_alive in *; unfold SC.is_unborn in *.
  eapply SC.isLabel_eq in Halive;
    [ | apply Ref.eq_refl| apply ObjectLabel.eq_refl | apply Exe.execute_spec; apply Hexe'].
  eapply SC.isLabel_eq in Hunborn;
    [ | apply Ref.eq_refl| apply ObjectLabel.eq_refl | apply Exe.execute_spec; apply Hexe'].

 (* ~ In n Ex' *)
  assert (~ RefSet.In n Ex') as HninN.
  intros Hnot.
  eapply Hex' in Hnot.
  eapply SC.is_label_iff_getLabel in Hunborn.
  unfold SC.is_alive in Hnot; unfold SC.is_dead in Hnot.
  destruct Hnot  as [Hnot | Hnot];
    eapply SC.is_label_iff_getLabel in Hnot;
      rewrite Hunborn in Hnot; discriminate Hnot.



  (* generalize obj_existed_potAcc_execute *)
  
  assert (RefSet.Subset objs Ex') as Hobjs'.

  eapply obj_existed_potAcc_execute;
    [ eapply ag_objs_spec_potTransfer; 
      [ apply Seq.ag_objs_spec_ag_objs
        | eapply Seq.potAcc_potAcc_fun
      ]
      | apply Hex
      | eapply ag_objs_spec_subset_existed;
        [ apply Hda
          | apply Seq.ag_objs_spec_ag_objs
          | apply Hex
        ]
      | apply Hpax
      | apply Hobjs
      | apply Hexe'
      | apply Hex'
    ].

  (* change potAcc over i0 *)
  eapply potAcc_eq_iff in Hpa; [ | apply AG.eq_sym; apply HeqI0 | apply AG.eq_refl].

  generalize (exists_dirAcc_spec s'); intros [d' Hda'].
  generalize (Seq.exists_potAcc d'); intros [p' Hpa'].

  generalize (IH _ _ _ HM' _ Hda _ Hpa _ Hex He _ Hm2); intros IH'.

  intros x HinX.

  eapply mutable_project with (N:=Ex') in HMx;
    [ eapply RefSetFacts.inter_iff in HinX; destruct HinX as [HinXM' HinXEx];
        apply IH';
          eapply RefSetFacts.inter_iff; split; auto 1;
            apply HMx;
              apply RefSetFacts.inter_iff; split; auto;
                eapply remains_existed;
                  [ apply Hex
                    | apply Hexe'
                    | apply Hex'
                    | auto ]
      | eapply potAcc_execute_spec_potAcc;
        [ eapply Seq.maxTransfer_maxPotTransfer; eapply Seq.potAcc_potAcc_fun
          | apply Hpax]
      | eapply Hobjs
      | auto
      |
        (* alive a *)
      | eapply Hex'; left; apply Halive
        (* also previously verified *)
      | apply HninN
      | eapply AG_project_endow;
        [ eapply maxTransfer_potAcc_refl;
          eapply potAcc_execute_spec_potAcc;
            [eapply Seq.maxTransfer_maxPotTransfer; eapply Seq.potAcc_potAcc_fun
              |eapply Hpax]
          | apply Hobjs
          | (* delay *)
          | eapply Proper_insert; [apply Ref.eq_refl|apply Ref.eq_refl
            | eapply HpaProper; [apply Sys.eq_refl
              | eapply Proper_potAcc_fun; apply HdaI]]
          | eapply Seq.potAcc_potAcc_fun
        ]; intros Hnot; apply Hobjs' in Hnot; contradiction
      | apply HM].

idtac.

rename opList0 into opList'.

assert (exists s'', Exe.execute_def S opList' s'') as [s'' Hexe''].
eapply ex_intro; eapply Exe.execute_spec; eapply Sys.eq_refl.
  
  assert (exists Ex'', obj_existed Ex'' s'') as [Ex'' Hex''].
  eapply ex_intro; eapply obj_existed_eq_existed_f; eapply RefSet.eq_refl.
  
  
  eapply RefSetProps.subset_trans.

eapply mutable_potAcc_execute_existed.
apply Hex.
apply He.
apply HM0.
apply Hexe''.
apply Hex''.

eapply remains_existed_op.
eapply Hex''.
2:eapply Hex'.

eapply Exe.execute_spec in Hexe''.
eapply Sys.eq_trans.
eapply SemConv.do_op_eq.
eapply Sys.eq_sym; apply Hexe''.

eapply Exe.execute_spec in Hexe'.
rewrite <- HopList in Hexe'; simpl in *.
apply Hexe'.

Qed.


(* I believe this is the last theorem for this module *)


Theorem mutable_approx_mutated:
forall opList S E m, mutated_def E S opList m ->
forall D, dirAcc_spec S D ->
forall P, Seq.potAcc D P ->
forall Ex, obj_existed Ex S ->
RefSet.Subset E Ex ->
forall M, mutable_spec P E M ->
(RefSet.Subset (RefSet.inter m Ex) M).
Proof.
  intros opList S E m Hm D Hda P Hpa Ex Hex Hsub M HM.
 
(*
 Theorem mutable_potAcc_execute_approx:
forall opList S E Mx, mutable_potAcc_execute opList S E Mx ->
forall D, dirAcc_spec S D ->
forall P, Seq.potAcc D P ->
forall Ex, obj_existed Ex S ->
RefSet.Subset E Ex ->
forall M, mutable_spec P E M ->
(RefSet.Subset (RefSet.inter Mx Ex) M).

Theorem mutable_potAcc_execute_approx_mutated:
  forall s s', Sys.eq s s' ->
    forall E E', RefSet.Subset E E' ->
      forall opList m, mutated_def E s opList m -> 
        forall m', mutable_potAcc_execute opList s' E' m' ->
          RefSet.Subset m m'.

Theorem exists_mutable_potAcc_execute: forall opList s E, exists m, mutable_potAcc_execute opList s E m.
*)
  generalize (exists_mutable_potAcc_execute opList S E); intros [Mx HMx].
  generalize (mutable_potAcc_execute_approx_mutated _ _ (Sys.eq_refl _) _ _ (@RefSetProps.subset_refl _) _ _ Hm _ HMx); intros Hsubx.

  intros x Hin.
  eapply RefSetFacts.inter_iff in Hin; destruct Hin as [Hinm HinEx].
  eapply Hsubx in Hinm.

  eapply mutable_potAcc_execute_approx.
  eapply HMx.
  apply Hda.
  apply Hpa.
  apply Hex.
  apply Hsub.
  apply HM.

  apply RefSetFacts.inter_iff; intuition.
Qed.

End MakeMutableSubset.