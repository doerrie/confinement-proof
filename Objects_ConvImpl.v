(* type_remove *)
Require Import Objects_Conv.
Require Import Objects.
Require Import Indices.
Require Import Capabilities.
Require Import OrdFMapEquiv.
Require Import OptionMap2.
Require Import FMapInterface2.
Require FMapFoldEqual.
Require Import OrderedTypeEquiv.
Require Import FMapExists.
Require Import References.
Require Import FMapFacts2.
Require Import FMapInterface2.

Module MakeObjConv (Ref:ReferenceType) (Cap:CapabilityType Ref) (Ind: IndexType) (Obj:ObjectType Ref Cap Ind) : ObjectConv Ref Cap Ind Obj.
  
  
  Module Obj_OrdProps := OrdProperties_fun Ind Obj.MapS.
  Module Obj_Props := Obj_OrdProps.P.
  Module Obj_Facts := Obj_Props.F.
  Module Obj_MapEquiv := MakeEquiv_fun Ind Obj.MapS Cap Obj.
  Module Obj_Exists := MakeExists_fun Ind Obj.MapS Cap Obj.
  Module Obj_Equiv := OT_Equiv Obj.
  Module Obj_FoldEqual := FMapFoldEqual.Make_fun Ind Obj.MapS Cap Obj.
  
  Definition ObjEQ := Obj_Equiv.Equiv.
  
  Module Ind_Equiv := OT_Equiv Ind.
  Definition IndEQ := Ind_Equiv.Equiv.


    Definition getCap (i:Ind.t) (o:Obj.t) : option Cap.t := Obj.MapS.find i o.

    Theorem getCap_eq: forall i i' o o',
      Ind.eq i i' ->
      Obj.eq o o' ->
      option_map_eq Cap.eq (getCap i o) (getCap i' o').
    Proof.
      intros.
      unfold option_map_eq.
      unfold option_map2.
      apply Obj_MapEquiv.find_eq; auto.
    Qed.

    Definition addCap (i:Ind.t) (c:Cap.t) (o:Obj.t) : Obj.t := Obj.MapS.add i c o.

    Definition rmCap (i:Ind.t) (o:Obj.t) : Obj.t := Obj.MapS.remove i o.

    Theorem addCap_eq : forall i i' c c' o o',
      Ind.eq i i' ->
      Cap.eq c c' ->
      Obj.eq o o' ->
      Obj.eq (addCap i c o) (addCap i' c' o').
    Proof.
      intros.
      unfold addCap.
      apply Obj.eq_1.
      unfold Obj.MapS.Equivb.
      unfold Obj.MapS.Equiv.
      unfold Cmp.
      apply Obj.eq_2 in H1.
      unfold Obj.MapS.Equivb in H1.
      unfold Obj.MapS.Equiv in H1.
      unfold Cmp in H1.
      destruct H1.
      split; intros. 
      split; intros.
    (*case 1 *)
      eapply Obj_Facts.add_in_iff.
      apply Obj_Facts.add_in_iff in H3.
      destruct H3.
    (* case 1.1 *)
      left.
      apply Ind.eq_trans with i; auto.
    (* case 1.2 *)
      right.
      eapply H1; assumption.
    (* case 2, identical to case 1 *)
      eapply Obj_Facts.add_in_iff.
      apply Obj_Facts.add_in_iff in H3.
      destruct H3.
    (* case 2.1 *)
      left.
      apply Ind.eq_trans with i'; auto.
    (* case 2.2 *)
      right.
      eapply H1; assumption.
    (* case 3 *)
    (* need to show Cap.eq e e' *)
      apply Obj_Facts.add_mapsto_iff in H3.
      apply Obj_Facts.add_mapsto_iff in H4.
      destruct H3; destruct H4; destruct H3; destruct H4.
    (* case 3.1 *)
      unfold Obj.cmp in *.
      generalize (Cap.compare e e'); intros CMP.
      destruct CMP as [CMP|CMP|CMP]; rewrite H5 in H0; rewrite H6 in H0.
      apply Cap.lt_not_eq in CMP; contradiction.
      trivial. 
      apply Cap.lt_not_eq in CMP; apply Cap.eq_sym in H0; contradiction.
    (* case 3.2 *)
      unfold Obj.cmp in *.
      generalize (Cap.compare e e'); intros CMP.
      apply Ind.eq_sym in H.
      apply Ind.eq_trans with (x:= i') (y:= i) (z:= k) in H; auto.
    (* case 3.3 *)
      unfold Obj.cmp in *.
      generalize (Cap.compare e e'); intros CMP.
      apply Ind.eq_trans with (x:= i) (y:= i') (z:= k) in H; auto.
    (* case 3.4 *)
      apply H2 with k; auto.
    Qed.

    Theorem removeCap_eq : forall i i' o o',
      Ind.eq i i' ->
      Obj.eq o o' ->
      Obj.eq (rmCap i o) (rmCap i' o').
    Proof.
      intros.
      unfold rmCap.
      apply Obj.eq_1.
      unfold Obj.MapS.Equivb.
      unfold Obj.MapS.Equiv.
      unfold Cmp.
      split; intros. 
      split; intros.
    (*case 1 *)
      eapply Obj_Facts.remove_in_iff.
      eapply Obj_Facts.remove_in_iff in H1.
      destruct H1.
      split.
    (* case 1.1 *)
      intro.
      apply Ind.eq_trans with (x:=i) (y:=i') (z:=k) in H3; try contradiction; auto.
    (* case 1.2 *)
      eapply Obj.eq_2; [apply Obj.eq_sym; apply H0 | auto].
    (* case 2, similar to case 1 *)
      eapply Obj_Facts.remove_in_iff.
      eapply Obj_Facts.remove_in_iff in H1.
      destruct H1.
      split.
    (* case 2.1 *)
      intro.
      apply Ind.eq_sym in H; apply Ind.eq_trans with (x:=i') (y:=i) (z:=k) in H3; try contradiction; auto.
    (* case 2.2 *)
      eapply Obj.eq_2; [apply H0 |auto].
    (* case 3 *)
      apply Obj.eq_2 in H0.
      unfold Obj.MapS.Equivb in H0.
      unfold Obj.MapS.Equiv in H0.
      unfold Cmp in H0.
      destruct H0.
    (* need to show Cap.eq e e' *)
      apply Obj_Facts.remove_mapsto_iff in H1.
      apply Obj_Facts.remove_mapsto_iff in H2.
      destruct H1; destruct H2.
      apply H3 with k; auto.
    Qed.

    Definition rmCapsByTarget t obj :=
      Obj.MapS.fold (fun ind cap obj' => if Ref.eq_dec (Cap.target cap) t then obj' else addCap ind cap obj') obj (Obj.MapS.empty _).

    Theorem addCap_transpose_neqkey: forall k k' e e' a,
      ~ Ind.eq k k' ->
      Obj.eq (addCap k e (addCap k' e' a)) (addCap k' e' (addCap k e a)).
    Proof.
      intros.
      unfold addCap.
      apply Obj.eq_1.
      unfold Obj.MapS.Equivb.
      unfold Obj.MapS.Equiv.
      split; intros.
      
      (* case In <-> In *)
      split; intros;
      (eapply Obj_Facts.add_in_iff;
       destruct H0; eapply Obj_Facts.add_mapsto_iff in H0; destruct H0; destruct H0;
       [ right; rewrite H0; eapply Obj_Facts.add_in_iff; intuition eauto
       | eapply Obj_Facts.add_mapsto_iff in H1; destruct H1; destruct H1;
         [ auto
         | right; eapply Obj_Facts.add_in_iff; right; eapply ex_intro; eapply H2]]).

      (* case Cmp Obj.cmp *)
      unfold Cmp; unfold Obj.cmp.
      apply Obj_Facts.add_mapsto_iff in H0; destruct H0 as [[HeqK HeqE]|[HneqK Hmap]];
        apply Obj_Facts.add_mapsto_iff in H1; destruct H1 as [[HeqK' HeqE']|[HneqK' Hmap']];
          try (apply Obj_Facts.add_mapsto_iff in Hmap'; destruct Hmap' as [[HeqK'' HeqE'']|[HneqK'' Hmap'']]);
            try (apply Obj_Facts.add_mapsto_iff in Hmap; destruct Hmap as [[HeqK''' HeqE''']|[HneqK''' Hmap''']]);
              destruct (Cap.compare e0 e'0); eauto;
                apply Cap.lt_not_eq in l; try rewrite <- HeqE in l; try rewrite HeqE'' in l; 
                  try rewrite <- HeqE''' in l; try rewrite HeqE' in l; try rewrite (Obj_Facts.MapsTo_fun Hmap'' Hmap''') in l; 
                    eauto.
    Qed.

    Theorem rmCapsByTarget_eq : forall r r' o o',
      Ref.eq r r' ->
      Obj.eq o o' ->
      Obj.eq (rmCapsByTarget r o) (rmCapsByTarget r' o').
    Proof.
      intros r r' o o' Hr.
      unfold rmCapsByTarget.
      intros.
      apply Obj_FoldEqual.fold_foldEqual with (m := o) (m' := o'); auto.
    (* Equivalence *)
      split; unfold Reflexive; unfold Symmetric; unfold Transitive; intros;
        try apply Obj.eq_refl; auto; try apply Obj.eq_sym; auto; try eapply Obj.eq_trans; apply Obj.eq_sym; eauto.
    (* eq empty *)
      apply Obj.eq_refl.
    (* FoldEqual *)
      unfold Obj_FoldEqual.foldEqual; intros.
    (* case on eq_dec *)
      case (Ref.eq_dec (Cap.target v) r); intros.
      assert (Ref.eq (Cap.target v') r');
        [apply Cap.target_eq in H2;
          eapply Ref.eq_trans; 
            [apply Ref.eq_sym; apply H2
              | eapply Ref.eq_trans; [apply e| apply Hr]] |].
      case (Ref.eq_dec (Cap.target v') r'); intros; auto; try contradiction.
      assert (~Ref.eq (Cap.target v') r');
        [intro n'; apply n; clear n; rename n' into n;
          apply Cap.target_eq in H2;
            eapply Ref.eq_trans;
              [apply H2 | eapply Ref.eq_trans; [apply n | apply Ref.eq_sym; apply Hr]] |].
      case (Ref.eq_dec (Cap.target v') r'); intros; auto; try contradiction; apply addCap_eq; auto.
    (* transpose_neqkey *)
      unfold Obj_FoldEqual.Props.transpose_neqkey.
      intros.
      case (Ref.eq_dec (Cap.target e) r);
        case (Ref.eq_dec (Cap.target e') r); intros; try apply Obj.eq_refl.
      eapply addCap_transpose_neqkey; auto.
    Qed.


    Theorem rmCapsByTarget_1: forall v r k o,
      ~ Ref.eq (Cap.target v) r -> Obj.MapS.MapsTo k v o ->
      Obj.MapS.MapsTo k v (rmCapsByTarget r o).
    Proof.
      intros v r k o Hneq.
      unfold rmCapsByTarget; unfold addCap.
      eapply Obj_Props.fold_rec_bis with (P:= fun m A =>Obj.MapS.MapsTo k v m -> Obj.MapS.MapsTo k v A); intros; eauto.
    (* mapsto k v a *)
      apply H0; eapply Obj_Facts.find_mapsto_iff; eapply Obj_Facts.find_mapsto_iff in H1; rewrite <- H1; apply H.
    (* mapsto k v (if ... ) *)
      case (Ref.eq_dec (Cap.target e) r); intros.
    (* (target e) [=] r *)
      eapply Obj_Facts.add_mapsto_iff in H2; destruct H2 as [[Heq Heq']|[Heq Hmap]]; auto; rewrite Heq' in *; try contradiction.
    (* target e [=] r *)
      eapply Obj_Facts.add_mapsto_iff in H2; destruct H2 as [[Heq Heq']|[Heq Hmap]]; auto; try rewrite Heq' in *;
        eapply Obj_Facts.add_mapsto_iff; auto.
    Qed.

    Theorem rmCapsByTarget_2: forall k r v o,
      Obj.MapS.MapsTo k v (rmCapsByTarget r o) -> Obj.MapS.MapsTo k v o.
    Proof.
      intros k r v o.
      unfold rmCapsByTarget.
      eapply Obj_Props.fold_rec_bis with (P:= fun m A => Obj.MapS.MapsTo k v A -> Obj.MapS.MapsTo k v m); intros; eauto.
      apply H0 in H1; eapply Obj_Facts.find_mapsto_iff; eapply Obj_Facts.find_mapsto_iff in H1; rewrite <- H1; auto.
      destruct (Ref.eq_dec (Cap.target e) r).
    (* case eq *)
      eapply Obj_Facts.add_mapsto_iff; apply H1 in H2; right; intuition auto.
      apply H0; unfold Obj.MapS.In; eapply Obj.MapS.MapsTo_1 in H2; apply Ind.eq_sym in H3; try apply H3.
      eapply ex_intro; eauto.
    (* case neq *)
      unfold addCap in *.
      eapply Obj_Facts.add_mapsto_iff; eapply Obj_Facts.add_mapsto_iff in H2.
      intuition eauto.
    Qed.

    Theorem rmCapsByTarget_3: forall v r k o,
      Ref.eq (Cap.target v) r -> 
      Obj.MapS.MapsTo k v o ->
      ~ exists v', Cap.eq v v' /\ Obj.MapS.MapsTo k v' (rmCapsByTarget r o).
    Proof.
      intros v r k o Heq.
      unfold rmCapsByTarget.
      eapply Obj_Props.fold_rec_bis with 
        (P:= fun m A => Obj.MapS.MapsTo k v o -> ~ exists v', Cap.eq v v' /\ Obj.MapS.MapsTo k v' A); intros; eauto.
    (* ~ mapsto k v empty *)
      unfold not; intros [v' [HeqV Hmap]].
      eapply Obj_Facts.empty_mapsto_iff in Hmap; assumption.
    (* ~ mapsto k v step *)
      destruct (Ref.eq_dec (Cap.target e) r) as [Hd | Hd].
    (* target e [=] r *)
      apply H1; auto.
    (* target e [<>] r *)
      intros [v' [HeqV' Hmap]].
      apply H1; auto.
      apply Obj_Facts.add_mapsto_iff in Hmap.
      destruct Hmap as [[Heq2 Heq2']|[Heq2 Hmap2]]; auto; try rewrite Heq2' in *; try solve [intuition eauto].
      eapply Ref.eq_trans in Heq; [| apply Ref.eq_sym; apply (Cap.target_eq _ _ HeqV')]; try contradiction.
    Qed.

    Hint Resolve rmCapsByTarget_1 rmCapsByTarget_2 rmCapsByTarget_3.

    Definition rmCapsByTarget_spec r o o' := forall k v,     
      Obj.MapS.MapsTo k v o' <->   Obj.MapS.MapsTo k v o /\ ~ Ref.eq (Cap.target v) r.

    Theorem rmCapsByTarget_spec_rmCapsByTarget: forall r o, rmCapsByTarget_spec r o (rmCapsByTarget r o).
    Proof.
      unfold rmCapsByTarget_spec; intros; split; intros; intuition eauto. 
      eapply (rmCapsByTarget_3 v r k o); eauto.
    Qed.

    Hint Resolve rmCapsByTarget_spec_rmCapsByTarget.

End MakeObjConv.

