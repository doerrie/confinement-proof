Require FSets.
Require FSetFacts.
Require RelationClasses.
Require FSetAddEq.
Require FoldEqual.
Require Import Morphisms.
Require Import OrderedTypeEquiv.

Module Make (F:FSetInterface.S).

  Module Facts  := FSetFacts.Facts F.
  Module AddEQ := FSetAddEq.Make F.
  Module Props := AddEQ.Properties.
  Module Dep := FSetBridge.DepOfNodep F.
  Module FEq := FoldEqual.Make F.
  Module FEquiv := OT_Equiv F.
  Module EEquiv := OT_Equiv F.E.


  Section fold_order.
    
    Variable A:Type.
    Variable eqA : Relation_Definitions.relation A.
    Variable A_EQ: RelationClasses.Equivalence eqA.
    Variable leA: Relation_Definitions.relation A.
    Variable A_PreOrd: RelationClasses.PreOrder leA.
    Variable A_PartOrd: RelationClasses.PartialOrder eqA leA.


    Definition F_EQ := FEquiv.Equiv.
    Definition E_EQ := EEquiv.Equiv.
    
    (* the reason we claim foldEqual f f and f' f' is because we need
      f and f' to be respectful morphisms over set and A.  At least, I think so,
      and I want to leverage current libraries, even though they are a bit outdated. *)

    Require SetoidList.

    Definition subset_leA_comm f f' := forall a a' e e', leA a a' -> F.E.eq e e' -> leA (f e a) (f' e' a').

    Definition leA_incremental (f: F.E.t -> A -> A) := forall a e, leA a (f e a).

    Definition foldPartialOrder (f f': F.E.t -> A -> A) :=
      Proper (F.E.eq ==> eqA ==> eqA) f  /\ Proper (F.E.eq ==> eqA ==> eqA) f' /\
     SetoidList.transpose eqA f' /\ subset_leA_comm f f'.

      Theorem Morphism_is_compat_op: forall (C D:Type)
        (eqC : Relation_Definitions.relation C)
        (eqD : Relation_Definitions.relation D)
        (C_EQ: RelationClasses.Equivalence eqC)
        (D_EQ: RelationClasses.Equivalence eqD)
        (f: C -> D -> D),
       Proper (eqC ==> eqD ==> eqD) f -> SetoidList.compat_op eqC eqD f.
      Proof.
      unfold SetoidList.compat_op;      intros.
      assumption.
      Qed.

      Implicit Arguments Morphism_is_compat_op [C D eqC eqD f].

    Theorem fold_foldPartialOrder : forall (f f': F.E.t -> A -> A), foldPartialOrder f f' ->
      forall (acc acc': A), leA acc acc' -> forall (s s' : F.t), F.Equal s s' ->
      leA (F.fold f s acc) (F.fold f' s' acc').
    Proof.
      intros f f' [Hfm [Hfm' [Htr Hco]]] acc acc' Hle s.
      eapply Props.fold_rec_bis with (i:=acc) (s:=s).
      (* compat *)
      intros.
      eapply H0; auto.      
      setoid_rewrite H; auto.
      (* base *)
      intros.
      eapply Props.fold_rec_nodep; intros; eauto.
      eapply F.eq_sym in H.
      eapply Props.empty_is_empty_2 in H.
      eapply H in H0.
      contradiction.
      (* step *)
      intros x a s0 Hin Hnin IH s' Heq.
      assert (F.In x s') as Hin'; [setoid_rewrite <- Heq; eapply F.add_1; eauto|].
      generalize (@Props.remove_fold_1 A eqA A_EQ f'
        (Morphism_is_compat_op E_EQ A_EQ Hfm') Htr acc' _ _ Hin'); intros Hfeq.
      setoid_symmetry in Hfeq.
      eapply A_PartOrd in Hfeq.
      repeat progress (red in Hfeq; simpl in Hfeq; try unfold Basics.flip in Hfeq).
      destruct Hfeq as [HleA HleA'].
      destruct A_PreOrd as [A_refl A_trans].
      eapply A_trans;[|eapply HleA'].
      eapply Hco; eauto.
      eapply IH.
      setoid_rewrite <- Heq.
      rewrite Props.remove_add; [apply F.eq_refl|eauto].
    Qed.

  (* The above holds if s [<=] s', provided f is incremental.  The following convenince theorem handles
     most of the base case *)

    Theorem fold_partialOrder_incremental : forall (f : F.E.t -> A -> A), leA_incremental f ->
      forall (acc acc': A), leA acc acc' -> forall (s : F.t), leA acc (F.fold f s acc').
    Proof.
      intros.
      apply Props.fold_rec with
        (f:=f) (i:=acc') (s:=s); intros; auto.
      unfold leA_incremental in *.
      destruct A_PreOrd as [A_refl A_trans].
      eapply A_trans;[apply H4|apply H].
    Qed.

    Theorem fold_foldpartialOrder_incremental: forall (f f': F.E.t -> A -> A), foldPartialOrder f f' ->
      leA_incremental f' -> forall (acc acc': A), leA acc acc' -> forall (s s' : F.t), F.Subset s s' ->
      leA (F.fold f s acc) (F.fold f' s' acc').
    Proof.
      intros f f' Hpo Hinc acc acc' Hle s s' Hsub.
      generalize Hpo; intros [Hfm [Hfm' [Htr Hco]]].
      destruct A_PreOrd as [leA_refl leA_trans].
      eapply leA_trans.
      (* by Props.inter_subset Props.inter_sym and Hsub we know that (F.inter s' s) [=] s,
         we may therefore apply fold_foldPartialOrder. *)
      eapply fold_foldPartialOrder; 
        [apply Hpo | apply Hle| 
          eapply F.eq_trans; 
            [eapply F.eq_sym; eapply Props.inter_subset_equal; apply Hsub | eapply Props.inter_sym]].
     (* this is now the correct form to continue *)
      generalize (Props.fold_diff_inter A_EQ (Morphism_is_compat_op E_EQ A_EQ Hfm') Htr acc' s' s); intros Hfeq.
      eapply A_PartOrd in Hfeq.
      repeat progress (red in Hfeq; simpl in Hfeq; try unfold Basics.flip in Hfeq).
      destruct Hfeq as [HleA HleA'].
      eapply leA_trans; [| eapply HleA].
      eapply fold_partialOrder_incremental; auto.
   Qed.
  End fold_order.

End Make.


