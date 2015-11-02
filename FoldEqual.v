Require FSets.
Require FSetFacts.
Require RelationClasses.
Require FSetAddEq.

Module Make (F:FSetInterface.S).


  Module Facts  := FSetFacts.Facts F.
  Module AddEQ := FSetAddEq.Make F.
  Module Props := AddEQ.Properties.
  Module Dep := FSetBridge.DepOfNodep F.

  Section fold_equal.
    
    Variable A:Type.
    Variable eqA: Relation_Definitions.relation A.
    Variable A_ST:RelationClasses.Equivalence eqA.

    (* I don't know how to access these in the new class notation *)
    
    Theorem eqA_refl : forall x, eqA x x.
    Proof.
      apply A_ST.
    Qed.
    
    Theorem eqA_sym : forall x y, eqA x y -> eqA y x.
    Proof.
      apply A_ST.
    Qed.
    
    Theorem eqA_trans: forall x y z, eqA x y -> eqA y z -> eqA x z.
    Proof.
      apply A_ST.
    Qed.
    
    Definition foldEqual (f f': F.E.t -> A -> A) :=
      forall (a a' : A),
        eqA a a' ->
        forall (e e' : F.E.t),
          F.E.eq e e' ->
          eqA (f e a) (f' e' a').

    Require SetoidList.
    
    Theorem foldEqual_sym : forall f f', foldEqual f f' -> foldEqual f' f.
    Proof.
      intros.
      unfold foldEqual in *.
      intros.
      apply eqA_sym.
      apply H; auto.
      apply eqA_sym; auto.
    Qed.

    Theorem compat_op_foldEqual : forall (f f': F.E.t -> A -> A),
      foldEqual f f' -> SetoidList.compat_op F.E.eq eqA f'.
    Proof.
      intros.
      unfold foldEqual in *; unfold SetoidList.compat_op in *.
      unfold Morphisms.Proper in *; unfold Morphisms.respectful in *.
      intros.
      generalize (H _ _ H1 _ _ H0); intros.    
      generalize (H _ _ (eqA_refl x0) _ _ (F.E.eq_refl x)); intros.
      apply eqA_sym in H3.
      eapply eqA_trans; [apply H3 | apply H2].
    Qed.

    Theorem transpose_foldEqual : forall (f f': F.E.t -> A -> A),
      foldEqual f f' -> SetoidList.transpose eqA f -> SetoidList.transpose eqA f'.
    Proof.
      intros f f' Hfeq H.
      unfold foldEqual in *; unfold SetoidList.transpose.
      intros.
      generalize (H x y z); intros Htrans.
      generalize (compat_op_foldEqual _ _ Hfeq); unfold SetoidList.compat_op; intros Hcompat.
      unfold Morphisms.Proper in *; unfold Morphisms.respectful in *.

      generalize (Hcompat _ _ (F.E.eq_refl x) _ _ (Hfeq _ _ (eqA_refl z) _ _ (F.E.eq_refl y))); intros.
      generalize (Hcompat _ _ (F.E.eq_refl y) _ _ (Hfeq _ _ (eqA_refl z) _ _ (F.E.eq_refl x))); intros.
      generalize (Hfeq _ _ (eqA_refl (f y z)) _ _ (F.E.eq_refl x)); intros.
      generalize (Hfeq _ _ (eqA_refl (f x z)) _ _ (F.E.eq_refl y)); intros.
      
      eapply eqA_trans; [apply eqA_sym in H0; apply H0 |].
      eapply eqA_trans; [apply eqA_sym in H2; apply H2 |].
      eapply eqA_trans; [apply Htrans |].
      eapply eqA_trans; [apply H3 |].
      eapply eqA_trans; [apply H1| apply eqA_refl].
    Qed.
    
(*   Theorem foldAGEqual_complete_ag_fold_src : *)
(*     forall (src src' : R.t), *)
(*       R.eq src src' -> *)
(*       foldAGEqual R.eq (complete_ag_fold_src src) (complete_ag_fold_src src'). *)
(*   Proof. *)
(*     intros. *)
(*     unfold foldAGEqual. *)
(*     intros. *)
(*     eapply eq_complete_ag_fold_src_full; *)
(*       [apply R.eq_sym; apply H |  *)
(*         apply R.eq_sym; apply H1 | *)
(*           apply AG.eq_sym; apply H0 |  *)
(*             eauto | eauto | eauto |  *)
(*               unfold complete_ag_fold_src; eauto]. *)
(*   Qed. *)

(* (* I need a theorem that states that for an FSetList over a UsualOrderedType, if the FSets are equal, *)
(*    then the Lists underneath are equal *) *)

    Hint Resolve compat_op_foldEqual transpose_foldEqual.
    Hint Immediate foldEqual_sym.

    Theorem fold2_foldEqual : forall (s : F.t) (f f': F.E.t -> A -> A)
      (acc acc': A), eqA acc acc' -> foldEqual f f' ->
      SetoidList.transpose eqA f ->
      eqA (F.fold f s acc) (F.fold f' s acc').
    Proof.
      intros.
      apply Props.fold_rec with
        (f:=f) (i:=acc) (s:=s); intros; auto.
      rewrite (Props.fold_1b _ _ H2); auto.
      generalize (@Props.remove_fold_1 A eqA A_ST f'
        (compat_op_foldEqual f f' H0)
        (transpose_foldEqual f f' H0 H1) acc' s'' x); intros.
      generalize (H4 x); intros Hadd; destruct Hadd.
      eapply H6 in H8; try left; try apply F.E.eq_refl.
      clear H6 H7.
      generalize (AddEQ.Add_remove_Equal _ _ _ H4 H3); intros Heq.
      generalize (foldEqual_sym _ _ H0); intros.
      generalize (compat_op_foldEqual _ _ H6 ); intros H7'. 
      unfold SetoidList.compat_op in H7'; unfold Morphisms.Proper in H7'; unfold Morphisms.respectful in H7'.
      generalize (compat_op_foldEqual _ _ H6 _ _ (F.E.eq_refl x) _ _  H5); intros.
      eapply eqA_trans; [apply H7|clear H7].
      apply eqA_sym; eapply eqA_trans. 
      apply eqA_sym in H8; apply H8.
      generalize (@Props.fold_equal _ _ A_ST f'
        (compat_op_foldEqual _ _ H0)
        (transpose_foldEqual _ _ H0 H1)
        acc' _ _ Heq); intros.
      generalize (compat_op_foldEqual _ _ H0 _ _ (F.E.eq_refl x) _ _ H7); intros.
      apply eqA_sym in H9; eapply eqA_trans; [apply H9| clear H9].
      apply eqA_sym; eapply H0; [apply eqA_refl| apply F.E.eq_refl].
    Qed.

    Theorem fold_foldEqual (f f': F.E.t -> A -> A) (s s' : F.t) (acc acc':A) :
      F.Equal s s' -> eqA acc acc' -> foldEqual f f' ->
      SetoidList.transpose eqA f ->
      eqA (F.fold f s acc) (F.fold f' s' acc').
    Proof.

      intros.
      generalize (fold2_foldEqual s f f' acc acc' H0 H1 H2); intros.
      eapply eqA_trans. apply H3.
      generalize (@Props.fold_equal _ _ A_ST f' 
        (compat_op_foldEqual _ _ H1)
        (transpose_foldEqual _ _ H1 H2)
        acc' _ _ H). auto.
    Qed.

  Require Import Morphisms.
  Theorem foldEqual_refl: forall f,
    Proper (F.E.eq ==> eqA ==> eqA) f ->
    foldEqual f f.
  Proof.
   intros.
   unfold foldEqual; intros.
   eapply H; auto.
  Qed.

  End fold_equal.

    Implicit Arguments foldEqual [ A ].



End Make.


