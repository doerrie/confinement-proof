Require Import List Sorting SetoidList.
Require Import FMapInterface2.
Require FMapFacts2.
Require Import RelationClasses.
Require Import OrderedTypeEx.
Require Import OrderedTypeEquiv.
Require Import OrdFMapEquiv.
Require Import Morphisms.

Module Make_fun (E:OrderedType) (MapS:Sfun E) (Data: OrderedType) (M:Sord_fun E MapS Data).

  Module Props := FMapFacts2.WProperties_fun E MapS.
  Module Facts  := Props.F.

  Import M.
  Import MapS.
  Module MEquiv := MakeEquiv_fun E MapS Data M.
  Import MEquiv.
  Module KeyOrdFacts := OrderedType.OrderedTypeFacts E.
  



  Module KDP_M := PairOrderedType E Data.
  Definition KDP := KDP_M.t.
  Definition eqKDP :=KDP_M.eq.
  Module KDP_Equiv := OT_Equiv KDP_M.
  Definition KDP_ST := KDP_Equiv.Equiv.

  Module DataEquiv := OT_Equiv Data.


  Section fold_equal.
    
    Variable A:Type.
    Variable eqA: Relation_Definitions.relation A.
    Variable A_ST:RelationClasses.Equivalence eqA.

    Variable elt : Type.


    Definition foldEqual (f f': key -> Data.t -> A -> A) :=
      forall (a a' : A),
        eqA a a' ->
        forall (k k' : key),
          E.eq k k' ->
          forall (v v' : Data.t),
            Data.eq v v' ->
            eqA (f k v a) (f' k' v' a').

    Notation equiv_refl E := (@Equivalence_Reflexive _ _ E).
    Notation equiv_sym E := (@Equivalence_Symmetric _ _ E).
    Notation equiv_trans E := (@Equivalence_Transitive _ _ E).
    
    Theorem foldEqual_sym : forall f f', foldEqual f f' -> foldEqual f' f.
    Proof.
      intros.
      unfold foldEqual in *.
      intros.
      apply (equiv_sym A_ST).
      apply H; auto.
      apply (equiv_sym A_ST); auto.
    Qed.
    
    Implicit Arguments foldEqual_sym [f f'].

    Definition pair_fn (f : key -> Data.t -> A -> A) (p: KDP) (a : A) := f (fst p) (snd p) a.

    Definition pair_foldEqual (f f': (key * Data.t) -> A -> A) :=
      forall (a a' : A),
        eqA a a' ->
        forall (p p' : KDP),
          eqKDP p p' ->
          eqA (f p a) (f' p' a').

    Theorem pair_foldEqual_iff : forall f f',
      foldEqual f f' <-> pair_foldEqual (pair_fn f) (pair_fn f').
    Proof.
      intros.
      unfold pair_fn; unfold pair_foldEqual; unfold foldEqual.
      split; intros; unfold eqKDP in *; unfold KDP_M.eq in *; 
        [destruct H1; eapply H; auto | eapply H with (p:=(k,v)) (p':=(k',v')); auto].
    Qed.

    Implicit Arguments pair_foldEqual [f f'].

(*    Theorem compat_op_foldEqual : forall f f',
      pair_foldEqual f f' -> SetoidList.compat_op eqKDP eqA f'.
    Proof.
      intros.
      unfold foldEqual in *; unfold SetoidList.compat_op in *.
      intros.
      generalize (H _ _ H1 _ _ H0); intros.    
      generalize (H _ _ ((equiv_refl A_ST) y) _ _ (KDP_M.eq_refl x)); intros.
      apply (equiv_sym A_ST) in H3.
      eapply (equiv_trans A_ST); [apply H3 | apply H2].
    Qed.

    Theorem transpose_foldEqual : forall f f',
      pair_foldEqual f f' -> SetoidList.transpose eqA f -> SetoidList.transpose eqA f'.
    Proof.
      intros f f' Hfeq H.
      unfold foldEqual in *; unfold SetoidList.transpose.
      intros.
      generalize (H x y z); intros Htrans.
      generalize (compat_op_foldEqual _ _ Hfeq); unfold SetoidList.compat_op; intros Hcompat.
      generalize (Hcompat _ _ _ _ (KDP_M.eq_refl x) (Hfeq _ _ ((equiv_refl A_ST) z) _ _ (KDP_M.eq_refl y))); intros.
      generalize (Hcompat _ _ _ _ (KDP_M.eq_refl y) (Hfeq _ _ ((equiv_refl A_ST) z) _ _ (KDP_M.eq_refl x))); intros.
      generalize (Hfeq _ _ ((equiv_refl A_ST) (f y z)) _ _ (KDP_M.eq_refl x)); intros.
      generalize (Hfeq _ _ ((equiv_refl A_ST) (f x z)) _ _ (KDP_M.eq_refl y)); intros.
      
      eapply (equiv_trans A_ST); [apply (equiv_sym A_ST) in H0; apply H0 |].
      eapply (equiv_trans A_ST); [apply (equiv_sym A_ST) in H2; apply H2 |].
      eapply (equiv_trans A_ST); [apply Htrans |].
      eapply (equiv_trans A_ST); [apply H3 |].
      eapply (equiv_trans A_ST); [apply H1| apply (equiv_refl A_ST)].
    Qed. 

    Hint Resolve compat_op_foldEqual transpose_foldEqual. *)


    Notation Leibniz := (@Logic.eq _).
    Theorem foldEqual_comp : forall (f f': key -> Data.t -> A -> A),
      foldEqual f f' ->
      Proper (E.eq==>Leibniz==>eqA==>eqA) f'.
    Proof.
      intros f f' Hf.
      unfold Proper.
      unfold respectful.
      intros.
      unfold foldEqual in *.
      (* use foldequal to generalize the terms *)
      generalize (Hf _ _ H1 _ _ H _ _ (DataEquiv.Leibniz_eq H0)); intros Hm.
      eapply (equiv_trans A_ST); [|apply Hm]; clear Hm.
      (* use foldequal to generalize the fn *)
      generalize (Hf _ _ ((equiv_refl A_ST) x1) _ _ (E.eq_refl x) _ _ ( DataEquiv.Leibniz_eq (Logic.refl_equal x0))); intros Hm.
      apply (equiv_sym A_ST). auto.
    Qed.
    Implicit Arguments foldEqual_comp [f f'].
    (* (* so we're constructing a morphism from foldEqual.  Perhaps a cleaner *)
    (*    strategy would be to construct foldEqual from morphisms *) *)

    Theorem transpose_foldEqual_1: forall f f',
      foldEqual f f' ->
      Props.transpose_neqkey eqA f ->
      Props.transpose_neqkey eqA f'.
    Proof.
      intros f f' Hf Hp.
      unfold Props.transpose_neqkey in *.
      intros k k' e e' a HneqK.
      generalize (Hp _ _ e e' a HneqK); clear Hp; intros Hp.
      (* use foldequal to generalize the fn *)
      unfold foldEqual in *.
      generalize (Hf _ _ ((equiv_refl A_ST) a) _ _ (E.eq_refl k) _ _ (DataEquiv.Leibniz_eq (Logic.refl_equal e))); intros Hinner.      
      generalize (Hf _ _ Hinner _ _ (E.eq_refl k') _ _ (DataEquiv.Leibniz_eq (Logic.refl_equal e'))); intros H.
      (* reduce half to f from f' *)
      eapply (equiv_trans A_ST);[|apply H].
      clear H Hinner.
      generalize (Hf _ _ ((equiv_refl A_ST) a) _ _ (E.eq_refl k') _ _ (DataEquiv.Leibniz_eq (Logic.refl_equal e'))); intros Hinner.      
      generalize (Hf _ _ Hinner _ _ (E.eq_refl k) _ _ (DataEquiv.Leibniz_eq (Logic.refl_equal e))); intros H.
      apply (equiv_sym A_ST) in H.
      eapply (equiv_trans A_ST);[apply H| auto].
    Qed.

    Hint Immediate foldEqual_sym.

    Theorem transpose_foldEqual : forall {f} {f'},
      foldEqual f f' ->
      (Props.transpose_neqkey eqA f <-> Props.transpose_neqkey eqA f').
    Proof.
      intros; split; intros;
        eapply transpose_foldEqual_1; eauto.
    Qed.

    Theorem fold2_foldEqual : forall m f f' acc acc',
      eqA acc acc' -> foldEqual f f' ->
      Props.transpose_neqkey eqA f ->
      eqA (fold f m acc) (fold f' m acc').
    Proof.
      intros.
      apply Props.fold_rec with
        (f:=f) (i:=acc) (m:=m); intros; auto.
      (* base *)
      eapply (equiv_trans A_ST); [apply H |]. 
      apply (equiv_sym A_ST); eapply (Props.fold_Empty A_ST); auto.
      (* step *)
      (* first reduce (fold f' m'' acc') to (f' k e (fold f' m' acc')) *)
      eapply transpose_foldEqual in H1; eauto.
      generalize (Props.fold_Add A_ST (foldEqual_comp H0) H1 acc' H3 H4); intros Heq.
      apply (equiv_sym A_ST) in Heq.
      eapply (equiv_trans A_ST); [|apply Heq].
      clear Heq.
      (* next reduce (f k e a) to (f' k e a). *)
      generalize (H0 _ _ ((equiv_refl A_ST) a) _ _ (E.eq_refl k) _ _ (DataEquiv.Leibniz_eq (Logic.refl_equal e))); intros Heq.
      eapply (equiv_trans A_ST); [apply Heq|]; clear Heq.
      (* finally apply foldEqual_comp from foldEqual *)
      apply (foldEqual_comp H0); auto.
    Qed.

    Definition equiv_key_elt p p' :=
      E.eq (fst p) (fst p') /\ Data.eq (snd p) (snd p').
    
    Theorem InA_equiv_eq: 
      forall (k:E.t) (e:Data.t) (l: list (E.t*Data.t)),
        InA (@eq_key_elt Data.t) (k,e) l ->
        InA equiv_key_elt (k,e) l.
    Proof.
      intros.
      induction l; simpl in *.
      apply InA_nil in H; contradiction.
      induction H.
      constructor.
      unfold eq_key_elt in *; unfold equiv_key_elt in *.
      destruct H; split; auto; unfold key in *; rewrite H0; auto.
      constructor 2; auto.
    Qed.

    Theorem InA_eq_exists_equiv:
      forall (k:E.t) (e:Data.t) (l: list (E.t*Data.t)),
        InA equiv_key_elt (k,e) l ->
        NoDupA (@eq_key Data.t) l ->
        (exists e', Data.eq e e' /\ InA (@eq_key_elt Data.t) (k,e') l).
    Proof.
      intros k e.
      induction l; intros.
        (* base *)
      apply InA_nil in H; contradiction.
        (* step *)
      inversion H0.
      inversion H.
        (* head *)
      destruct a as [k' e']; destruct H6 as [Hk Hd]; simpl in *.
      eapply ex_intro; split;
        [apply Hd
          | constructor; unfold eq_key_elt; simpl; split; auto].
        (* tail *)
      destruct a as [k' e'].
      generalize (IHl H6 H4); intros IH'.
      destruct IH' as [e'' IH']; destruct IH' as [IHeq IHina].
      eapply ex_intro; split; [apply IHeq|].
      constructor 2; auto.
    Qed.

    Theorem InA_equiv: 
      forall p p' (l: list (E.t*Data.t)),
        equiv_key_elt p p' ->
        InA equiv_key_elt p l ->
        InA equiv_key_elt p' l.
    Proof.
      intros.
      induction l; simpl in *.
      apply InA_nil in H0; contradiction.
      inversion H0.
      constructor 1.
      unfold equiv_key_elt in *.
      destruct H2; destruct H; split; auto.
      eapply E.eq_trans; [apply E.eq_sym; apply H| auto].
      eapply Data.eq_trans; [apply Data.eq_sym; apply H5 | auto].
      constructor 2; auto.
    Qed.

    Theorem Equiv_InA_if: forall m m',
      eq m m' -> forall x, 
        InA equiv_key_elt x (elements m) ->
        InA equiv_key_elt x (elements m').
    Proof.
      intros.
      destruct x as [k e].
      generalize (InA_eq_exists_equiv _ _ _ H0 (elements_3w m)); intros H1.
      destruct H1 as [e' [H1 H2]].
      apply elements_2 in H2.
        (* find another e'' in m' *)
      generalize (exists_mapsTo_eq _ _ H _ _ H2 _ (E.eq_refl k));
        intros H3.
      destruct H3 as [e'' [Heq Hmap]].
      apply InA_equiv with (p:=(k,e'')).
      unfold equiv_key_elt.
      simpl; split; auto; apply Data.eq_trans with e'; eauto.
      apply InA_equiv_eq.
      apply elements_1; auto.
    Qed.


    Theorem Equiv_equivlistA: forall m m',
      eq m m' <->
      equivlistA equiv_key_elt (elements m) (elements m').
    Proof.
      intros.
      split; intros.
      (* eq -> equivlistA *)
      split; intros; eapply Equiv_InA_if;
        solve [apply H | apply eq_sym in H; apply H| auto].
      (* equivlistA -> eq *)
      apply eq_1.
      unfold Equivb.
      unfold Equiv.
      split; intros.
      unfold In; split; intros; destruct H0.
      (* In one *)
      Theorem InA_equiv_In_if: forall m m',
        equivlistA equiv_key_elt (elements m) (elements m') ->
        forall k x, MapsTo k x m ->
          exists e, MapsTo k e m'.
      Proof.
        intros.
        apply elements_1 in H0.
        apply InA_equiv_eq in H0.
        apply H in H0.
        generalize (InA_eq_exists_equiv _ _ _ H0 (elements_3w m')); intros.
        destruct H1 as [e' [H1 H2]].
        apply elements_2 in H2.
        eapply ex_intro; eauto.
      Qed.
      eapply InA_equiv_In_if; eauto.
      eapply InA_equiv_In_if; eauto.
      unfold equivlistA in *; intros; eapply iff_sym; eapply H.
      (* final cmp operation *)
      apply elements_1 in H0; apply InA_equiv_eq in H0.
      apply elements_1 in H1; apply InA_equiv_eq in H1.
      eapply H in H0.
      clear H m.
      generalize (InA_eq_exists_equiv _ _ _ H0 (elements_3w m')); 
        intros H0dup; destruct H0dup as [e0 [Heq HinA]].
      generalize (InA_eq_exists_equiv _ _ _ H1 (elements_3w m')); 
        intros H1dup; destruct H1dup as [e0' [Heq' HinA']].
      (* show e0 = e0' *)
      apply elements_2 in HinA; apply elements_2 in HinA'.
      apply find_1 in HinA'; apply find_1 in HinA.
      rewrite HinA in HinA'.
      injection HinA'; intros H.
      rewrite H in *.
      eapply Data.eq_trans with (z:= e') in Heq; auto.
      clear HinA HinA' Heq' H H1 H0 e0 e0' k m'.
      unfold Cmp.
      unfold cmp.
      destruct (Data.compare e e'); auto;
        apply Data.lt_not_eq in l; try contradiction; 
          apply Data.eq_sym in Heq; contradiction.
    Qed.

    (* with elements_3, we should be able to get eqlistA on lists *)

    

    Theorem eqlist_equivlist: forall m m',
      equivlistA equiv_key_elt (elements m) (elements m') ->
      eqlistA equiv_key_elt (elements m) (elements m').
    Proof. 
      intros.
      eapply SortA_equivlistA_eqlistA; eauto; try eapply elements_3.      
      split; red.

      Theorem equiv_key_elt_refl: forall x, equiv_key_elt x x.
      Proof.
        intros.
        unfold equiv_key_elt.
        split; try apply E.eq_refl; try apply Data.eq_refl; auto.
      Qed.
      eapply equiv_key_elt_refl.
      
      Theorem equiv_key_elt_sym: forall x y,
        equiv_key_elt x y -> equiv_key_elt y x.
      Proof.
        intros.
        destruct H.
        apply E.eq_sym in H; apply Data.eq_sym in H0.
        split; auto.
      Qed.
      apply equiv_key_elt_sym.
      
      Theorem equiv_key_elt_trans: forall x y z,
        equiv_key_elt x y -> equiv_key_elt y z -> equiv_key_elt x z.
      Proof.
        intros.
        destruct H.
        destruct H0.
        split; solve [eapply E.eq_trans; eauto|eapply Data.eq_trans; eauto].
      Qed.
      apply equiv_key_elt_trans.

      split; repeat progress (red).

      Theorem lt_key_not_equiv: forall x y, 
        lt_key x y -> ~ equiv_key_elt x y.
      Proof.
        intros; intro Hnot; destruct Hnot;
          apply E.lt_not_eq in H; auto.
      Qed.
      intros.
      eapply lt_key_not_equiv; [eauto | apply equiv_key_elt_refl].

      Theorem lt_key_trans: forall (B:Type) x y z ,
        lt_key x y -> lt_key y z -> (@lt_key B) x z.
      Proof.
        intros.
        eapply E.lt_trans; eauto.
      Qed.
      apply lt_key_trans.

      split.

      Theorem lt_key_equiv: forall x y z, 
        lt_key x y -> equiv_key_elt y z -> lt_key x z.
      Proof.
        intros.
        destruct H0 as [H0 _].
        eapply KeyOrdFacts.lt_eq; eauto.
      Qed.

      Theorem equiv_lt_key: forall x y z, 
        equiv_key_elt x y -> lt_key y z -> lt_key x z.
      Proof.
        intros.
        destruct H as [H _].
        eapply KeyOrdFacts.eq_lt; eauto.
      Qed.
      intros.
      eapply lt_key_equiv; eauto.
      eapply equiv_lt_key; eauto.
      eapply equiv_key_elt_sym; auto.

      intros.
      eapply equiv_lt_key; eauto.
      eapply lt_key_equiv; eauto.
      eapply equiv_key_elt_sym; auto.
    Qed.

    Section eqlistA.
      Variable B:Type.
      Variable eqB: Relation_Definitions.relation B.
      Variable B_ST:RelationClasses.Equivalence eqB.

      Theorem eqlistA_equivlistA: forall l l',
        eqlistA eqB l l' -> equivlistA eqB l l'.
      Proof.
        intros.
        induction H.
        split; intros; auto.
        split; intros;
          (eapply InA_cons in H1; destruct H1;
            [eapply InA_cons; left; eapply (equiv_trans B_ST); eauto; 
              apply (equiv_sym B_ST); eauto
              | eapply InA_cons; right; eapply IHeqlistA; auto]).
      Qed.
    End eqlistA.

    Theorem Equiv_elements: forall m m',
      eq m m' <->
      eqlistA equiv_key_elt (elements m) (elements m').
    Proof.
      intros; split; intros.
      (* eq -> eqlistA *)
      apply eqlist_equivlist; eapply  Equiv_equivlistA; auto.
      (* eqlistA -> eq *)
      eapply  Equiv_equivlistA; auto.
      apply eqlistA_equivlistA; eauto.
      split.
      unfold Reflexive; apply equiv_key_elt_refl.
      unfold Symmetric; apply equiv_key_elt_sym.
      unfold Transitive; apply equiv_key_elt_trans.
    Qed.

Unset Automatic Introduction.

      Theorem fold_trans_foldEqual f acc:
        Proper (E.eq==>Data.eq==>eqA==>eqA) f ->
        forall m m',
          eq m m' ->
          eqA (fold f m acc) (fold f m' acc).
      Proof.
        intros f acc Htrans m m' Heq.
      (* reduce to lists with elements *)
        do 2 rewrite fold_1.
      (* fold_right will induct correctly, rewrite and show NoDupA *)
        do 2 rewrite <- fold_left_rev_right.
        eapply fold_right_eqlistA with (eqB := eqA) (eqA := equiv_key_elt); try exact A_ST.
        do 4 red in Htrans; do 3 red; unfold equiv_key_elt; intros; destruct H; eapply Htrans; auto.
        apply eqlistA_rev; eapply Equiv_elements; auto.
      Qed.
      Hint Resolve fold_trans_foldEqual.
        
      Theorem foldEqual_Proper f f': foldEqual f f' ->
        Proper (E.eq==>Data.eq==>eqA==>eqA) f'.
      Proof.
        intros.
        unfold foldEqual in *.
        unfold Proper.
        unfold respectful.
        intros.
        (* use foldequal to generalize the terms *)
        generalize (H _ _ H2 _ _ H0 _ _ H1); intros Hm.
        eapply (equiv_trans A_ST); [|apply Hm]; clear Hm.
        (* use foldequal to generalize the fn *)
        generalize (H _ _ ((equiv_refl A_ST) x1) _ _ (E.eq_refl x) _ _ (Data.eq_refl x0)); intros Hm.
        apply (equiv_sym A_ST). auto.        
      Qed.
      Hint Resolve foldEqual_Proper.


    
    Theorem fold_foldEqual f f' m m' acc acc': 
      eq m m' -> eqA acc acc' -> foldEqual f f' ->
      Props.transpose_neqkey eqA f ->
      eqA (fold f m acc) (fold f' m' acc').
    Proof.
      intros.
      (* reduce (fold f m acc) to (fold f' m acc') *)
      generalize (fold2_foldEqual m f f' acc acc' H0 H1 H2); intros Heq;
        eapply (equiv_trans A_ST); [apply Heq|]; clear Heq.
      (* transpose_neqkey eqA f' *)
      eapply transpose_foldEqual in H2; eauto.
      (* we have reduced to Props.fold_Equal over a different Proper *)
      (* the whole FMap/FSet library should be rewritten over general morphisms *)
      (* eauto takes care of the rest *)
    Qed.
        
  
  End fold_equal.

End Make_fun.


Module Make (M:Sord).
  Include Make_fun M.MapS.E M.MapS M.Data M.
End Make.

