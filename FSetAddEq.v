Require FSets.
Require FSetFacts.
Require Import Sumbool.

Module Make (F: FSetInterface.S).
  
  Module Facts  := FSetFacts.Facts F.
  Module Properties := FSetProperties.Properties F.
  Module Dep := FSetBridge.DepOfNodep F.
  
  Section Eq.
    Variable x: F.E.t.
    Variable x': F.E.t.
    Variable A: F.t.
    Variable A': F.t.
    Variable B: F.t.
    Variable B': F.t.

    (* added for Coq 8.2, I don't know why unfolding Add goes past E.eq *)
    Theorem Add_unfold : Properties.Add x A A' -> forall x', F.In x' A' <->  F.In x' A \/ F.E.eq x x'.
    Proof.
      intros.
      unfold Properties.Add in *.
      split; intros;
      generalize (H x'0);
      intros;
      destruct H1;
      tauto.
    Qed.

    
    Theorem FSetAdd_Eq:
      F.add x A = F.add x' A -> F.E.eq x x' \/ F.In x A.
    Proof.
      intros H.
      generalize (Properties.Add_add A x'); unfold Properties.Add; intros H0.
      generalize (H0 x); intro H1.
      destruct H1 as [H1 H2].
      rewrite <- H in H1.
      generalize (F.E.eq_refl x). intros H3.
      generalize (F.add_1 A H3). intros H4.
      generalize (H1 H4). intros H5.
      destruct H5;
        eauto with *.
    Qed.
    
    Theorem add_eq_edges:
      F.E.eq x x'-> F.Equal (F.add x A) (F.add x' A).
    Proof.
      intros.
      auto with *.
    Qed.

    Theorem Add_eq_complete: F.E.eq x x' -> F.Equal A A' -> F.Equal B B' -> Properties.Add x A B -> Properties.Add x' A' B'.
    Proof.
      intros H3 H H0 H1.
      unfold Properties.Add in *.
      split;
        unfold F.Equal in *;
          generalize (H y); generalize (H0 y); generalize (H1 y); intros H6 H7 H8;
            destruct H6; destruct H7; destruct H8;
              intros; intuition eauto.
    Qed.
    
    Theorem Add_eq_full: F.Equal A A' -> F.Equal B B' -> Properties.Add x A B -> Properties.Add x A' B'.
    Proof.
      intros H H0 H1.
      unfold Properties.Add in *.
      split; 
        unfold F.Equal in *;
          generalize (H y); generalize (H0 y); generalize (H1 y); intros H6 H7 H8;
            destruct H6; destruct H7; destruct H8;
              intros; intuition auto. 
    Qed.
    
    Theorem Add_eq: F.Equal B B' -> Properties.Add x A B -> Properties.Add x A B'.
    Proof.
      intros H H0.
      unfold Properties.Add in *.
      split;
        unfold F.Equal in *;
          generalize (H y); generalize (H0 y); intros H1 H2 H3;
            destruct H1; destruct H2; auto.
    Qed.

    Theorem Eq_Add_Add: F.Equal A A' -> Properties.Add x A B -> Properties.Add x A' B.
    Proof.
      intros.
      unfold Properties.Add in *.
      unfold F.Equal in *.
      intros.
      generalize (H0 y); intros H1; destruct H1.
      generalize (H y); intros H3; destruct H3.
      split; intuition eauto.
    Qed.

    Theorem Add_Add: F.E.eq x x' -> Properties.Add x A B -> Properties.Add x' B B' -> F.Equal B B'.
    Proof.
      intros.
      intro e.
      generalize (H0 e); intros H0'.
      eapply iff_trans; [eapply H0'| clear H0'].
      generalize (H1 e); intros H1'.      
      eapply iff_sym; eapply iff_trans; [eapply H1'|clear H1'].
      unfold Properties.Add in H0.
      case (F.E.eq_dec e x); intros Heq; intuition; eauto; right;
      generalize (H0 e); intros H0'; intuition; eapply F.E.eq_sym in H2; contradiction.
    Qed.

    Theorem In_eq_full: F.Equal A A' -> F.In x A -> F.In x A'.
    Proof.
      intros H H0.
      unfold F.Equal in H.
      generalize (H x). intros H1.
      destruct H1 as [H1 H2].
      intuition.
    Qed.

    Theorem Eq_Add_complete: F.E.eq x x' -> F.Equal A A' -> Properties.Add x A B -> Properties.Add x' A' B' -> F.Equal B B'.
    Proof.
      intros H9 H H0 H1.
      unfold Properties.Add in *; unfold F.Equal in *.
      intros.
      split;
        generalize (H0 a); intro H2;
          generalize (H1 a); intro H3;
            generalize (H a); intro H4;
              destruct H2; destruct H3; destruct H4;
                intuition eauto.
    Qed.

    Theorem Eq_Add: F.Equal A A' -> Properties.Add x A B -> Properties.Add x A' B' -> F.Equal B B'.
    Proof.
      intros.
      unfold Properties.Add in *; unfold F.Equal in *.
      intros.
      split;
        generalize (H0 a); intro H2;
          generalize (H1 a); intro H3;
            generalize (H a); intro H4;
              destruct H2; destruct H3; destruct H4;
                intuition eauto.
    Qed.
    
    Theorem Add_equal: Properties.Add x A B -> Properties.Add x' A B -> F.E.eq x x' \/ F.In x' A.
    Proof.
      intros.
      unfold Properties.Add in *.
      generalize (H x'); intro H1.
      destruct H1 as [H1 H2].
      generalize (H0 x'); intro H3.
      destruct H3 as [H3 H4].
      eauto.
    Qed.

    Theorem Add_Eq_Add: Properties.Add x A B -> F.E.eq x x' -> Properties.Add x' A B.
    Proof.
      intros.
      unfold Properties.Add in *.
      intro y.
      generalize (H y).
      intro H1.
      destruct H1.
      split.

      intro H3.
      generalize (H1 H3). intro H4.
      destruct H4; eauto.

      intro H3.
      apply H2.
      destruct H3; eauto.
    Qed.
    
    Theorem In_Add: F.In x A -> F.Equal A B -> Properties.Add x A B.
    Proof.
      intros HinX Heq.
      unfold Properties.Add in *.
      intros y.
      unfold F.Equal in *.
      split.
      intros HinY.
      right.
      generalize (Heq y); intros Htmp; destruct Htmp as [HyA HyB]; eauto.

      intros Hand.
      destruct Hand as [HeqXY | HinYA];
        generalize (Heq y); intros Htmp; destruct Htmp as [HinYAi HinYBi]; eauto;
          apply HinYAi;
            generalize (Facts.In_eq_iff A HeqXY); intros Htmp; destruct Htmp; eauto.
    Qed.
    
    Theorem Add_Subset:
      forall a b e,
        Properties.Add e a b -> F.Subset a b.
    Proof.
      intros.
      unfold Properties.Add in *.
      unfold F.Subset.
      intro.
      generalize (H a0). intro.
      destruct H0.
      auto with sets.
    Qed.
    Hint Resolve Add_Subset.

    Theorem Subset_Add : F.Subset A B -> Properties.Add x A A' -> Properties.Add x B B' ->
      Properties.Add x' A A' -> Properties.Add x' B B'.
    Proof.
      intros H H0 H1 H2.
      unfold F.Subset in H.
      unfold Properties.Add in *. intros y.
      split; intros H3;
        generalize (H y); generalize (H0 y); generalize (H1 y); generalize (H2 y); intros H4 H5 H6 H7;
          destruct H6; destruct H5; destruct H4; intuition auto.
    Qed.

    Theorem Add_lub: Properties.Add x A A' -> Properties.Add x' A' B -> Properties.Add x' A B' ->
      Properties.Add x B' B.
    Proof.
      intros Haa' Ha'b Hab'.
      unfold Properties.Add in *; intros; split; intros;
        generalize (Haa' y) (Ha'b y) (Hab' y); intros H1 H2 H3;
          destruct H1; destruct H2; destruct H3;
            intuition eauto.
    Qed.

    Theorem DepAdd_iff_Add: Properties.Add x A B <-> Dep.Add x A B.
    Proof.
      intuition.
    Qed.

    Theorem Add_In : F.E.eq x x' -> Properties.Add x A B -> F.In x' B.
    Proof.
      intuition.
      generalize (H0 x').
      intros H1; destruct H1 as [H1 H2].
      apply H2; auto.
    Qed.

  End Eq.  

    Theorem Add_add: forall x A A', Properties.Add x A A' <-> F.Equal (F.add x A) A'.
    Proof.
      intros; split; intros.

      unfold Properties.Add in *.
      unfold F.Equal.
      intros.
      generalize (H a). intros.
      destruct H0.
      split; Facts.set_iff; trivial.

      eapply Add_eq.
      apply H.
      apply Properties.Add_add.
    Qed.


  Section add_dec.
    Variable x: F.E.t.
    Variable x': F.E.t.
    Variable A: F.t.
    Variable A': F.t.

    Theorem Add_dec: { Properties.Add x A A' } + { ~ Properties.Add x A A' }.
    Proof.
      generalize (Dep.add x A).
      intros Hdep.
      case Hdep; clear Hdep; intros C Hdep.
      generalize (DepAdd_iff_Add x A C); intros Hadd; destruct Hadd as [Hadd1 Hadd2].
      generalize (Dep.equal C A'); intros Ha'.
      intuition.
      
      left.
      apply Add_eq with C; auto.
      
      right.
      intuition.
      apply b.
      apply Eq_Add with x A A; auto.
      apply F.eq_refl.
    Qed.

    Theorem compat_P_Add: SetoidList.compat_P F.E.eq (fun x => Properties.Add x A A').
    Proof.
      unfold SetoidList.compat_P; unfold Morphisms.Proper; unfold Morphisms.respectful; unfold Basics.impl; intros.
      eapply Add_Eq_Add; eauto.
    Qed.

    Theorem compat_op_add: SetoidList.compat_op F.E.eq F.eq F.add.
    Proof.
      unfold SetoidList.compat_op;unfold Morphisms.Proper; unfold Morphisms.respectful; intros.
      eapply Eq_Add_complete; eauto.
    Qed.

  End add_dec.

  Section add.

    Variable x: F.E.t.
    Variable x': F.E.t.
    Variable A: F.t.
    Variable A': F.t.
    Variable B : F.t.

    Theorem Addx_dec: let Addx := (fun x => Properties.Add x A A') in
      forall x:F.E.t, {Addx x} + {~ Addx x}.
    Proof.
      simpl; intros.
      apply Add_dec.
    Qed.      

    Theorem exists_Add_dec: { F.Exists (fun x => Properties.Add x A A') A } +
      { ~ F.Exists (fun x => Properties.Add x A A') A }.
    Proof.
      generalize (compat_P_Add A A'); intros H.
      generalize (Dep.exists_ Addx_dec A); intros H2.
      destruct H2; intuition.
    Qed.

    Theorem add_equal_complete: 
      F.Equal A A' -> F.E.eq x x' -> F.Equal (F.add x A) (F.add x' A').
    Proof.
      intros.
      generalize (Properties.Add_add A x); generalize (Properties.Add_add A' x'); intros.
      eapply Eq_Add_complete; eauto.
    Qed.

    Theorem elim_In_add: F.In x A -> F.In x (F.add x' A).
    Proof.
      intros Hin.
      Facts.set_iff.
      right.
      trivial.
    Qed.

    Theorem Add_Equal : F.E.eq x x' -> F.In x A -> Properties.Add x' A B -> F.Equal A B.
    Proof.
      intros.
      apply F.In_1 with (x:=x) (y:=x') in H0; auto.
      generalize (Properties.Add_add A x'); intros.
      apply Eq_Add with (A:=A) (B:=B) in H2;[|apply Properties.equal_refl|auto].
      generalize (Properties.add_equal H0); intros.
      eapply Properties.equal_sym.
      eapply Properties.equal_trans; [apply H2 | apply H3].
    Qed.

    (* push this over to FSetAddEq.v *)
    Theorem In_nIn_neq :
      F.In x A -> ~ F.In x' A -> ~ F.E.eq x x'.
    Proof.
      intros.
      red. intros. apply H0.
      apply F.In_1 with x; auto.
    Qed.
    
    (* push to FSetAddEq.v *)
    Theorem In_remove_neq :
      F.In x (F.remove x' A) -> ~ F.E.eq x x'.
    Proof.
      intros.
      red; intros.
      apply F.E.eq_sym in H0.
      eapply F.remove_1. apply H0. apply H.
    Qed.

  End add.

  Section remove.

    Theorem Add_remove_Equal: forall edge A A',
      Properties.Add edge A A' -> ~ F.In edge A -> F.Equal A (F.remove edge A').
    Proof.
      intros.
      split; intros.
      generalize (In_nIn_neq _ _ _ H1 H0); intros Hneq.
      apply F.remove_2; auto.
      generalize (H a); intros Hadd; destruct Hadd.
      apply H3; auto.
      (* converse *)
      intros.
      generalize (In_remove_neq _ _ _ H1); intros Hneq.
      generalize (F.remove_3 H1); intros HinA'.
      generalize (H a); intros Hadd; destruct Hadd.
      apply H2 in HinA'.
      destruct HinA'; auto.
      red in Hneq.
      generalize (F.E.eq_sym H4). intros; auto.
      apply Hneq in H5.
      contradiction.
    Qed.

  End remove.

  Section union.
   (* This might have been proved using AGAddEq.Subset_fold_add_Equal,
      instantiating (AG.fold AG.add B A) for (AG.union A (AG.diff B A)),
      but this would still require induction to prove *)

   Theorem subset_union_diff : forall A B, F.Subset A B -> 
     F.Equal B ((fun A => (F.union A (F.diff B A))) A).
   Proof.
     intros.
     eapply F.eq_trans;[ eapply F.eq_sym;eapply Properties.diff_inter_all |].
     rewrite Properties.inter_sym;
       rewrite Properties.inter_subset_equal; [rewrite Properties.union_sym; apply F.eq_refl|eauto].
   Qed.

   Hint Resolve subset_union_diff.
 End union.

  Section Add_Eq_eq.

    Theorem Add_neq_iff x x' A B: ~ F.E.eq x x' -> Properties.Add x A B ->
      (F.In x' B <-> F.In x' A).
    Proof.
      intros.
      generalize (H0 x'); intros.
      intuition.
    Qed.

    Theorem Add_neq_iff2 x x' A A' B B' : 
      ~ F.E.eq x x' ->
      F.Equal A A' -> F.Equal B B' ->
      Properties.Add x A B -> (F.In x' B' <-> F.In x' A).
    Proof.
      intros.
      generalize (H2 x'); intros.
      generalize (H0 x'); intros.
      generalize (H1 x'); intros.
      intuition.
    Qed.
      
    
    Theorem double_add_eq A A' B B' x x': ~ F.In x A -> 
      F.Equal A A' -> F.Equal B B' ->
      Properties.Add x A B -> Properties.Add x' A' B' -> 
        F.E.eq x x'.
    Proof.
      intros.
      case (F.E.eq_dec x x'); intros; auto.
      assert (~ F.E.eq x' x); auto.
      case (Properties.In_dec x B'); intros.
      (* In x B' *)
      generalize (Add_neq_iff _ _ _ _ H4 H3); intros.
      destruct H5.
      generalize (H0 x); intros H7; destruct H7.
      intuition.
      (* ~ In x B' *)
      generalize (Add_neq_iff _ _ _ _ H4 H3); intros.
      generalize (H1 x); intros.
      generalize (H2 x); intros.
      generalize (F.E.eq_refl x); intros.
      intuition.
    Qed.

  End Add_Eq_eq.
  
  Section fold.

    Theorem subset_fold_subset: forall A A',
      F.Subset A A' -> F.Subset (F.fold F.add A' A) A'.
    Proof.
      intros A A' Hsub.
      eapply Properties.fold_rec_bis with 
        (P:= fun (s a :F.t) => (F.Subset a A'));
 intros.
      (* equiv *)
      eauto.
      (* base *)
      eauto.
      (* step *)
      eapply Properties.subset_add_3; auto.
    Qed.

    Hint Resolve subset_fold_subset.
 
  (* problem, that proof was not dependent *)

    Theorem subset_fold_add_subset_2: forall A A',
      F.Subset A A' -> F.Subset A' (F.fold F.add A' A).
    Proof.
      intros A A' Hsub.
      eapply Properties.fold_rec_bis with 
        (P:= fun (s a :F.t) => F.Subset s a);
 intros.
      (* equiv *)
      eapply F.eq_sym in H.
      eapply Properties.subset_equal in H.
      eapply Properties.subset_trans; eauto.
      (* base *)
      eapply Properties.subset_empty.
      (* step *)
      intros y Hin.
      generalize (Properties.Add_add s' x y); intros [Hadd HAdd'].
      apply Hadd in Hin; clear Hadd HAdd'; destruct Hin as [Hin | Hin'];
      Facts.set_iff; eauto.
    Qed.

    Hint Resolve subset_fold_add_subset_2.

    Theorem subset_fold_add_Equal: forall A A', 
      F.Subset A A' -> F.Equal (F.fold F.add A' A) A'.
    Proof.
      intros A A' Hsub.
      eapply Properties.subset_antisym; eauto.
    Qed.

  End fold.

  Theorem is_empty_add : forall x s,
    F.is_empty (F.add x s) = false.
  Proof.
    intros.
    case (sumbool_of_bool (F.is_empty (F.add x s))); intros Hnot; auto.
    eapply Facts.is_empty_iff in Hnot.
    unfold F.Empty in *.
    generalize (Properties.Add_add s x x); intros [_ Hadd].
    eapply Hnot in Hadd; try contradiction; try auto.
  Qed.

  Theorem double_add : forall x s,
    F.Equal (F.add x (F.add x s)) (F.add x s).
  Proof.
    intros.
    intro; split; intro.

    apply Facts.add_iff in H; destruct H; auto.
    apply Facts.add_iff; left; auto.

    apply Facts.add_iff; right; auto.
  Qed.

End Make.