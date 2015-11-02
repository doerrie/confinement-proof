Require Import Sumbool.
Require Import SetoidList.
Require Import Decidable.


Section Sumbool_dec.

  Variable P:Prop.
  Hypothesis Pdec: {P}+{~P}.

  Theorem Sumbool_dec_iff_imp: forall A:Prop, (P <->A) -> {A} + {~A}.
  Proof.
    tauto.
  Qed.

      Theorem Sumbool_dec_not: {~ P} + { ~ ~ P}.
      Proof.
        tauto.
      Qed.
      Theorem Sumbool_dec_neg: {~ P} + {P}.
      Proof.
        tauto.
      Qed.

   Theorem Sumbool_decidable:  decidable P.
      Proof.
        case Pdec; intros HP; [left|right]; eauto.
      Qed.

      Theorem Sumbool_dec_not_not_iff: P <-> ~ ~ P.
      Proof.
        intros; split; intros; tauto.
      Qed.



  Variable Q:Prop.
  Hypothesis Qdec: {Q}+{~Q}.

  Theorem Sumbool_dec_and: {P /\ Q} + {~ (P /\ Q) }.
  Proof.
    tauto.
  Qed.

  Theorem Sumbool_dec_or: {P \/ Q} + {~ (P \/ Q)}.
  Proof.
    tauto.
  Qed.

  Theorem Sumbool_dec_imp: {P -> Q} + { ~ (P -> Q) }.
  Proof.
    tauto.
  Qed.

  Theorem Sumbool_dec_iff: {P <-> Q} + {~ (P <-> Q)}.
  Proof.
    tauto.
  Qed.

      Theorem Sumbool_not_and: (~ ( P /\ Q)) <-> (~ P \/ ~ Q).
      Proof.
        intros; tauto.
      Qed.
      Theorem Sumbool_not_or: (~ ( P \/ Q)) <-> (~ P /\ ~ Q).
      Proof.
        intros; tauto.
      Qed.
      Hint Resolve Sumbool_not_and Sumbool_not_or.

      (* TODO, find these somewhere, or place them somewhere *)
      Theorem Sumbool_dec_neg_iff: 
        (P <-> Q) <-> (~ P <-> ~ Q).
      Proof.
        intros; split; intros; try tauto.
      Qed.

   

End Sumbool_dec.

  Definition true_bool_of_sumbool {A} {B} (SB:{A}+{B}) : bool := proj1_sig (bool_of_sumbool SB).

  Theorem true_bool_of_sumbool_l : forall A B (SB:{A}+{B}),
    proj1_sig (bool_of_sumbool SB) = true -> A.
  Proof.
    intros A B SB. 
    generalize (bool_of_sumbool SB). intros Hs Hp.
    case SB; auto.
    intros b.
    generalize (proj2_sig Hs).
    rewrite Hp; auto.
  Qed.

  Theorem true_bool_of_sumbool_r: forall A B (SB:{A}+{B}),
    proj1_sig (bool_of_sumbool SB) = false -> B.
    intros A B SB.
    generalize (bool_of_sumbool SB). intros Hs Hp.
    case SB; auto.
    intros a.
    generalize (proj2_sig Hs).
    rewrite Hp; auto.
  Qed.

  Hint Unfold true_bool_of_sumbool.

  Theorem proof_r_true_bool_of_sumbool: forall A (SB:{A}+{~A}),
    A -> proj1_sig (bool_of_sumbool SB) = true.
  Proof.
    intros.
    destruct SB; auto; contradiction.
  Qed.

  Theorem proof_l_true_bool_of_sumbool: forall A (SB:{A}+{~A}),
    ~A -> proj1_sig (bool_of_sumbool SB) = false.
  Proof.
    intros.
    destruct SB; auto; contradiction.
  Qed.

  Theorem compat_P_compat_bool_true_bool_of_sumbool: forall (A:Type) (R: A -> Prop) eqA (EqA: Equivalence eqA) (SBR: forall a, {R a}+{~ R a}),
    compat_P eqA R -> compat_bool eqA (fun a => true_bool_of_sumbool (SBR a)).
  Proof.
    intros.
    unfold compat_bool.
    unfold compat_P in *.
    intros.
    destruct EqA as [refl sym trans].
    unfold Proper in *; unfold respectful in *.
    intros.
    case (SBR x); intros HcaseX; case (SBR y); intros HcaseY;
      unfold true_bool_of_sumbool; simpl; auto;
    try apply H with (y:=y) in HcaseX; try apply H with (y:=x) in HcaseY; auto; try apply sym; contradiction.
  Qed.


(* These do not require decidable tests, but will be used later *)

      Theorem not_exists_iff {A} {P: A->Prop}:
        (~ exists y, P y) <-> (forall y, ~ P y).
      Proof.
        split; intros H.
        intros y Hnot; apply H; eapply ex_intro; apply Hnot.
        intros [y Hnot]; eapply H; eapply Hnot.
      Qed.

      Theorem not_forall_l {A} {P: A -> Prop}:
        (exists y, ~ P y) -> (~ forall y, P y).
      Proof.
        intros [y H] Hnot; apply H; auto.
      Qed.


(* These quantify the decidability differently than within our section *)

      Theorem Sumbool_dec_forall_not_not_iff: forall A (P:A->Prop) (P_dec:forall x, {P x} + {~ P x}),
        (forall x, P x) <-> (forall x, ~ ~ P x).
      Proof.
        intros; split; intros.
        intro Hnot; apply Hnot; apply H.
        generalize (H x); clear H; intro H.
        apply not_not; auto.
        apply Sumbool_decidable; auto.
      Qed.

      Theorem Sumbool_dec_forall_not_iff {A} {P: A -> Prop} :
        {exists y, ~ P y} + {~ exists y, ~ P y} ->
        (forall y, {P y} + { ~ P y}) ->
        ((forall y, P y) <-> (~ exists y, ~ P y)).
      Proof.
        intros Ex_dec P_dec; split; intros H.
        destruct Ex_dec as [Ex|Ex].
        intros [y Hnot]; eapply Hnot; eapply H; assumption.
        assumption.

        intros y.
        case (P_dec y); intros Hcase; try assumption.
        generalize (ex_intro (fun y => ~ P y) y Hcase); intros H'. contradiction.
      Qed.

      Theorem Sumbool_dec_exists_not_iff {A} {P: A -> Prop} :
        {exists y, P y} + {~ exists y, P y} ->
        ((exists y, P y) <-> (~ forall y, ~ P y)).
      Proof.
        intros Ex_dec; split; intros H.
        destruct H as [y Py].
        intro Hnot. eapply Hnot. apply Py.

        destruct Ex_dec as [Ex|Ex]; try assumption.
        rewrite not_exists_iff in Ex; contradiction.
      Qed.

      Theorem Sumbool_dec_not_forall_r {A} {P: A -> Prop}:
        {exists y, ~ P y} + {~ exists y, ~ P y} ->
        (forall y, {P y} + {~ P y}) ->
        (~ forall y, P y) -> (exists y, ~ P y).
      Proof.
        intros Ex_dec P_dec U.
        destruct Ex_dec as [Ex | Ex]; try solve [assumption].
        rewrite not_exists_iff in Ex; simpl in *.
        rewrite <- Sumbool_dec_forall_not_not_iff in Ex; solve [contradiction|assumption].
      Qed.

      Theorem Sumbool_dec_not_forall_iff {A} {P: A -> Prop}:
        {exists y, ~ P y} + {~ exists y, ~ P y} ->
        (forall y, {P y} + {~ P y}) ->
        ((~ forall y, P y) <-> (exists y, ~ P y)).
      Proof.
        intros; split; intros.
        apply Sumbool_dec_not_forall_r; auto.
        apply not_forall_l; auto.
      Qed.

  Ltac Sumbool_decide :=
    repeat progress
    match goal with
      | [ |- {?P \/ ?Q} + {~ (?P \/ ?Q) } ] => eapply Sumbool_dec_or
      | [ |- {?P /\ ?Q} + {~ (?P /\ ?Q) } ] => eapply Sumbool_dec_and
      | [ |- {?P -> ?Q} + {~ (?P -> ?Q) } ] => eapply Sumbool_dec_imp
      | [ |- {?P <-> ?Q} + {~ (?P <-> ?Q) } ] => eapply Sumbool_dec_iff
      | [ |- {~ ?P } + {~ ~ ?P } ] => eapply Sumbool_dec_not
      | [ |- {~ ?P} + { ?P } ] => eapply Sumbool_dec_neg
    end.
