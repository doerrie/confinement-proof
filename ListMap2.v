Require Import Coq.Program.Equality.
Require Import RelationClasses.
Require Import List.

Fixpoint triple_list_fix A (l1 l2 l3: list A) {struct l1} : Prop :=
  match l1 with
    | nil =>
      match l2 with
        | nil => 
          match l3 with
            | nil => True
            | cons _ _ => False
          end
        | cons _ _ => False
      end
    | cons _ l1 =>
      match l2 with
        | nil => False
        | cons _ l2 => 
          match l3 with
            | nil => False
            | cons _ l3 => triple_list_fix _ l1 l2 l3
          end
      end
  end.

Implicit Arguments triple_list_fix [A].

Functional Scheme triple_list_fix_ind := Induction for triple_list_fix Sort Prop.
Functional Scheme triple_list_fix_rec := Induction for triple_list_fix Sort Set.
Functional Scheme triple_list_fix_rect := Induction for triple_list_fix Sort Type.

Inductive triple_list_inductive A : list A -> list A -> list A -> Type :=
| triple_list_inductive_nil: triple_list_inductive A nil nil nil
| triple_list_inductive_cons: forall h1 h2 h3 t1 t2 t3,
  triple_list_inductive A t1 t2 t3 ->
  triple_list_inductive A (h1 :: t1) (h2 :: t2) (h3 :: t3).

Implicit Arguments triple_list_inductive [A].

Theorem triple_list_fix_exists_manual: forall A (l1 l2 l3: list A),
  length l1 = length l2 -> length l2 = length l3 -> triple_list_fix l1 l2 l3.
Proof.
  intros A l1 l2 l3.
  functional induction (triple_list_fix l1 l2 l3); intros.
  auto.
  discriminate H0.
  discriminate H.
  discriminate H.
  discriminate H0.
  simpl in H. simpl in H0. 
  apply eq_add_S in H. apply eq_add_S in H0. 
  apply IHP. assumption. assumption.
Qed.

Theorem triple_list_fix_triple_list_ind :forall A (l1 l2 l3: list A),
  triple_list_fix l1 l2 l3 -> triple_list_inductive l1 l2 l3.
Proof.
  intros A l1 l2 l3.
  functional induction (triple_list_fix l1 l2 l3); intros.
  constructor.
  contradiction.
  contradiction.
  contradiction.
  contradiction.
  constructor. apply IHP. assumption.
Qed. 

Theorem triple_list_inductive_exists_manual: forall A (l1 l2 l3: list A),
  length l1 = length l2 -> length l2 = length l3 -> triple_list_inductive l1 l2 l3.
Proof.
  intros.
  apply triple_list_fix_triple_list_ind.
  apply triple_list_fix_exists_manual; assumption.
Qed.

Inductive list_eq_inductive A eqA : list A -> list A -> Prop:=
| list_eq_inductive_nil: list_eq_inductive A eqA nil nil
| list_eq_inductive_cons: forall h h' t t', 
  eqA h h' ->
  list_eq_inductive A eqA t t'->
  list_eq_inductive A eqA (cons h t) (cons h' t').

Implicit Arguments list_eq_inductive [A].

Hint Constructors list_eq_inductive.


Theorem list_eq_inductive_refl: forall A eqA (EqA:Equivalence eqA) (l : list A),
  list_eq_inductive eqA l l.
Proof.
  intros.
  induction l; auto; firstorder.
Qed.

Theorem list_eq_inductive_sym: forall A eqA (EqA:Equivalence eqA) (l1 l2: list A),
  list_eq_inductive eqA l1 l2 -> list_eq_inductive eqA l2 l1.
Proof.
  intros.
  induction H; auto; firstorder.
Qed.

Theorem list_eq_inductive_trans: forall A eqA (EqA:Equivalence eqA) (l1 l2 l3: list A),
  list_eq_inductive eqA l1 l2 ->
  list_eq_inductive eqA l2 l3 ->
  list_eq_inductive eqA l1 l3.
Proof.
  intros A eqA EqA l1 l2 l3.
  functional induction (triple_list_fix l1 l2 l3); intros.
  constructor.
  inversion H0.
  inversion H.
  inversion H.
  inversion H0.
  inversion H; inversion H0.
  constructor.
  destruct EqA as [_ _ trans]; apply trans with _x0; assumption.
  apply IHP; assumption.
Qed.


Fixpoint list_eq_alt A eqA (l1 l2 : list A) {struct l1} : Prop:=
  match l1 with
    | nil => 
      match l2 with
        | nil => True
        | cons h2 t2 => False
      end
    | cons h1 t1 =>
      match l2 with
        | nil => False
        | cons h2 t2 => (eqA h1 h2) /\ (list_eq_alt A eqA t1 t2)
      end
  end.

Implicit Arguments list_eq_alt [A].

Theorem list_eq_inductive_imp_list_eq_alt:
  forall A (eqA : A -> A -> Prop) l1 l2,
    list_eq_inductive eqA l1 l2 -> list_eq_alt eqA l1 l2.
Proof.
  intros.
  induction H; simpl; auto; split; auto.
Qed.

Theorem list_eq_alt_imp_list_eq_inductive:
  forall A (eqA : A -> A -> Prop) l1 l2,
    list_eq_alt eqA l1 l2 -> list_eq_inductive eqA l1 l2.
Proof.
  intros A eqA.
  double induction l1 l2; intros.
  constructor.
  red in H0; simpl in H0; contradiction.
  red in H1; simpl in H1; contradiction.
  constructor.
  red in H2; simpl in H2; destruct H2 as [H2 H3]; auto.
  red in H2; simpl in H2; destruct H2 as [H2 H3].
  fold list_eq_alt in H3.
  destruct l3.
  destruct l0; firstorder; constructor.
  apply (H0 H a2 l3 H3).
Qed.

Hint Resolve list_eq_alt_imp_list_eq_inductive list_eq_inductive_imp_list_eq_alt.

Theorem list_eq_alt_iff_list_eq_inductive:
  forall A (eqA : A -> A -> Prop) l1 l2,
    (list_eq_alt eqA l1 l2 <-> list_eq_inductive eqA l1 l2).
Proof.
  intros; split; intros; auto.
Qed.

Theorem list_eq_alt_len_eq : forall A (eqA : A -> A -> Prop) (l1 l2: list A),
  list_eq_alt eqA l1 l2 -> List.length l1 = List.length l2.
Proof.
  intros A eqA.
  double induction l1 l2; intros; firstorder.
  simpl.
  destruct l3.
  destruct l0; auto.
  simpl in H3; contradiction.
  rewrite (H0 a2 l3 H3); trivial.
Qed.


(* find this theorem's name *)
Theorem nat_neq: forall n:nat,
  S n <> n.
Proof.
  auto.
Qed.

Theorem list_eq_inductive_neq: forall A eqA (EqA:Equivalence eqA) (l: list A) (a:A),
  ~ list_eq_inductive eqA (a :: l) l.
Proof.
  intros.
  intro.
  apply list_eq_alt_iff_list_eq_inductive in H.
  generalize (list_eq_alt_len_eq _ _ _ _ H); intros H0.
  simpl in H0.
  apply nat_neq in H0; auto.
Qed.
  
Theorem list_eq_inductive_nil_neq: forall A eqA (EqA:Equivalence eqA) (l: list A) (a:A),
  ~ list_eq_inductive eqA (a :: l) nil.
Proof.
  intros.
  intro.
  apply list_eq_alt_iff_list_eq_inductive in H.
  generalize (list_eq_alt_len_eq _ _ _ _ H); intros H0.
  simpl in H0.
  discriminate H0.
Qed.
  
Theorem list_eq_alt_refl : forall A eqA (EqA: Equivalence eqA) (l: list A),
  list_eq_alt eqA l l.
  Proof.
    intros.
    induction l; simpl; auto.
    split; intuition.
  Qed.

Theorem list_eq_alt_symmetric: forall A eqA (EqA: Equivalence eqA) (l1 l2: list A),
  list_eq_alt eqA l1 l2 -> list_eq_alt eqA l2 l1.
  Proof.
    intros.
    apply list_eq_alt_iff_list_eq_inductive in H.
    induction H.
    simpl; auto.
    simpl; split; firstorder.
  Qed.

Fixpoint map2 (A B C:Type) (f2: A -> B -> C) (fa: A -> C) (fb: B -> C) 
  (la : list A) (lb : list B) { struct la } : list C :=
match la with 
  | nil => 
    match lb with
      | nil => nil
      | cons hb tb => cons (fb hb) (map fb tb)
    end
  | cons ha ta => 
    match lb with
      | nil => cons (fa ha) (map fa ta)
      | cons hb tb => cons (f2 ha hb) (map2 A B C f2 fa fb ta tb)
    end
end.

Implicit Arguments map2 [A B C].

Definition list_eq (A:Type) (eq: A -> A -> Prop) l1 l2 := 
  fold_right and True (map2 eq (fun _ => False) (fun _ => False) l1 l2).

Implicit Arguments list_eq [A].

Definition fold_right_compat_op A B eqB (EqB: Equivalence eqB) (f: A -> B -> B) :=
  forall b b', eqB b b' -> forall a, eqB (f a b) (f a b').

Implicit Arguments fold_right_compat_op [A B eqB].

Theorem fold_right_Equiv : forall A B (eqB: B -> B -> Prop) (EqB: Equivalence eqB)
  (f: A -> B -> B),
  fold_right_compat_op EqB f ->
  fold_right_compat_op EqB (fun l b => fold_right f b l) .
Proof.
  unfold fold_right_compat_op.
  intros.
  induction a; simpl; auto. 
Qed.

Theorem list_eq_refl : forall A eqA (EqA: Equivalence eqA) (l: list A),
  list_eq eqA l l.
  Proof.
    intros.
    unfold list_eq in *; unfold map2 in *.
    induction l; simpl; auto.
    split; intuition.
  Qed.

Theorem list_eq_symmetric: forall A eqA (EqA: Equivalence eqA) (l1 l2: list A),
  list_eq eqA l1 l2 -> list_eq eqA l2 l1.
  Proof.
    unfold list_eq; unfold map2; intros A eqA EqA.
    double induction l1 l2; intros; simpl; auto.
    simpl in *.
    destruct H2.
    split; [intuition auto|].
    fold map2 in *.
    intuition.
    destruct l3; destruct l0; simpl;
      try trivial; split; auto; firstorder.
  Qed.


Theorem list_eq_transitive:  forall A eqA (EqA: Equivalence eqA) (l1 l2 l3: list A),
  list_eq eqA l1 l2 -> list_eq eqA l2 l3 -> list_eq eqA l1 l3.
  Proof.
    intros A eqA EqA l1 l2 l3.
    functional induction (triple_list_fix l1 l2 l3); intros.
    unfold list_eq. simpl. trivial.
    unfold list_eq in *. simpl in *. destruct H0. contradiction.
    unfold list_eq in *. simpl in *. destruct H; contradiction.
    unfold list_eq in *; simpl in *. destruct H; contradiction.
    unfold list_eq in *; simpl in *. destruct H0; contradiction.
    unfold list_eq in *; simpl in *. destruct H; destruct H0.
    split.
    destruct EqA as [_ _ trans]; apply trans with _x0; assumption.
    apply IHP; assumption.
  Qed.

Theorem list_eq_Equiv: forall A (eqA: A -> A -> Prop) (EqA: Equivalence eqA), 
  Equivalence (list_eq eqA).
  intros.
  apply Build_Equivalence.
  unfold Reflexive; intros; apply list_eq_refl; assumption.
  unfold Symmetric; intros; apply list_eq_symmetric; assumption.
  unfold Transitive; intros x y z; intros; apply list_eq_transitive with y; assumption.
Qed.

