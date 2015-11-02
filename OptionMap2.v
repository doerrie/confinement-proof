Require Import RelationClasses.

Definition option_map2 (A B:Type) (f2: A -> A -> B) (f1: A -> B) (f0:B) o1 o2 :=
match o1 with 
  | None => 
    match o2 with
      | None => f0
      | Some a2 => (f1 a2)
    end
  | Some a1 => 
    match o2 with
      | None => (f1 a1)
      | Some a2 => (f2 a1 a2)
    end
end.

Implicit Arguments option_map2 [A B].

Definition option_map_eq (A:Type) (eq: A -> A -> Prop) o1 o2 :=
  option_map2 eq (fun _ => False) True o1 o2.

Implicit Arguments option_map_eq [A].

Theorem option_map_eq_refl : forall A Aeq (EQUIV: Equivalence Aeq) (o: option A),
  option_map_eq Aeq o o.
  Proof.
    intros.
    unfold option_map_eq in *; unfold option_map2 in *.
    destruct o; auto.
    apply reflexivity; auto.
  Qed.

Theorem option_map_eq_symmetric: forall A Aeq (EQUIV: Equivalence Aeq) (o1 o2: option A),
  option_map_eq Aeq o1 o2 ->   option_map_eq Aeq o2 o1.
  Proof.
    intros.
    unfold option_map_eq in *; unfold option_map2 in *.
    destruct o1; destruct o2; auto.
    apply symmetry; auto.
  Qed.

Theorem option_map_eq_transitive:  forall A Aeq (EQUIV: Equivalence Aeq) (o1 o2 o3: option A),
  option_map_eq Aeq o1 o2 -> option_map_eq Aeq o2 o3 -> option_map_eq Aeq o1 o3.
  Proof.
    intros.
    unfold option_map_eq in *; unfold option_map2 in *.
    destruct o1; destruct o2; destruct o3; auto.
    apply transitivity with a0; auto.
    contradiction.
  Qed.

Theorem option_map_eq_Equiv: forall A (eqA:A->A->Prop) (EqA: Equivalence eqA), 
  Equivalence (option_map_eq eqA).
Proof.
  intros.
  eapply Build_Equivalence.
  unfold Reflexive; apply option_map_eq_refl; auto.
  unfold Symmetric; apply option_map_eq_symmetric; auto.
  unfold Transitive; apply option_map_eq_transitive; auto.
Qed.

Implicit Arguments option_map_eq_Equiv [A].

Theorem option_map_eq_dec: forall A (eqA: A->A->Prop)
  (Hdec: forall a1 a2, {eqA a1 a2} + {~ eqA a1 a2}),
  forall o1 o2, {option_map_eq eqA o1 o2} + {~ option_map_eq eqA o1 o2}.
Proof.
  intros.
  destruct o1 as [a1|]; destruct o2 as [a2|]; simpl; intuition.
Qed.

Implicit Arguments option_map_eq_dec [A eqA].

Definition option_map1 (A B:Type) (f1:A -> B) (f0:B) o :=
  match o with
    | None => f0
    | Some a => f1 a
  end.

Implicit Arguments option_map1 [A B].

Theorem option_map_is_option_map1 :
  forall (A B:Type) (a:option A) (f:A->B),
    option_map f a = option_map1 (fun a => Some (f a)) None a.
Proof.
  auto.
Qed.

(* we need a version of this that has op and op' *)

(* Definition option_map1_compat_op A B eqA eqB  *)
(*   (EqA: Equivalence eqA) (EqB:Equivalence eqB) (op: A -> B) : Prop :=  *)
(*   forall a a', eqA a a' -> eqB (op a) (op a'). *)

(* Implicit Arguments option_map1_compat_op [A B]. *)

(* Theorem option_map1_Equiv A B eqA eqB EqA EqB op  *)
(*   (compat_op: @option_map1_compat_op A B eqA eqB EqA EqB op): *)
(*   forall base, @option_map1_compat_op (option A) B (option_map_eq eqA) eqB  *)
(*     (option_map_eq_Equiv eqA EqA) EqB (option_map1 op base). *)
(* Proof. *)
(*   intros. *)
(*   unfold option_map1_compat_op in *. *)
(*   intros. *)
(*   unfold option_map1. *)
(*   destruct EqB. *)
(*   destruct a; destruct a'; auto; contradiction. *)
(* Qed.   *)

Definition option_map1_compat_op A B eqA eqB 
  (EqA: Equivalence eqA) (EqB:Equivalence eqB) (op op': A -> B) : Prop := 
  forall a a', eqA a a' -> eqB (op a) (op' a').

Implicit Arguments option_map1_compat_op [A B].

Theorem option_map1_Equiv A B eqA eqB EqA EqB op op' 
  (compat_op: @option_map1_compat_op A B eqA eqB EqA EqB op op'):
  forall base base', eqB base base' ->
    @option_map1_compat_op (option A) B (option_map_eq eqA) eqB 
    (option_map_eq_Equiv eqA EqA) EqB (option_map1 op base) (option_map1 op' base').
Proof.
  intros.
  unfold option_map1_compat_op in *.
  intros.
  unfold option_map1.
  destruct EqB.
  destruct a; destruct a'; auto; contradiction.
Qed.  

Implicit Arguments option_map1_Equiv [A B].

