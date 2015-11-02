(* For the time being, we will assume that Lists of ordered types are themselves ordered *)
(* This assumption can be instantiated using standard eq, and a lt that first checks the length of two lists, and then
   compares each element lexicographically. *)

Require Import OrderedType.
Require Import OrderedTypeEx.

Module ListOrderedType (O:OrderedType) <: OrderedType.

  (* Build known OrderedType facts for our given ordered type. *)
  Module MO := OrderedTypeFacts(O).

  (* Define t as a list over this ordered type. *)
  Definition t := list O.t.
  
  Inductive eq : t -> t -> Prop :=
  | eq_nil : eq nil nil
  | eq_cons : forall (a b: O.t) (x y: t), 
    O.eq a b -> eq x y -> eq (cons a x) (cons b y).

  Hint Constructors eq.

  Theorem eq_refl : forall x : t, eq x x.
  Proof.
    unfold t.
    intro.
    induction x; auto.
  Qed.

  Hint Immediate eq_refl.
  
  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    unfold t.
    intros x y H.
    induction H; auto.
  Qed.
  
  Hint Resolve eq_sym.

  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    intros x y z H0 H1.
    induction x.  inversion H0; unfold t in *.  rewrite <- H2 in H1.  assumption.
    inversion H0.  inversion H1. subst.
    
    
    
    

  
  
    
    (* not finished*)
  Qed.

  Hint Resolve eq_trans.
  
  Fixpoint lt (x y: t) {struct x} : Prop :=
    match x,y with
      | nil, (cons b y) => True
      | (cons a x), (cons b y) =>
        O.lt a b \/
        O.eq a b /\ lt x y
      | _,_ => False
    end.

  Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

  Parameter compare : forall x y : t, Compare lt eq x y.

End ListOrderedType.