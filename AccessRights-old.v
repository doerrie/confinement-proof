Require Import FSets.
Require Import S_as_OT.

Inductive accessRight : Set :=
| weak : accessRight
| read : accessRight
| write : accessRight
| send : accessRight.

(* This defines a stepwise ordering on accessRights *)

  Inductive accessRight_succ : accessRight -> accessRight -> Prop :=
  | succ_weak_read : accessRight_succ weak read
  | succ_read_write : accessRight_succ read write
  | succ_write_send : accessRight_succ write send.

  Hint Constructors accessRight_succ: caps.

  Hint Resolve (f_equal accessRight_succ) : caps.

(* The successor of n is not equal to n *)

  Theorem accessRight_succ_neq : forall n Sn, accessRight_succ n Sn -> n <> Sn. 
  Proof.
    intros n Sn H.
    destruct H; discriminate.
  Qed.

  Hint Immediate accessRight_succ_neq : caps.

(* Weak is not the successor of anything *)

  Theorem accessRight_succ_weak : forall n, ~ accessRight_succ n weak.
  Proof.
    intros n H.
    inversion H.
  Qed.

  Hint Resolve accessRight_succ_weak : caps.

(* Nothing is the successor of send *)

  Theorem accessRight_succ_send : forall n, ~ accessRight_succ send n.
  Proof.
    intros n H.
    inversion H.
  Qed.

  Hint Resolve accessRight_succ_send : caps.

(* Successor is not reflexive *)

  Theorem accessRight_succ_n_n : forall n, ~ accessRight_succ n n.
  Proof.
    intros n H.
    destruct n;
      inversion H.
  Qed.

  Hint Resolve accessRight_succ_n_n : caps.

(* Successor is not symmetric *)

  Theorem accessRight_succ_neq_succ : forall a b, accessRight_succ a b -> ~ accessRight_succ b a.
  Proof.
    intros a b S H.
    inversion S; subst; inversion H.
  Qed.

(* Define an order using successor *)

  Inductive accessRight_le : accessRight -> accessRight -> Prop :=
  | le_base : forall x, accessRight_le x x
  | le_trans : forall x y z, accessRight_le x y -> accessRight_succ y z -> accessRight_le x z.

  Hint Constructors accessRight_le : caps.

  Hint Resolve (f_equal accessRight_le) : caps.

(* accessRight_le is transitive *)

  Theorem accessRight_le_trans : forall x y z, accessRight_le x y -> accessRight_le y z -> accessRight_le x z.
  Proof.
    intros.
    induction H0; firstorder.  apply (le_trans x y z); assumption.
  Qed.

  Hint Resolve accessRight_le_trans: caps.

(* accessRight_le is reflexive *)

  Theorem accessRight_le_refl : forall x, accessRight_le x x.
  Proof.
    auto with caps.

(*
    intros. exact (le_base x).
*)
  Qed.

(** modeled from Coq.Arith.Le **)

(* Weak is less than everything *)

  Theorem accessRight_le_weak_n : forall n, accessRight_le weak n.
  Proof.
    induction n;
      eauto with caps.
(*    
    apply le_trans with weak; constructor.
    apply le_trans with read; try constructor.
    apply le_trans with weak; constructor.
    apply le_trans with write; try constructor.
    apply le_trans with read; try constructor.
    apply le_trans with weak; constructor.
    constructor.
*)
  Qed.

  Hint Resolve accessRight_le_weak_n : caps.

(* The successor of anything is not less than weak *)

  Theorem accessRight_le_Sn_weak : forall n Sn, accessRight_succ n Sn -> ~ accessRight_le Sn weak.
  Proof.
    intros n Sn S.
    red.
    intro H.
    change ((fun r =>
      match r with
        | weak => False
        | read => True
        | write => True
        | send => True
      end) weak).
    induction H.
    destruct S; trivial.
    destruct H0; trivial.
  Qed.

  Hint Resolve accessRight_le_Sn_weak : caps.

(* Only weak is less than weak *)

  Theorem accessRight_le_n_weak_eq : forall n, accessRight_le n weak -> weak = n .
  Proof.
    intros n H.
    inversion H; 
      [trivial
        | absurd (accessRight_succ y weak); eauto with caps] .
  Qed.

  Hint Immediate accessRight_le_n_weak_eq : caps.

(* The successor of n is not less than n *)

  Theorem accessRight_le_Sn_n : forall n Sn, accessRight_succ n Sn -> ~ accessRight_le Sn n.
  Proof.
    intros n p S.
    induction S; eauto with caps; intro ; inversion H ; subst;
      inversion H1 ; subst ; inversion H0 ; subst.
    absurd (accessRight_succ y weak); eauto with caps.
    inversion H3; subst.  inversion H2; subst.
    absurd (accessRight_succ y weak); eauto with caps.
  Qed.
  Hint Resolve accessRight_le_Sn_n : caps.

  Theorem accessRight_le_n_S : forall n m Sn Sm, 
    accessRight_succ n Sn -> accessRight_succ m Sm -> accessRight_le n m -> accessRight_le Sn Sm.
  Proof.
    intros.
    inversion H; subst; inversion H0; subst; firstorder; eauto with caps.
    absurd (accessRight_le read weak); eauto with caps.
    absurd (accessRight_le write weak); eauto with caps.
    absurd (accessRight_le write read); eauto with caps.
  Qed.

  Theorem accessRight_le_Sn_le : forall n m Sn Sm, 
    accessRight_succ n Sn -> accessRight_succ m Sm -> accessRight_le Sn Sm -> accessRight_le n m.
  Proof.
    intros n m Sn Sm S S1 H.
    inversion S; inversion S1; subst; eauto with caps.
    inversion H; subst.  inversion H1; subst.  inversion H0; subst; contradiction accessRight_succ_weak with y.
    inversion H; subst.  inversion H1; subst.  inversion H0; subst. contradiction accessRight_succ_weak with y.
    inversion H; subst.  inversion H1; subst.  inversion H0; subst.
    inversion H3; subst.  inversion H2; subst.  contradiction accessRight_succ_weak with y.
  Qed.

  Hint Resolve accessRight_le_Sn_le : caps.

  Theorem accessRight_le_n_Sn : forall n p, accessRight_succ n p -> accessRight_le n p.
  Proof.
    eauto with caps.
  Qed.

  Hint Resolve accessRight_le_n_Sn : caps.

  Theorem accessRight_le_pred_n : forall n Sn m,
    accessRight_succ n Sn -> accessRight_le Sn m -> accessRight_le n m.
  Proof.
    intros n Sn m H. apply accessRight_le_trans. eauto with caps.
  Qed.

  Hint Immediate accessRight_le_pred_n: caps.

  Theorem accessRight_le_not_Sn : forall n Sn m,
    accessRight_succ n Sn -> ~ accessRight_le n m -> ~ accessRight_le Sn m.
  Proof.
    intros n Sn m S H.
    inversion S; subst; eauto with caps.
  Qed.

  Hint Resolve accessRight_le_not_Sn : caps.

  Theorem accessRight_le_not_n_Sn : forall n Sn m,
    accessRight_succ n Sn -> ~ accessRight_le m Sn -> ~ accessRight_le m n.
  Proof.
    intros n Sn m S H.
    eauto with caps.
  Qed.

  Hint Resolve accessRight_le_not_n_Sn : caps.

(* If n is less than m, m is not the successor of n *)

  Theorem accessRight_le_succ : forall n m,
    accessRight_le n m -> ~ accessRight_succ m n.
  Proof.
    intros n m H.
    inversion H as [| x pred_m z H0 H1]; subst; eauto with caps.
    inversion H1; subst.
    inversion H0; subst;  intro NOT;  inversion NOT; subst.  contradiction accessRight_succ_weak with y.
    inversion H0; subst.  intro NOT; inversion NOT.  inversion H3; subst.  inversion H2; subst.  intro NOT.  inversion NOT.
    contradiction accessRight_succ_weak with y.
    inversion H0; subst.  intro NOT; inversion NOT; subst.  inversion H3; subst.  inversion H2; subst.  intro NOT.  inversion NOT.
    inversion H5; subst.  inversion H4; subst.  intro NOT; inversion NOT.  contradiction accessRight_succ_weak with y.  
  Qed.

  Hint Resolve accessRight_le_succ : caps.

  Theorem accessRight_le_antisym : forall x y, accessRight_le x y -> accessRight_le y x -> x = y.
  Proof.
    intros x y H H0.
    inversion H as [| x' pred_y z H1 H2]; subst; eauto with caps.
    absurd (accessRight_le y x); eauto with caps.
    apply accessRight_le_Sn_n in H2.
    eauto with caps.
  Qed.

  Hint Resolve accessRight_le_antisym : caps.

  Theorem accessRight_succ_neq_trans : forall n Sn SSn,
    accessRight_succ n Sn -> accessRight_succ Sn SSn -> n <> SSn.
  Proof.
    intros n Sn SSn S S1.
    inversion S; subst; inversion S1; subst; discriminate.
  Qed.

  Hint Resolve accessRight_succ_neq_trans : caps.

  Inductive accessRight_lt (n m :accessRight) : Prop :=
  | accessRight_lt_le : forall Sn, accessRight_succ n Sn -> accessRight_le Sn m -> accessRight_lt n m.

  Hint Constructors accessRight_lt : caps.

  Theorem accessRight_lt_trans : forall n m p,
    accessRight_lt n m -> accessRight_lt m p -> accessRight_lt n p.
  Proof.
    intros n m p H H0; inversion H0 as [Sm]; subst; inversion H as [Sn]; subst; constructor 1 with Sn; eauto with caps.
  Qed.

  Hint Resolve accessRight_lt_trans : caps.

  Theorem accessRight_lt_irrefl : forall n,  ~ accessRight_lt n n.
  Proof.
    intros n H.
    destruct H.
    contradiction accessRight_le_Sn_n with n Sn.
  Qed.

  Hint Resolve accessRight_lt_irrefl : caps.

  Theorem accessRight_lt_not_eq: forall n m,
    accessRight_lt n m -> n <> m.
    intros n m Hlt.
    destruct Hlt as [Sn S Hle].
    destruct S. 
    destruct m ; try discriminate ; inversion Hle; subst; contradiction accessRight_succ_weak with y . 
    destruct m ; try discriminate ; inversion Hle; subst; inversion H0; subst; inversion H; subst; contradiction accessRight_succ_weak with y . 
    destruct m ; try discriminate ; inversion Hle; subst. inversion H0; subst. inversion H; subst.  inversion H2; subst.     inversion H1; subst. contradiction accessRight_succ_weak with y . 
  Qed.

  Hint Resolve accessRight_lt_not_eq : caps.

  Theorem accessRight_lt_eq_lt_dec n m :
    {accessRight_lt n m} + {n = m} + {accessRight_lt m n}.
  Proof.
    intros.
    destruct n; destruct m; eauto with caps. 
  Qed.

  Theorem accessRight_eq_dec: forall n m:accessRight, {n = m} + {n <> m}.
  Proof.
    intros.
    induction n; destruct m; auto;
    (* all that remains are the <> cases *)
      right; simplify_eq.
  Qed.    

Module AccessRight_as_UOT <: UsualOrderedType.
  
  Definition t := accessRight.

  Definition eq := @eq accessRight.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec := accessRight_eq_dec.

  Definition lt := accessRight_lt.

  Definition lt_trans := accessRight_lt_trans.

  Definition lt_not_eq := accessRight_lt_not_eq.

  Theorem compare : forall x y : t, Compare lt eq x y. 
  Proof.
    unfold t, lt.
    intros.
    case (accessRight_lt_eq_lt_dec x y).
    intro s.  destruct s as [a|a].
    exact (LT eq a).
    exact (EQ accessRight_lt a).
    intro a.
    exact (GT eq a).
  Qed.

Hint Unfold eq : caps.
Hint Unfold lt : caps.

End AccessRight_as_UOT.

Module AccessRightOT <: OrderedType := AccessRight_as_UOT.

Module AccessRightFSetList := FSetList.Make AccessRightOT.

Module Type AccessRightFSetType := FSetInterface.S with Module E := AccessRightOT.

Module AccessRightFSet : AccessRightFSetType := AccessRightFSetList.

Definition accessRightSet := AccessRightFSet.t.

Hint Immediate AccessRightFSet.eq_sym : caps.
Hint Resolve AccessRightFSet.eq_refl AccessRightFSet.eq_trans AccessRightFSet.lt_not_eq AccessRightFSet.lt_trans : caps.

Require FSetAddEq.
Require FSetListUOT.
Require FoldEqual.

Module ARSetProps := FSetProperties.Properties AccessRightFSet.
Module ARSetFacts := FSetFacts.Facts AccessRightFSet.
Module ARSetfDep := FSetBridge.DepOfNodep AccessRightFSet.
Module ARSetEqProps := FSetEqProperties.EqProperties AccessRightFSet.
Module ARSetAddEq := FSetAddEq.Make AccessRightFSet.
Module ARSetFold := FoldEqual.Make AccessRightFSet.


Definition all_rights := AccessRightFSet.add read
        (AccessRightFSet.add write
          (AccessRightFSet.add weak
            (AccessRightFSet.singleton send))).
