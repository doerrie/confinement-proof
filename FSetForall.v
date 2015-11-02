Require Import FSets.
Require Import SetoidList.
Require Import Sumbool_dec.
Require Import OrderedTypeEquiv.

Module makeForall (FS:FSetInterface.S).
  
  Module FSEquivM := OT_Equiv FS.
  Definition FSEquiv := FSEquivM.Equiv.
  Module ElemEquivM := OT_Equiv FS.E.
  Definition ElemEquiv := ElemEquivM.Equiv.

  Theorem for_all_prop_1: forall P s (SB: forall e, {P e}+{~ P e}), compat_P FS.E.eq P -> 
    FS.For_all P s -> FS.for_all (fun e => true_bool_of_sumbool (SB e)) s = true.
  Proof.
    intros.
    apply FS.for_all_1.
    apply compat_P_compat_bool_true_bool_of_sumbool; try exact ElemEquiv; auto.
    unfold FS.For_all in *.
    intros.

    unfold true_bool_of_sumbool.
    apply proof_r_true_bool_of_sumbool.
    auto.
  Qed.

  Theorem for_all_prop_2: forall P s (SB: forall e, {P e}+{~ P e}), compat_P FS.E.eq P -> 
    FS.for_all (fun e => true_bool_of_sumbool (SB e)) s = true -> FS.For_all P s.
  Proof.
    intros.
    unfold true_bool_of_sumbool in *.
    apply FS.for_all_2 in H0; try apply compat_P_compat_bool_true_bool_of_sumbool; try exact ElemEquiv; auto.
    unfold FS.For_all in *.
    intros.
    generalize (H0 x H1); intros H2.
    case (SB x); intros Hsb; auto.
    rewrite (proof_l_true_bool_of_sumbool _ (SB x) Hsb) in *.
    discriminate.
  Qed.

  Theorem For_all_dec: forall P s (SB: forall e, {P e}+{~ P e}), compat_P FS.E.eq P ->
    {FS.For_all P s} + {~ FS.For_all P s}.
  Proof.
    intros.
    case (bool_dec (FS.for_all (fun e : FS.elt => true_bool_of_sumbool (SB e)) s) true); intros Hforall;
      [left; apply for_all_prop_2 with (SB:=SB); auto
        |right; intro; apply Hforall; apply for_all_prop_1 with (SB:=SB); auto].
  Qed.

  Theorem forall_iff_dec: forall P s (SB: forall e, {P e}+{~ P e}), compat_P FS.E.eq P ->
    {forall e, FS.In e s <-> P e} + {~ (forall e, FS.In e s <-> P e)}.
  Proof.
    intros.
    (* I should be able to use For_all_dec to build a sumbool with P := In e s <-> P' e from a sumbool P'.  *)
    (* Then the rest should be easy *)
    case (bool_dec (FS.for_all (fun e : FS.elt => true_bool_of_sumbool (SB e)) s) true); intros Hforall;
      [left; apply for_all_prop_2 with (SB:=SB); auto
        |right; intro; apply Hforall; apply for_all_prop_1 with (SB:=SB); auto].
  Qed.

End makeForall.