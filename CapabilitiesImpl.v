Require Import Capabilities.
Require Import OrderedTypeEx.
Require Import References.
Require Import AccessRights.
Require Import AccessRightSets.
Require Import Sumbool_dec.
Require Import OrderedType.


Module MakeCapability (Ref : ReferenceType) : CapabilityType Ref.

  Module ARC := PairOrderedType Ref ARSet.
  
  Definition t := ARC.t.
  Definition eq:= @ARC.eq.
  Definition eq_refl := ARC.eq_refl.
  Definition eq_sym := ARC.eq_sym.
  Definition eq_trans := ARC.eq_trans.
  Definition eq_dec := ARC.eq_dec.
  Definition lt:= @ARC.lt.
  Definition lt_trans := @ARC.lt_trans.
  Definition lt_not_eq := @ARC.lt_not_eq.

  Definition compare := @ARC.compare.

  Definition target (cap : t) : Ref.t := (fst cap).

  Definition rights (cap : t) := (snd cap).
  
  Definition mkCap (tgt:Ref.t) (rgts:ARSet.t):= pair tgt rgts.

  Definition weaken c := 
    (mkCap (target c) 
      (if orb (true_bool_of_sumbool (ARSetProps.In_dec wk (rights c)))
        (true_bool_of_sumbool (ARSetProps.In_dec rd (rights c))) 
        then (ARSet.singleton wk) 
        else ARSet.empty)).

  Theorem target_eq: forall c1 c2, eq c1 c2 -> Ref.eq (target c1) (target c2).
  Proof.
    intros.
    unfold eq in H.
    unfold ARC.eq in H.
    destruct H.
    unfold target.
    assumption.
  Qed.

  Theorem rights_eq: forall c1 c2, eq c1 c2 -> ARSet.eq (rights c1) (rights c2).
  Proof.
    intros.
    unfold eq in H.
    unfold ARC.eq in H.
    destruct H.
    unfold rights.
    assumption.
  Qed.

  Theorem target_rights_eq: forall (c1 c2:t), 
    Ref.eq (target c1) (target c2) -> 
    ARSet.eq (rights c1) (rights c2) ->
    eq c1 c2.
  Proof.
    intros.
    unfold eq; unfold ARC.eq.
    split; auto.
  Qed.

  Theorem mkCap_eq: forall tgt rgts c, 
    Ref.eq tgt (target c) /\ ARSet.eq rgts (rights c) <->
    eq (mkCap tgt rgts) c.
  Proof.
    intros; split; intros;
      unfold eq; unfold ARC.eq; auto.
  Qed.

  Theorem weaken_eq: forall c,
    eq (weaken c)
    (mkCap (target c) 
      (if orb (true_bool_of_sumbool (ARSetProps.In_dec wk (rights c)))
        (true_bool_of_sumbool (ARSetProps.In_dec rd (rights c)))
        then (ARSet.singleton wk) 
        else ARSet.empty)).
  Proof.
    intros.
    unfold weaken.
    apply eq_refl.
  Qed.

End MakeCapability.


