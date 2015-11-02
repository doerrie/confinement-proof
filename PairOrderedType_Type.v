Require Import OrderedType.
Require Import OrderedTypeEx.

Module Type PairOrderedType_Type (O1 O2:OrderedType).

 Module MO1:=OrderedTypeFacts(O1).
 Module MO2:=OrderedTypeFacts(O2).

 Definition t := prod O1.t O2.t.

 Definition eq x y := O1.eq (fst x) (fst y) /\ O2.eq (snd x) (snd y).

 Definition lt x y :=
    O1.lt (fst x) (fst y) \/
    (O1.eq (fst x) (fst y) /\ O2.lt (snd x) (snd y)).

 Parameter eq_refl : forall x : t, eq x x.
 
 Parameter eq_sym : forall x y : t, eq x y -> eq y x.

 Parameter eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.

 Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.

 Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

 Parameter compare : forall x y : t, Compare lt eq x y.

 Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.

End PairOrderedType_Type.