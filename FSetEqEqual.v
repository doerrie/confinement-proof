Require Import FSetInterface.
Require Import OrderedType.

Module makeEqual_fun (E:OrderedType) (SF:Sfun E).

  Theorem eq_Equal: forall ag ag',
    SF.eq ag ag' <-> SF.Equal ag ag'.
  Proof.
    intros; split;intros; eapply H.
  Qed.
  Hint Resolve eq_Equal.

End makeEqual_fun.

Module makeEqual (S:S).

  Include (makeEqual_fun S.E S).

End makeEqual.  