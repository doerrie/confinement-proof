  Theorem option_sumbool A (o: option A) : {o = None} + {exists a, o = Some a}.
  Proof.
    intros.
    destruct o.
    right.
    split with a; auto.
    left.
    auto.
  Qed.

Implicit Arguments option_sumbool [A].