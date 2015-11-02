(* tauto can handle this proof, but sometimes we just want to step it a bit. *)

Theorem not_iff : forall A B, (A <-> B) -> ~ A -> ~ B.
Proof.
  intros A B Hiff H.
  tauto.
Qed.
