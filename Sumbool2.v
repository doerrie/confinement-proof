Require Import Sumbool.

Section Sumbool2.

  Variables A B : Prop.

  Hypothesis Ha : {A} + {~ A}.
  Hypothesis Hb : {B} + {~ B}.

  (* this is just a sanity check *)

  Theorem and_imp (C : Prop) : (A -> B -> C) <-> (A /\ B -> C).
  Proof.
    intros; split; intros; tauto.
  Qed.

  Theorem sumbool_imp : { A -> B } + { ~ (A -> B) }.
  Proof.
    case Hb; case Ha; tauto.
  Qed.
  

End Sumbool2.