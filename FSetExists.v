Require Import FSets.

Module makeExists (F: FSetInterface.Sdep).

  Import F.

  Theorem exists_' :  forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}) (s : t),
    compat_P E.eq P -> {Exists P s} + {~ Exists P s}.
  Proof.
    intros; generalize (exists_ Pdec s); intros [Hdec|Hdec]; auto.
  Qed.

End makeExists.