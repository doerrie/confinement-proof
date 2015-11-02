Require Import Morphisms.
Require Import Basics.

Definition irrel {A} (a b:A) := True.

Hint Unfold irrel.

Theorem Proper_irrel_subst_covariant : forall A B T (F:A -> B -> T) R Q, 
  Proper (irrel ==> R) F -> Proper (Q ==> R) F.
Proof.
  unfold Proper; unfold respectful; unfold flip; intros; eauto.
Qed.

Hint Resolve Proper_irrel_subst_covariant.

Theorem Proper_irrel_subst_contravariant : forall A B T (F:A -> B -> T) R Q,
  Proper (irrel --> R) F -> Proper (Q --> R) F.
Proof.
  unfold Proper; unfold respectful; unfold flip; intros; eauto.
Qed.

Hint Resolve Proper_irrel_subst_contravariant.
  
Theorem Proper_irrel_ignore_covariant : forall B T (F: B -> T) R, 
  Proper R F -> forall A, Proper ((@irrel A) ==> R) (fun _ => F). 
Proof.
  unfold Proper; unfold respectful; unfold flip; intros; eauto.
Qed.

Hint Resolve Proper_irrel_ignore_covariant.

Theorem Proper_irrel_ignore_contravariant : forall B T (F: B -> T) R, 
  Proper R F -> forall A, Proper ((@irrel A) --> R) (fun _ => F). 
Proof.
  unfold Proper; unfold respectful; unfold flip; intros; eauto.
Qed.

Hint Resolve Proper_irrel_ignore_contravariant.