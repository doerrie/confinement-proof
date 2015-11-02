Require Import Decidable.
Require Import References.
Require Import AccessRights.

Module Type AccessType.


  (* We need a reference type *)
  Declare Module R : ReferenceType.

  Parameter hasAccess: accessRight -> R.t -> R.t -> Prop.

  Parameter hasAccess_dec: forall (r:accessRight) (s t: R.t), decidable (hasAccess r s t).

End AccessType.

(* We offer no minimal implementation in this file, as it is reused for both potential and direct authority *)
(* To demonstrate confinement, subset authority type in your system state. *)
(* Correspondence between all operations that are not allocate should be straightforward by least upper bound *)
(* We will then be left with the allocate operation, wich requires futher reasoning through actual properties *)

