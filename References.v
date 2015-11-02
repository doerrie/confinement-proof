(** A definition of reference type.

Reference types must be satisfied as designators for objects.
Therefore they must subtype DecidableType.
Currently, we are using that definition and leave it as a placeholder for future refinement.

**)

Require Import OrderedType.
Require Import OrderedInclude.

Module Type ReferenceType := UsualOrderedTypeWithHints.

Module ReferenceTypeFacts := OrderedTypeFacts.
