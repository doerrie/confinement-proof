(** A definition of reference type.

Index types must be satisfied as designators for capabilities.
Therefore they must subtype DecidableType.
Currently, we are using that definition and leave it as a placeholder for future refinement.

**)

Require Import OrderedType.
Require Import OrderedInclude.

Module Type IndexType := OrderedType.

Module IndexTypeFacts := OrderedTypeFacts.

