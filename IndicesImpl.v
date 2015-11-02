Require Import OrderedType.
Require Import OrderedTypeEx.
Require Import Indices.

Module NatIndex <: IndexType := Nat_as_OT.

Module NatIndexFacts := IndexTypeFacts (NatIndex).