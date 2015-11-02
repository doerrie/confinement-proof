Require Import RefSets.
Require Import RefSetsImpl.
Require Import ReferencesImpl.

Module NatRefSet <: RefSetType NatReference := Make NatReference.

