Require FSetToFiniteSet.
Require Import Ensembles Finite_sets.
Require Import FSetInterface FSetProperties OrderedTypeEx.

Module S_to_Finite_set (U:UsualOrderedType)(M:S with Module E := U).
  Module STFS := (FSetToFiniteSet.S_to_Finite_set U M).
  Import STFS.


 