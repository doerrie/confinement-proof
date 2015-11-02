Require Import OrderedType.
Require Import FSetInterface.

Module S_as_OT (s : S) <: OrderedType := s.
Module S_to_OT (s : S) : OrderedType := s.