Require Import Decidable.
Require Import References.
Require Import AccessRights.
Require Import OrderedTypeEx.
Require AccessEdge.
Require FSets.
Require FSetFacts.
Require FSetEqProperties.
Require Import SequentialAccess.


Module PotentialAccess (RT:ReferenceType).

  Module Seq := SeqAcc RT.
  Definition t := Seq.t.
  Module AG := Seq.AG.
  Module Edge := Seq.Edge.

  Inductive potAcc (i:t) : t -> Prop := 
  | potAcc_trans: forall a:t,



End PotentialAccess.
