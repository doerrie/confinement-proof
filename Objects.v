(* Objects are a map from index to cap *)
Require Import References.
Require Import Indices.
Require Import Capabilities.
Require Import FMapInterface2.


(* originally I had intended both objects and system state types to be more relaxed than
   FMaps, but I am correcting that for the time being *)


Module Type ObjectType (Ref: ReferenceType) (Cap:CapabilityType Ref) (Ind:IndexType).

  Declare Module MapS : Sfun Ind.

  Include (Sord_fun Ind MapS Cap).
  
  Parameter eq_dec : forall x y, { eq x y } + { ~ eq x y }.
  
End ObjectType.


