Require Import References.
Require Import Capabilities.
Require Import FSets.
Require Import OrderedTypeEx.
Require FSetAddEq.
Require FSetBridge.
Require FoldEqual.
Require FoldOrder.
Require FSetEqEqual.
Require FSetExists.
(* type_remove *)
Require Import CapSets.

Module Make (Ref:ReferenceType) (Cap:CapabilityType Ref) : CapSetType Ref Cap.

  Module CapSet := FSetList.Make Cap. 
  Module CapSetProps := FSetProperties.Properties CapSet.
  Module CapSetFacts := FSetFacts.Facts CapSet.
  Module CapSetDep := FSetBridge.DepOfNodep CapSet.
  Module CapSetEqProps := FSetEqProperties.EqProperties CapSet.
  Module CapSetAddEq := FSetAddEq.Make CapSet.
  Module CapSetFold := FoldEqual.Make CapSet.
  Module CapSetFoldOrder := FoldOrder.Make CapSet.
  Module CapSetEqEqual :=  FSetEqEqual.makeEqual CapSet.
  Module CapSetExists := FSetExists.makeExists CapSetDep.

End Make.