Require Import References.
Require Import Indices.
Require Import Capabilities.
Require Import Objects.
Require Import FMapList2.
Require Import OrderedType.

Module MakeNatObj (Ref:ReferenceType) (Cap:CapabilityType Ref) (Ind:IndexType): ObjectType Ref Cap Ind.
  
  Module MapS := Make_fun Ind.
  Module Obj := Make_ord_fun Ind MapS Cap.

  Include Obj.
  
  Module ObjectFMapList_OT := MOT_to_OT Obj.
  Definition eq_dec := ObjectFMapList_OT.eq_dec.
  
End MakeNatObj.

