Require Import SystemState.
Require Import Objects. 
Require Import ObjectLabels.
Require Import ObjectTypes.
Require Import ObjectSchedules.
Require Import OrderedTypeEx.
Require Import OrderedType.
Require Import FMapList2.
Require Import References.
Require Import Indices.
Require Import Capabilities.


Module MakePairSystemState (Ref: ReferenceType) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) : SystemStateType Ref Cap Ind Obj.

  Module MapS := Make_fun Ref.
  Module P3 := PairOrderedType Obj ObjectLabel.
  Module P2 := PairOrderedType P3 ObjectType.
  Module P := PairOrderedType P2 ObjectSchedule.

  Module SysSt := Make_ord_fun Ref MapS P.

  Include SysSt.

  Module SysStFMapList_OT := MOT_to_OT SysSt.
  Definition eq_dec := SysStFMapList_OT.eq_dec.

End MakePairSystemState.