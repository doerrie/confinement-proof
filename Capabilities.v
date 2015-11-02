Require Import Bool.
Require Import References.
Require Import OrderedType.
Require Import AccessRights.
Require Import AccessRightSets.
Require Import Sumbool_dec.

(* Capabilities combine designation and authority *)
(* Specifically, capabilities have a target function. *)
(* Capabilities are a MiniOrderedType *)

Module Type CapabilityType (Ref:ReferenceType).
  
  Include Type OrderedType.OrderedType.
  
  (* a capability designates a target *)
  Parameter target: t -> Ref.t.
  Parameter rights: t -> ARSet.t.
  Parameter mkCap: Ref.t -> ARSet.t -> t.
  Parameter weaken: t -> t.
  
  Parameter target_eq: forall (c1 c2:t), eq c1 c2 -> Ref.eq (target c1) (target c2).
  Parameter rights_eq: forall (c1 c2:t), eq c1 c2 -> ARSet.eq (rights c1) (rights c2).
  
  Parameter target_rights_eq: forall (c1 c2:t), 
    Ref.eq (target c1) (target c2) -> 
    ARSet.eq (rights c1) (rights c2) ->
    eq c1 c2.
  
  Parameter mkCap_eq: forall tgt rgts c, 
    Ref.eq tgt (target c) /\ ARSet.eq rgts (rights c) <->
    eq (mkCap tgt rgts) c.
  
  Parameter weaken_eq: forall c,
    eq (weaken c) 
    (mkCap (target c) 
      (if orb (true_bool_of_sumbool (ARSetProps.In_dec wk (rights c)))
        (true_bool_of_sumbool (ARSetProps.In_dec rd (rights c))) 
        then (ARSet.singleton wk) 
        else ARSet.empty)).
  
End CapabilityType.


