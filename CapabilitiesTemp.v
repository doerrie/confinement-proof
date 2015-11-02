Require Import List.
Require Import ListSet.

Section System.

  (* Define the common access rights *)

  Inductive accessRight : Set :=
  |  weak : accessRight
  |  read : accessRight
  | write : accessRight
  |  send : accessRight.
  
  (* Define the object states.  We use the term 'live' to denote an object that 'exists' as exists is a reserved word. *)

  Inductive obState : Set :=
  | unborn : obState
  | live : obState
  | dead : obState.

  (* Declare a universe of Objects *)
  
  Variable object : Set.

  (* Declare that the equality of objects is decidable *)

  Hypothesis object_eq_dec : forall x y:object, {x = y} + {x <> y}.

  (* A capability is a target and finite set of access Rights *)

  Inductive capability : Set :=
  | obCap : object -> set accessRight -> capability.

  (* stateObs declares that an object in our graph has a label. *)

  Inductive stateOb : Set :=
  | obLabel : object -> obState -> stateOb.

  (* the obState portion of the system state is a set of stateObs. *)

  Definition stateObState := set stateOb.

  (* stateCaps declares an edge in the graph *)

  Inductive stateCap : Set :=
  | ownCap : object -> capability -> stateCap.

  (* the capability portio of the system state is a set of stateCaps *)

  Definition stateCapState := set stateCap.

  (* constructs a system state from a set of stateCaps and a set of stateObs *)

  Inductive sysState : Set := 
  | mkSysState : stateObState -> stateCapState -> sysState.

  (* Theorem: obStates have a decidable equality *)

  Theorem obState_eq_dec: forall x y: obState, {x = y} + {x <> y}.
    Proof.
      decide equality.
    Qed.

  (* Theorem: stateObs have a decidable equality *)

  Theorem stateOb_eq_dec: forall x y: stateOb, {x = y} + {x <> y}.
  Proof.
    intros.
    destruct x; destruct y.
    generalize (object_eq_dec o o1); intros.
    generalize (obState_eq_dec o0 o2); intros.
    destruct H; destruct H0;
      first 
        [constructor 1 ; subst ; reflexivity | 
          constructor 2;  subst; simplify_eq; auto].  
  Qed.

Require Import Wf_nat.


  (* Decide if there are no duplicate objects in a stateObState *)

  Inductive hasObject (objs : stateObState) (obj : object) : Prop :=
  | containment : forall obSt, set_In (obLabel obj obSt) objs -> hasObject objs obj.

  Definition hasObject2 (objs : stateObState) (obj : object) := forall obSt, set_In (obLabel obj obSt) objs.

(*
  Theorem fooey : forall objs obj,
    hasObject objs obj <-> hasObject2 objs obj.
  Proof.
    intros; split; intros.
    unfold hasObject2. intros.  inversion H; subst.  
    
  Qed.
*)

  Inductive no_dup_objs : stateObState -> Prop :=
  | dup_empty : no_dup_objs (empty_set stateOb)
  | dup_add : forall objs ob obSt,
      no_dup_objs objs -> ~ set_In (obLabel ob obSt) objs -> no_dup_objs (set_add stateOb_eq_dec (obLabel ob obSt) objs).




End System.
