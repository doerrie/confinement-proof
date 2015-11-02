(* type_remove *)
Require Import Semantics.
Require Import Sumbool_dec.
Require Import FMapFacts.
Require Import OptionMap2.
Require Import SemanticsDefinitions.
Require Import AccessRights.
Require Import AccessRightSets.
Require Import RefSets.
Require Import References.
Require Import Indices.
Require Import Capabilities.
Require Import Objects.
Require Import SystemState.
Require Import SemanticsDefinitions.

Module SimpleSemantics (Ref:ReferenceType) (RefS: RefSetType Ref) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) (SemDefns: SemanticsDefinitionsType Ref Cap Ind Obj Sys) : SemanticsType Ref RefS Cap Ind Obj Sys SemDefns.
  Import SemDefns.
  Export SemDefns.

(*  Module RS_Mod := RefSets.Make Ref.
  Import RS_Mod. *)
  Import RefS.



  (* in the following, I'm abusing notation.  
     We use t as an object, not an index to find the target defining an object.
     We use c as a capability, not an index in t naming the capability.
     Likewise with cl for capability lists. *)
  (* (read a t s): a reads data from t.  *)
  (* abstract *)
  Definition do_read (a:Ref.t) (t:Ind.t) (s:Sys.t) : Sys.t := s.

  Theorem read_spec: forall a t s, Sys.eq (do_read a t s) s.
  Proof.
    intros.
    unfold do_read.
    apply Sys.eq_refl.
  Qed.

  (* (write a t s): a writes data to t. *)
  (* abstract *)
  Definition do_write (a:Ref.t) (t:Ind.t) (s:Sys.t) : Sys.t := s.
  
  Theorem write_spec: forall a t s, Sys.eq (do_write a t s) s.
  Proof.
    intros.
    unfold do_write.
    apply Sys.eq_refl.
  Qed.

  (* (fetch a t c i s): a fetches c from t and places it at index i. *)
  (* abstract *)
  Definition do_fetch (a:Ref.t) (t:Ind.t) (c:Ind.t) (i:Ind.t) (s:Sys.t) : Sys.t :=
    if (true_bool_of_sumbool (SemDefns.fetch_preReq_dec a t s))
      then if (true_bool_of_sumbool (SemDefns.option_hasRight_dec (SC.getCap t a s) rd))
        then (option_map1 (fun tgt => SC.copyCap c tgt i a s) s (SemDefns.option_target (SC.getCap t a s)))
        else (option_map1 (fun tgt => SC.weakCopyCap c tgt i a s) s (SemDefns.option_target (SC.getCap t a s)))
      else s.

  Theorem fetch_invalid: forall a t c i s, 
    ~ SemDefns.fetch_preReq a t s -> Sys.eq (do_fetch a t c i s) s.
  Proof.
    intros.
    unfold do_fetch.
    destruct (SemDefns.fetch_preReq_dec a t s); [contradiction | simpl].
    apply Sys.eq_refl.
  Qed.
  
  Theorem fetch_read: forall a t c i s,
    SemDefns.fetch_preReq a t s -> SemDefns.option_hasRight (SC.getCap t a s) rd -> 
    Sys.eq (do_fetch a t c i s)
         (option_map1 (fun tgt => SC.copyCap c tgt i a s) s (SemDefns.option_target (SC.getCap t a s))).
  Proof.
    intros.
    unfold do_fetch.
    destruct (SemDefns.fetch_preReq_dec a t s); try contradiction; simpl.
    destruct (SemDefns.option_hasRight_dec (SC.getCap t a s) rd); try contradiction; simpl.
    apply Sys.eq_refl.
  Qed.

  Theorem fetch_weak: forall a t c i s,
    SemDefns.fetch_preReq a t s -> ~ SemDefns.option_hasRight (SC.getCap t a s) rd -> 
    SemDefns.option_hasRight (SC.getCap t a s) wk  ->
    Sys.eq (do_fetch a t c i s)
    (option_map1 (fun tgt => SC.weakCopyCap c tgt i a s) s (SemDefns.option_target (SC.getCap t a s))).
  Proof.
    intros.
    unfold do_fetch.
    destruct (SemDefns.fetch_preReq_dec a t s); try contradiction; simpl.
    destruct (SemDefns.option_hasRight_dec (SC.getCap t a s) rd); try contradiction; simpl.
    apply Sys.eq_refl.
  Qed.

  Ltac prove_valid_invalid do_X X_preReq_dec a t s :=
    intros; unfold do_X; destruct (X_preReq_dec a t s); try contradiction; simpl; apply Sys.eq_refl.

  (* (store a t c i s): a stores c to t at index i. *)
  (* abstract *)
  Definition do_store (a:Ref.t) (t:Ind.t) (c:Ind.t) (i:Ind.t) (s:Sys.t) : Sys.t :=
    if (true_bool_of_sumbool (SemDefns.store_preReq_dec a t s))
      then (option_map1 (fun tgt => SC.copyCap c a i tgt s) s (SemDefns.option_target (SC.getCap t a s)))
      else s.

  Theorem store_invalid : forall a t c i s, ~ SemDefns.store_preReq a t s -> Sys.eq (do_store a t c i s) s.
  Proof.
    prove_valid_invalid do_store SemDefns.store_preReq_dec a t s.
  Qed.
  
  Theorem  store_valid: forall a t c i s, SemDefns.store_preReq a t s -> 
    Sys.eq (do_store a t c i s) 
    (option_map1 (fun tgt => SC.copyCap c a i tgt s) s (SemDefns.option_target (SC.getCap t a s))).
  Proof.
    prove_valid_invalid do_store SemDefns.store_preReq_dec a t s.
  Qed.

  (* (revoke a t c s): a removes capability c from t. *)
  (* abstract *)
  Definition do_revoke (a:Ref.t) (t:Ind.t) (c:Ind.t) (s:Sys.t) : Sys.t :=
    if (true_bool_of_sumbool (SemDefns.revoke_preReq_dec a t s))
      then (option_map1 (fun tgt => SC.rmCap c tgt s) s (SemDefns.option_target (SC.getCap t a s)))
      else s.

  Theorem revoke_invalid : forall a t c s, ~ SemDefns.revoke_preReq a t s -> Sys.eq (do_revoke a t c s) s.
  Proof.
    prove_valid_invalid do_revoke SemDefns.revoke_preReq_dec a t s.
  Qed.

  Theorem revoke_valid : forall a t c s, SemDefns.revoke_preReq a t s -> 
    Sys.eq (do_revoke a t c s) 
    (option_map1 (fun tgt => SC.rmCap c tgt s) s (SemDefns.option_target (SC.getCap t a s))).
  Proof.
    prove_valid_invalid do_revoke SemDefns.revoke_preReq_dec a t s.
  Qed.

  (* (send a t cil op_i s): a sends a message to t containing capabilities. 
     The cil is a capability -> index list, and is a list of pairs.
     Each capability c is stored at index i in t. *)
  (* abstract *)
  Definition do_send (a:Ref.t) (t:Ind.t) (cil:list (Ind.t * Ind.t)) (op_i:option Ind.t) (s:Sys.t) : Sys.t :=
    if (true_bool_of_sumbool (SemDefns.send_preReq_dec a t s))
      then (option_map1 (fun tgt => SC.copyCapList a tgt cil 
      (option_map1
             (fun i => 
               SC.addCap i 
               (Cap.mkCap a (ARSet.singleton tx)) 
               tgt 
               s)
             s 
             op_i)) s (SemDefns.option_target (SC.getCap t a s)))
      else s.

  Theorem send_invalid : forall a t cil op_i s, ~ SemDefns.send_preReq a t s -> Sys.eq (do_send a t cil op_i s) s.
  Proof.
    prove_valid_invalid do_send SemDefns.send_preReq_dec a t s.
  Qed.

  Theorem send_valid : forall a t cil op_i s, SemDefns.send_preReq a t s -> 
    Sys.eq (do_send a t cil op_i s) 
    (option_map1 
      (fun tgt => 
        SC.copyCapList a tgt cil 
           (option_map1 
             (fun i => 
               SC.addCap i 
               (Cap.mkCap a (ARSet.singleton tx)) 
               tgt 
               s)
             s 
             op_i)) 
      s 
      (SemDefns.option_target (SC.getCap t a s))).
  Proof.
    prove_valid_invalid do_send SemDefns.send_preReq_dec a t s.
  Qed.

  (* (destroy a t s): a destroys t. *)
  (* abstract *)
  Definition do_destroy (a:Ref.t) (t:Ind.t) (s:Sys.t) : Sys.t :=
      if (true_bool_of_sumbool (SemDefns.destroy_preReq_dec a t s))
      then (option_map1 (fun tgt => SC.set_dead tgt s) s (SemDefns.option_target (SC.getCap t a s)))
      else s.

  Theorem destroy_invalid: forall a t s, ~ SemDefns.destroy_preReq a t s -> Sys.eq (do_destroy a t s) s.
  Proof.
    prove_valid_invalid do_destroy SemDefns.destroy_preReq_dec a t s.
  Qed.

  Theorem destroy_valid: forall a t s, SemDefns.destroy_preReq a t s -> 
    Sys.eq (do_destroy a t s)
    (option_map1 (fun tgt => SC.set_dead tgt s) s (SemDefns.option_target (SC.getCap t a s))).
  Proof.
    prove_valid_invalid do_destroy SemDefns.destroy_preReq_dec a t s.
  Qed.

  (* (allocate a n i cil s): a allocates child n,
     handing it capabilities via cil, and places the child's cap at index i. *)
  (* abstract *)
  Definition do_allocate (a:Ref.t) (n:Ref.t) (i:Ind.t) (cil:list (Ind.t * Ind.t)) (s:Sys.t) : Sys.t :=
    if (true_bool_of_sumbool (SemDefns.allocate_preReq_dec a n s))
      then
    (SC.addCap i 
      (Cap.mkCap n 
        (ARSet.add rd 
          (ARSet.add wr 
            (ARSet.add wk
              (ARSet.singleton tx))))) a 
    (SC.copyCapList a n cil 
      (SC.set_alive n (SC.updateObj n (Obj.MapS.empty _) 
        (SC.rmCapsByTarget n s)))))
    else s.
  Theorem allocate_invalid: forall a n i cil s, ~ SemDefns.allocate_preReq a n s -> Sys.eq (do_allocate a n i cil s) s.
  Proof.
    prove_valid_invalid do_allocate SemDefns.allocate_preReq_dec a n s.
  Qed.

  Theorem allocate_valid: forall a n i cil s, SemDefns.allocate_preReq a n s ->
    Sys.eq (do_allocate a n i cil s)
    (SC.addCap i 
      (Cap.mkCap n all_rights) a 
    (SC.copyCapList a n cil 
      (SC.set_alive n (SC.updateObj n (Obj.MapS.empty _) 
        (SC.rmCapsByTarget n s))))).
  Proof.
    prove_valid_invalid do_allocate SemDefns.allocate_preReq_dec a n s.
  Qed.


  Inductive operation : Type :=
  | read: Ref.t -> Ind.t  -> operation
  | write: Ref.t -> Ind.t -> operation
  | fetch: Ref.t -> Ind.t -> Ind.t -> Ind.t -> operation
  | store: Ref.t -> Ind.t -> Ind.t -> Ind.t -> operation
  | revoke: Ref.t -> Ind.t -> Ind.t -> operation
  | send: Ref.t -> Ind.t -> list (Ind.t * Ind.t) -> option Ind.t -> operation
  | allocate: Ref.t -> Ref.t -> Ind.t -> list (Ind.t * Ind.t) -> operation
  | destroy: Ref.t -> Ind.t -> operation.
  
  Inductive do_op_spec : operation -> (Sys.t -> Sys.t) -> Prop :=
    | do_op_spec_read: forall a t, do_op_spec (read a t) (do_read a t)
    | do_op_spec_write: forall a t, do_op_spec (write a t) (do_write a t)
    | do_op_spec_fetch: forall a t c i, do_op_spec (fetch a t c i) (do_fetch a t c i)
    | do_op_spec_store: forall a t c i, do_op_spec (store a t c i) (do_store a t c i)
    | do_op_spec_revoke: forall a t c, do_op_spec (revoke a t c) (do_revoke a t c)
    | do_op_spec_send: forall a t cil op_i, do_op_spec (send a t cil op_i) (do_send a t cil op_i)
    | do_op_spec_allocate: forall a t i cil, do_op_spec (allocate a t i cil) (do_allocate a t i cil)
    | do_op_spec_destroy: forall a t, do_op_spec (destroy a t) (do_destroy a t).

  Hint Constructors do_op_spec.

  Definition do_op op s:=
    match op with
      | read a t => do_read a t s
      | write a t => do_write a t s
      | fetch a t c i => do_fetch a t c i s
      | store a t c i => do_store a t c i s
      | revoke a t c => do_revoke a t c s
      | send a t cil op_i => do_send a t cil op_i s
      | allocate a n i cil => do_allocate a n i cil s
      | destroy a t => do_destroy a t s
    end.

  Theorem do_op_spec_do_op: forall op,
    do_op_spec op (do_op op).
  Proof.
    intros.
    destruct op; unfold do_op; constructor.
  Qed.

  Definition add_option_target s a t r_set := (option_map1 (fun tgt => RefSet.add tgt r_set) r_set (SemDefns.option_target (SC.getCap t a s))).
  
  Inductive read_from_def s: operation -> RefSet.t -> Prop :=
  | read_from_read_valid : forall a t x, 
    SemDefns.read_preReq a t s ->
    RefSet.Equal (add_option_target s a t (RefSet.singleton a)) x ->
    read_from_def s (read a t) x
  | read_from_read_invalid : forall a t x, 
    ~ SemDefns.read_preReq a t s ->
    RefSet.Empty x ->
    read_from_def s (read a t) x

  | read_from_write_valid: forall a t x,
    SemDefns.write_preReq a t s ->
    RefSet.Equal (RefSet.singleton a) x ->
    read_from_def s (write a t) x
  | read_from_write_invalid: forall a t x,
    ~ SemDefns.write_preReq a t s ->
    RefSet.Empty x ->
    read_from_def s (write a t) x

  | read_from_fetch_valid : forall a t c i x, 
    SemDefns.fetch_preReq a t s ->
    RefSet.Equal (add_option_target s a t (RefSet.singleton a)) x ->
    read_from_def s (fetch a t c i) x
  | read_from_fetch_invalid : forall a t c i x, 
    ~ SemDefns.fetch_preReq a t s ->
    RefSet.Empty x ->
    read_from_def s (fetch a t c i) x

  | read_from_store_valid: forall a t c i x,
    SemDefns.store_preReq a t s ->
    RefSet.Equal (RefSet.singleton a) x ->
    read_from_def s (store a t c i) x
  | read_from_store_invalid: forall a t c i x,
    ~ SemDefns.store_preReq a t s ->
    RefSet.Empty x ->
    read_from_def s (store a t c i) x

  | read_from_revoke_valid: forall a t c x, 
    SemDefns.revoke_preReq a t s ->
    RefSet.Equal (RefSet.singleton a) x ->
    read_from_def s (revoke a t c) x
  | read_from_revoke_invalid: forall a t c x, 
    ~ SemDefns.revoke_preReq a t s ->
    RefSet.Empty x ->
    read_from_def s (revoke a t c) x

  | read_from_send_valid: forall a t cil op_i x, 
    SemDefns.send_preReq a t s ->
    RefSet.Equal (RefSet.singleton a) x ->
    read_from_def s (send a t cil op_i) x
  | read_from_send_invalid: forall a t cil op_i x, 
    ~ SemDefns.send_preReq a t s ->
    RefSet.Empty x ->
    read_from_def s (send a t cil op_i) x

  | read_from_allocate_valid: forall a n i cil x, 
    SemDefns.allocate_preReq a n s ->
    RefSet.Equal (RefSet.singleton a) x ->
    read_from_def s (allocate a n i cil) x
  | read_from_allocate_invalid: forall a n i cil x, 
    ~ SemDefns.allocate_preReq a n s ->
    RefSet.Empty x ->
    read_from_def s (allocate a n i cil) x

  | read_from_destroy_valid: forall a t x, 
    SemDefns.destroy_preReq a t s ->
    RefSet.Equal (RefSet.singleton a) x ->
    read_from_def s (destroy a t) x
  | read_from_destroy_invalid: forall a t x, 
    ~ SemDefns.destroy_preReq a t s ->
    RefSet.Empty x ->
    read_from_def s (destroy a t) x.

  Inductive wrote_to_def s: operation -> RefSet.t -> Prop :=
  | wrote_to_read_valid : forall a t x, 
    SemDefns.read_preReq a t s ->
    RefSet.Equal (RefSet.singleton a) x -> 
    wrote_to_def s (read a t) x
  | wrote_to_read_invalid : forall a t x, 
    ~ SemDefns.read_preReq a t s ->
    RefSet.Empty x ->
    wrote_to_def s (read a t) x

  | wrote_to_write_valid: forall a t x,
    SemDefns.write_preReq a t s ->
    RefSet.Equal (add_option_target s a t RefSet.empty) x ->
    wrote_to_def s (write a t) x
  | wrote_to_write_invalid: forall a t x,
    ~ SemDefns.write_preReq a t s ->
    RefSet.Empty x ->
    wrote_to_def s (write a t) x

  | wrote_to_fetch_valid : forall a t c i x, 
    SemDefns.fetch_preReq a t s ->
    RefSet.Equal (RefSet.singleton a) x -> 
    wrote_to_def s (fetch a t c i) x
  | wrote_to_fetch_invalid : forall a t c i x, 
    ~ SemDefns.fetch_preReq a t s ->
    RefSet.Empty x ->
    wrote_to_def s (fetch a t c i) x

  | wrote_to_store_valid: forall a t c i x, 
    SemDefns.store_preReq a t s ->
    RefSet.Equal (add_option_target s a t RefSet.empty) x -> 
    wrote_to_def s (store a t c i) x
  | wrote_to_store_invalid: forall a t c i x, 
    ~ SemDefns.store_preReq a t s ->
    RefSet.Empty x ->
    wrote_to_def s (store a t c i) x

  | wrote_to_revoke_valid: forall a t c x, 
    SemDefns.revoke_preReq a t s ->
    RefSet.Equal (add_option_target s a t RefSet.empty) x -> 
    wrote_to_def s (revoke a t c) x
  | wrote_to_revoke_invalid: forall a t c x, 
    ~ SemDefns.revoke_preReq a t s ->
    RefSet.Empty x ->
    wrote_to_def s (revoke a t c) x

  | wrote_to_send_valid: forall a t cil op_i x,
    SemDefns.send_preReq a t s ->
    RefSet.Equal (add_option_target s a t RefSet.empty) x -> 
    wrote_to_def s (send a t cil op_i) x
  | wrote_to_send_invalid: forall a t cil op_i x,
    ~ SemDefns.send_preReq a t s ->
    RefSet.Empty x ->
    wrote_to_def s (send a t cil op_i) x

  | wrote_to_allocate_valid: forall a n i cil x, 
    SemDefns.allocate_preReq a n s ->
    RefSet.Equal (RefSet.add n (RefSet.singleton a)) x -> 
    wrote_to_def s (allocate a n i cil) x
  | wrote_to_allocate_invalid: forall a n i cil x, 
    ~ SemDefns.allocate_preReq a n s ->
    RefSet.Empty x ->
    wrote_to_def s (allocate a n i cil) x

  | wrote_to_destroy_valid: forall a t x, 
    SemDefns.destroy_preReq a t s ->
    RefSet.Equal (RefSet.singleton a) x -> 
    wrote_to_def s (destroy a t) x
  | wrote_to_destroy_invalid: forall a t x,
    ~ SemDefns.destroy_preReq a t s -> 
    RefSet.Empty x ->
    wrote_to_def s (destroy a t) x.

  (*abstract*)
  Definition read_from s op :=
    match op with
      | read a t => if (SemDefns.read_preReq_dec a t s) 
        then add_option_target s a t (RefSet.singleton a)
        else RefSet.empty
      | write a t => if (SemDefns.write_preReq_dec a t s)
        then RefSet.singleton a
        else RefSet.empty
      | fetch a t c i => if (SemDefns.fetch_preReq_dec a t s) 
        then add_option_target s a t (RefSet.singleton a)
        else RefSet.empty
      | store a t c i => if SemDefns.store_preReq_dec a t s
        then RefSet.singleton a
        else RefSet.empty
      | revoke a t c => if SemDefns.revoke_preReq_dec a t s
        then RefSet.singleton a
        else RefSet.empty
      | send a t cil opt_i => if SemDefns.send_preReq_dec a t s
        then RefSet.singleton a
        else RefSet.empty
      | allocate a n i cil => if SemDefns.allocate_preReq_dec a n s
        then RefSet.singleton a
        else RefSet.empty
      | destroy a t => if SemDefns.destroy_preReq_dec a t s
        then RefSet.singleton a
        else RefSet.empty
    end.


    Ltac solve_apply_16_constructors remainder :=
      solve [constructor 1; remainder
        | constructor 2; remainder
        | constructor 3; remainder
        | constructor 4; remainder
        | constructor 5; remainder
        | constructor 6; remainder
        | constructor 7; remainder
        | constructor 8; remainder
        | constructor 9; remainder
        | constructor 10; remainder
        | constructor 11; remainder
        | constructor 12; remainder
        | constructor 13; remainder
        | constructor 14; remainder
        | constructor 15; remainder
        | constructor 16; remainder
      ].

  Theorem read_from_spec : forall s op ob_list,
    read_from_def s op ob_list <-> 
    RefSet.Equal (read_from s op) ob_list.
  Proof.

    (* these will be deleted by typeify2.pl as they are in a proof body *)
    Ltac reduce_dec dec :=
      let Hcase := fresh "Hcase" in
        case dec; intros Hcase; try contradiction.
    Ltac solve_reduce_tail H0 := solve[ auto| eapply RefSetProps.empty_is_empty_1 in H0; 
              eapply RefSet.eq_sym; auto].
    Ltac reduce_and_solve dec H0 := reduce_dec dec; solve_reduce_tail H0.
    Ltac empty_solution := auto; apply RefSetProps.empty_is_empty_2; apply RefSet.eq_sym; auto.
    Ltac reduce_and_solve2 dec := reduce_dec dec; [intros H; solve_apply_16_constructors auto
      | intros H; solve_apply_16_constructors empty_solution].


    intros; split; intros.
    destruct H; unfold read_from;
      try solve [reduce_and_solve (send_preReq_dec a t s) H0
      | reduce_and_solve (read_preReq_dec a t s) H0
      | reduce_and_solve (write_preReq_dec a t s) H0
      | reduce_and_solve (fetch_preReq_dec a t s) H0
      | reduce_and_solve (store_preReq_dec a t s) H0
      | reduce_and_solve (revoke_preReq_dec a t s) H0
      | reduce_and_solve (allocate_preReq_dec a n s) H0
      | reduce_and_solve (destroy_preReq_dec a t s) H0
      ].

    revert H; unfold read_from in *; destruct op;

      try solve 
        [ reduce_and_solve2 (send_preReq_dec t t0 s)
          | reduce_and_solve2 (read_preReq_dec t t0 s)
          | reduce_and_solve2 (write_preReq_dec t t0 s)
          | reduce_and_solve2 (fetch_preReq_dec t t0 s)
          | reduce_and_solve2 (store_preReq_dec t t0 s)
          | reduce_and_solve2 (revoke_preReq_dec t t0 s)
          | reduce_and_solve2 (allocate_preReq_dec t t0 s)
          | reduce_and_solve2 (destroy_preReq_dec t t0 s)
        ].

  Qed.

  (*abstract*)
  Definition wrote_to s op :=
    match op with
      | read a t =>  if (SemDefns.read_preReq_dec a t s) 
        then RefSet.singleton a
        else RefSet.empty
      | write a t =>  if (SemDefns.write_preReq_dec a t s) 
        then add_option_target s a t RefSet.empty
        else RefSet.empty
      | fetch a t c i =>  if (SemDefns.fetch_preReq_dec a t s) 
        then RefSet.singleton a
        else RefSet.empty
      | store a t c i => if (SemDefns.store_preReq_dec a t s) 
        then add_option_target s a t RefSet.empty
        else RefSet.empty
      | revoke a t c => if (SemDefns.revoke_preReq_dec a t s) 
        then add_option_target s a t RefSet.empty
        else RefSet.empty
      | send a t cil opt_i => if (SemDefns.send_preReq_dec a t s) 
        then add_option_target s a t RefSet.empty
        else RefSet.empty
      | allocate a n i cil => if (SemDefns.allocate_preReq_dec a n s) 
        then RefSet.add n (RefSet.singleton a)
        else RefSet.empty
      | destroy a t => if (SemDefns.destroy_preReq_dec a t s) 
        then RefSet.singleton a
        else RefSet.empty
    end.

  Theorem wrote_to_spec : forall s op ob_list,
    wrote_to_def s op ob_list <-> 
    RefSet.Equal (wrote_to s op) ob_list.
  Proof.
    intros; split; intros.

    destruct H; unfold wrote_to;
      try solve [reduce_and_solve (send_preReq_dec a t s) H0
      | reduce_and_solve (read_preReq_dec a t s) H0
      | reduce_and_solve (write_preReq_dec a t s) H0
      | reduce_and_solve (fetch_preReq_dec a t s) H0
      | reduce_and_solve (store_preReq_dec a t s) H0
      | reduce_and_solve (revoke_preReq_dec a t s) H0
      | reduce_and_solve (allocate_preReq_dec a n s) H0
      | reduce_and_solve (destroy_preReq_dec a t s) H0
      ].
    
    revert H; unfold wrote_to in *; destruct op;
      try solve 
        [ reduce_and_solve2 (send_preReq_dec t t0 s)
          | reduce_and_solve2 (read_preReq_dec t t0 s)
          | reduce_and_solve2 (write_preReq_dec t t0 s)
          | reduce_and_solve2 (fetch_preReq_dec t t0 s)
          | reduce_and_solve2 (store_preReq_dec t t0 s)
          | reduce_and_solve2 (revoke_preReq_dec t t0 s)
          | reduce_and_solve2 (allocate_preReq_dec t t0 s)
          | reduce_and_solve2 (destroy_preReq_dec t t0 s)
        ].

Qed.

End SimpleSemantics.


