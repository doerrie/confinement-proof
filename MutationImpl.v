Require Import Morphisms.
Require Import AccessRights.
Require Import References.
Require Import RefSets.
Require Import Capabilities.
Require Import Indices.
Require Import Objects.
Require Import SystemState.
Require Import SemanticsDefinitions.
Require Import Semantics.
Require Import Semantics_ConvImpl.
Require Import Execution.
Require FSetExists.
Require Import Basics.
Require Import SetoidList.
(* Require Import SetoidListEquiv. *)
Require Import Morphisms.
(* type_remove *)
Require Import Mutation.



Module MakeMutation (Ref:ReferenceType) (RefS: RefSetType Ref) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) (SemDefns: SemanticsDefinitionsType Ref Cap Ind Obj Sys) (Sem: SemanticsType Ref RefS Cap Ind Obj Sys SemDefns) (Exe: ExecutionType Ref RefS Cap Ind Obj Sys SemDefns Sem) : MutationType Ref RefS Cap Ind Obj Sys SemDefns Sem Exe.

(* Import Sem.RS_Mod. *)
Import RefS.
Module SemConv := MakeSemanticsConv Ref RefS Cap Ind Obj Sys SemDefns Sem.

Inductive mutated_op_def n s op : RefSet.t -> Prop := 
| mutated_op_not_in : forall rf n', RefSet.eq n n' -> Sem.read_from_def s op rf ->
  ~ RefSet.Exists (fun x => RefSet.In x rf) n -> mutated_op_def n s op n'
| mutated_op_valid_in : forall rf n', RefSet.eq n n' -> Sem.read_from_def s op rf -> 
  RefSet.Exists (fun x => RefSet.In x rf) n ->
  forall wt, Sem.wrote_to_def s op wt -> 
    forall n2, RefSet.eq (RefSet.union n' wt) n2 ->
    mutated_op_def n s op n2.

Inductive mutated_def n (s:Sys.t) : (list Sem.operation) -> RefSet.t -> Prop :=
| mutated_nil : forall n', RefSet.eq n n' -> mutated_def n s nil n'
| mutated_cons : forall opList n2, mutated_def n s opList n2 -> 
  forall s', Exe.execute_def s opList s' ->
    forall op n3, mutated_op_def n2 s' op n3 ->
      mutated_def n s (cons op opList) n3.


Theorem exists_in2: forall n rf, 
  {RefSet.Exists (fun x => RefSet.In x rf) n} + {~ RefSet.Exists (fun x => RefSet.In x rf) n}.
Proof.
  intros.
  eapply RefSetExists.exists_'.
  intros; eapply RefSetDep.mem.
  unfold SetoidList.compat_P; unfold Proper; unfold respectful; unfold impl; unfold flip; intros.
  rewrite <- H; auto.
Qed.

Definition mutated_op n s op := 
  let rf := (Sem.read_from s op) in
  if exists_in2 n rf then 
    RefSet.union n (Sem.wrote_to s op)
    else n.

Fixpoint mutated n s opList : RefSet.t := 
  match opList with
    | nil => n
    | cons op tl => mutated_op (mutated n s tl) (Exe.execute s tl) op
  end.

Theorem mutated_op_spec : forall n s op, mutated_op_def n s op (mutated_op n s op).
Proof.
  unfold mutated_op; intros.
  case (exists_in2 n (Sem.read_from s op)); intros Hcase;
    [eapply mutated_op_valid_in | eapply mutated_op_not_in];
    solve 
    [eapply Sem.read_from_spec; eapply RefSet.eq_refl
      |apply Hcase
      |apply Sem.wrote_to_spec; eapply RefSet.eq_refl
      |apply RefSet.eq_refl
    ].
Qed.

Theorem mutated_spec: forall s opList n, mutated_def n s opList (mutated n s opList).
Proof.
  intros s opList n; revert n s.
  induction opList;
  intros n s; econstructor; simpl;
    try solve [apply IHopList
      |apply Exe.execute_spec; apply Sys.eq_refl
      |eapply mutated_op_spec
     |eapply RefSet.eq_refl
    ].
Qed.

Theorem Proper_mutated_op_def: Proper (RefSet.eq ==> Sys.eq ==> eq ==> RefSet.eq ==> impl) mutated_op_def.
Proof.
  unfold Proper; unfold respectful; unfold impl.
  intros n n' HeqN s s' HeqS op op' HeqOp m m' HeqM Himpl.
  destruct Himpl as [rf n2 Heq Hrf Hex | rf n2 Heq Hrf Hex wt Hwt]; rewrite HeqOp in *.
  eapply mutated_op_not_in.
  eapply RefSet.eq_trans. apply RefSet.eq_sym; apply HeqN. 
  eapply RefSet.eq_trans. apply Heq.
  apply HeqM.
  (* Proper_read_from_def moved to Semantics_ConvImpl.v *)
  eapply SemConv.Proper_read_from_def;
    [ apply HeqS
      | apply eq_refl
      | apply RefSet.eq_refl
      | apply Hrf
    ].
  intros Hnot; apply Hex. clear Hex.
  destruct Hnot as [x Hnot]; apply ex_intro with x.
  intuition eauto; eapply HeqN; auto.

  eapply mutated_op_valid_in.

  eapply RefSet.eq_trans. eapply RefSet.eq_sym; apply HeqN.
  apply Heq.
  eapply SemConv.Proper_read_from_def;
    [ apply HeqS
      | apply eq_refl
      | apply RefSet.eq_refl
      | apply Hrf
    ].
  destruct Hex as [x Hex]; apply ex_intro with x.
  intuition eauto; eapply HeqN; auto.
  (* Proper_wrote_to_def moved to Semantics_ConvImpl.v *)
  eapply SemConv.Proper_wrote_to_def;
    [ apply HeqS
      | apply eq_refl
      | apply RefSet.eq_refl
      | apply Hwt
    ].

  eapply RefSet.eq_trans; eauto.

Qed.

(* This isn't necessary for future proofs, so I'm ignoring it for now. *)
(*
Theorem Proper_mutated_def: Proper (RefSet.eq ==> Sys.eq ==> eqlistA eq ==> RefSet.eq ==> impl) mutated_def.
Proof.
  intros.
Admitted.
*)

End MakeMutation.