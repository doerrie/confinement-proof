Require Import References.
Require Import RefSets.
Require Import Capabilities.
Require Import Indices.
Require Import Objects.
Require Import SystemState.
Require Import SemanticsDefinitions.
Require Import Semantics.
Require Import List.
Require Import Semantics_Conv.
Require Import Semantics_ConvImpl.
(* type_remove *)
Require Import Execution.

Module SimpleExecution (Ref:ReferenceType) (RefS: RefSetType Ref) (Cap:CapabilityType Ref) (Ind:IndexType) (Obj:ObjectType Ref Cap Ind) (Sys:SystemStateType Ref Cap Ind Obj) (SemDefns: SemanticsDefinitionsType Ref Cap Ind Obj Sys) (Sem:SemanticsType Ref RefS Cap Ind Obj Sys SemDefns) : ExecutionType Ref RefS Cap Ind Obj Sys SemDefns Sem.

  Module SemConv := MakeSemanticsConv Ref RefS Cap Ind Obj Sys SemDefns Sem.

  Inductive execute_def s: list Sem.operation -> Sys.t -> Prop :=
  | execute_nil: forall s', Sys.eq s s' -> execute_def s nil s'
  | execute_cons : forall op tail s',
    execute_def s tail s' ->
    forall s'', Sys.eq (Sem.do_op op s') s'' ->
    execute_def s (op :: tail) s''.

  Definition execute s op_list := (List.fold_right Sem.do_op s op_list).

  Theorem execute_spec_1 : forall s s' op_list, 
    execute_def s op_list s' -> Sys.eq (execute s op_list) s'.
  Proof.
    intros.
    unfold execute.
    induction H; simpl; auto.
    eapply Sys.eq_trans.
    eapply SemConv.do_op_eq; eauto.
    assumption.
  Qed.

  Theorem execute_spec_2 : forall s op_list s', 
     Sys.eq (execute s op_list) s' -> execute_def s op_list s'.
  Proof.
    intros s op_list.
    induction op_list; intros.
    constructor; simpl in *; auto.
    simpl in H.
    constructor 2 with (execute s op_list); auto;
      apply IHop_list; apply Sys.eq_refl.
  Qed.
  
  Theorem execute_spec : forall s s' op_list, 
    execute_def s op_list s' <-> Sys.eq (execute s op_list) s'.
  Proof.
    intros.
    split; intros; 
      [apply execute_spec_1|apply execute_spec_2]; auto.
  Qed.

End SimpleExecution.
