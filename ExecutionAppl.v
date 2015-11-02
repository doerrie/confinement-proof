Require Import Execution.
Require Import ExecutionImpl.
(* Require Import Semantics_ConvAppl. *)
Require Import ReferencesImpl.
Require Import CapabilitiesAppl.
Require Import IndicesImpl.
Require Import ObjectsAppl.
Require Import SystemStateAppl.
Require Import SemanticsDefinitionsAppl.
Require Import RefSetsAppl.
Require Import SemanticsAppl.

Module NatExecution <:
  ExecutionType NatReference NatRefSet NatCapability NatIndex NatObject NatState NatSemDefns NatSemantics :=
  SimpleExecution NatReference NatRefSet NatCapability NatIndex NatObject NatState NatSemDefns NatSemantics.