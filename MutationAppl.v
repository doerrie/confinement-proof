Require Import Mutation.
Require Import MutationImpl.
Require Import Semantics_ConvAppl.
Require Import ReferencesImpl.
Require Import RefSetsAppl.
Require Import CapabilitiesAppl.
Require Import IndicesImpl.
Require Import ObjectsAppl.
Require Import SystemStateAppl.
Require Import SemanticsDefinitionsAppl.
Require Import SemanticsAppl.
Require Import ExecutionAppl.

Module NatMutation <: 
  MutationType NatReference NatRefSet NatCapability NatIndex NatObject NatState NatSemDefns NatSemantics NatExecution :=
  MakeMutation NatReference NatRefSet NatCapability NatIndex NatObject NatState NatSemDefns NatSemantics NatExecution.