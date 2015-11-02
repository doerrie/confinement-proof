Require Import CapSets.
Require Import CapSetsImpl.
Require Import ReferencesImpl.
Require Import Capabilities.
Require Import CapabilitiesAppl.

Module NatCapSet <: CapSetType NatReference NatCapability := Make NatReference NatCapability.

