Require Import Capabilities_Conv.
Require Import Capabilities_ConvImpl.
Require Import ReferencesImpl.
Require Import CapabilitiesAppl.

Module NatCapability_Conv <: CapabilityConv NatReference NatCapability 
  := MakeCapConv NatReference NatCapability.