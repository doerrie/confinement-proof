Require Import Capabilities.
Require Import CapabilitiesImpl.
Require Import ReferencesImpl.

(* Check that our AccessRightCapability satisfies a Capability Type *)
(* Instantiate capabilities using NatReferences and AccessRights *)

Module NatCapability <: CapabilityType NatReference := MakeCapability NatReference.

