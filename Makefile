# V_FILES=$(wildcard *.v)
# VO_FILES=$(V_FILES:.v=.vo)
# all : $(V_FILES:.v=.vo)

GENERATED_V_FILES:=
TYPES_VO:=
IMPLS_VO:=
APPLS_VO:=

%.vo : %.v
	sh maxmem.sh -c "coqc $<" $<.mem

#doc : all
#	coqdoc VO_FILES

# Things we really need to know about FSets.

# No longer used
# FSetListUOT.vo : SortingEqual.vo

FoldEqual.vo: FSetAddEq.vo

FSetForall.vo : Sumbool_dec.vo OrderedTypeEquiv.vo

FoldOrder.vo : FSetAddEq.vo FoldEqual.vo OrderedTypeEquiv.vo

# Things we really need to know about FMaps.

OrdFMapEquiv.vo : OptionMap2.vo OptionSumbool.vo FMapFacts2.vo FMapExists.vo

FMapAdd.vo: OptionMap2.vo OptionSumbool.vo OrdFMapEquiv.vo

FMapFoldEqual.vo: OrdFMapEquiv.vo OrderedTypeEquiv.vo

FMapExists.vo: Sumbool_dec.vo FMapInterface2.vo FMapFacts2.vo

FMapList2.vo: FMapInterface2.vo

# The Model and Naive Implementation

References.vo : OrderedInclude.vo

ReferencesImpl.vo: References.vo

Indices.vo: OrderedInclude.vo

IndicesImpl.vo: Indices.vo

AccessRights.vo: ProjectedOrderedType.vo

ObjectTypes.vo : ProjectedOrderedType.vo

ObjectLabels.vo : ProjectedOrderedType.vo

ObjectSchedules.vo : ProjectedOrderedType.vo

CapIndexListFacts.vo : Indices.vo

REFSETS_REQ := FSetAddEq.vo FoldEqual.vo References.vo FoldOrder.vo

RefSets.v : typeify.pl RefSetsImpl.v
	perl typeify.pl  RefSetsImpl.v $@
GENERATED_V_FILES += RefSets.v
RefSets.vo: $(REFSETS_REQ)
TYPES_VO += RefSets.vo
RefSetsImpl.vo: $(REFSETS_REQ) RefSets.vo
IMPLS_VO += RefSetsImpl.vo
RefSetsAppl.vo: ReferencesImpl.vo RefSets.vo RefSetsImpl.vo
APPLS_VO += RefSetsAppl.vo

AccessRightSets.vo : AccessRights.vo FSetAddEq.vo FoldEqual.vo FoldOrder.vo FSetEqEqual.vo

# Capabilities

CAPABILITIES_REQ := References.vo AccessRightSets.vo Sumbool_dec.vo

Capabilities.vo: $(CAPABILITIES_REQ)
TYPES_VO += Capabilities.vo
CapabilitiesImpl.vo: $(CAPABILITIES_REQ) Capabilities.vo
IMPLS_VO += CapabilitiesImpl.vo
CapabilitiesAppl.vo: ReferencesImpl.vo Capabilities.vo CapabilitiesImpl.vo
APPLS_VO += CapabilitiesAppl.vo

# Capabilities Convenience

CAPABILITIES_CONV_REQ := Sumbool_dec.vo AccessRights.vo Capabilities.vo OrderedTypeEquiv.vo

Capabilities_Conv.v : typeify.pl Capabilities_ConvImpl.v
	perl typeify.pl Capabilities_ConvImpl.v $@
GENERATED_V_FILES += Capabilities_Conv.v
Capabilities_Conv.vo: $(CAPABILITIES_CONV_REQ)
TYPES_VO += Capabilities_Conv.vo
Capabilities_ConvImpl.vo: $(CAPABILITIES_CONV_REQ) Capabilities_Conv.vo
IMPLS_VO += Capabilities_ConvImpl.vo
Capabilities_ConvAppl.vo: CapabilitiesAppl.vo Capabilities_ConvImpl.vo
APPLS_VO += Capabilities_ConvAppl.vo

# Capability Sets

CAPSETS_REQ := FSetAddEq.vo FoldEqual.vo References.vo FoldOrder.vo Capabilities.vo Sumbool_dec.vo

CapSets.v : typeify.pl CapSetsImpl.v
	perl typeify.pl  CapSetsImpl.v $@
GENERATED_V_FILES += CapSets.v
CapSets.vo: $(CAPSETS_REQ)
TYPES_VO += CapSets.vo
CapSetsImpl.vo: $(CAPSETS_REQ) CapSets.vo
IMPLS_VO += CapSetsImpl.vo
CapSetsAppl.vo: ReferencesImpl.vo CapabilitiesAppl.vo CapSets.vo CapSetsImpl.vo
APPLS_VO += CapSetsAppl.vo


# Objects

OBJECTS_REQ := Indices.vo Capabilities.vo FMapList2.vo

Objects.vo: $(OBJECTS_REQ)
TYPES_VO += Objects.vo
ObjectsImpl.vo: $(OBJECTS_REQ) Objects.vo FMapInterface2.vo
IMPLS_VO += ObjectsImpl.vo
ObjectsAppl.vo: ObjectsImpl.vo Objects.vo IndicesImpl.vo CapabilitiesAppl.vo
APPLS_VO += ObjectsAppl.vo

# Objects Convenience

OBJECTS_CONV_REQ := Objects.vo Indices.vo Capabilities.vo OrdFMapEquiv.vo \
	OptionMap2.vo FMapFoldEqual.vo OrderedTypeEquiv.vo FMapExists.vo \
	FMapFacts2.vo

Objects_Conv.v : typeify.pl Objects_ConvImpl.v
	perl typeify.pl Objects_ConvImpl.v $@
GENERATED_V_FILES += Objects_Conv.v
Objects_Conv.vo: $(OBJECTS_CONV_REQ)
TYPES_VO += Objects_Conv.vo
Objects_ConvImpl.vo: $(OBJECTS_CONV_REQ) Objects_Conv.vo
IMPLS_VO += Objects_ConvImpl.vo
Objects_ConvAppl.vo: Objects_ConvImpl.vo ObjectsAppl.vo
APPLS_VO += Objects_ConvAppl.vo

# The System State

SYSTEM_STATE_REQ := Objects.vo ObjectLabels.vo ObjectTypes.vo ObjectSchedules.vo

SystemState.vo: $(SYSTEM_STATE_REQ)
TYPES_VO += SystemState.vo
SystemStateImpl.vo: $(SYSTEM_STATE_REQ) SystemState.vo 
IMPLS_VO += SystemStateImpl.vo
SystemStateAppl.vo: SystemStateImpl.vo ObjectsAppl.vo
APPLS_VO += SystemStateAppl.vo

# System State Convenience

SYSTEM_STATE_CONV_REQ := SystemState.vo OptionMap2.vo CapIndexListFacts.vo \
		     Objects_Conv.vo Capabilities_Conv.vo FMapExists.vo \
		     OrdFMapEquiv.vo ObjectLabels.vo ObjectTypes.vo \
		     ObjectSchedules.vo OptionSumbool.vo OrderedTypeEquiv.vo \
		     FMapFoldEqual.vo Objects_Conv.vo Capabilities_Conv.vo \
		     Capabilities_ConvImpl.vo Objects_ConvImpl.vo CapIndexListFacts.vo \
		     FMapAdd.vo

SystemState_Conv.v : typeify.pl SystemState_ConvImpl.v
	perl typeify.pl  SystemState_ConvImpl.v $@
GENERATED_V_FILES += SystemState_Conv.v
SystemState_Conv.vo: $(SYSTEM_STATE_CONV_REQ)
TYPES_VO += SystemState_Conv.vo
SystemState_ConvImpl.vo: $(SYSTEM_STATE_CONV_REQ) SystemState_Conv.vo
IMPLS_VO += SystemState_ConvImpl.vo
SystemState_ConvAppl.vo: SystemState_ConvImpl.vo SystemStateAppl.vo
APPLS_VO += SystemState_ConvAppl.vo

# Semantics Definitions and Lemmas

SEMANTICS_DEFINITIONS_REQ := OptionMap2.vo Sumbool_dec.vo SystemState_Conv.vo Iff_Equiv.vo \
			AccessRights.vo SystemState.vo SystemState_ConvImpl.vo

SemanticsDefinitions.v : typeify.pl SemanticsDefinitionsImpl.v
	perl typeify.pl SemanticsDefinitionsImpl.v $@
GENERATED_V_FILES += SemanticsDefinitions.v
SemanticsDefinitions.vo : $(SEMANTICS_DEFINITIONS_REQ)
TYPES_VO += SemanticsDefinitions.vo
SemanticsDefinitionsImpl.vo: $(SEMANTICS_DEFINITIONS_REQ) SemanticsDefinitions.vo 
IMPLS_VO += SemanticsDefinitionsImpl.vo
SemanticsDefinitionsAppl.vo: SemanticsDefinitionsImpl.vo SystemState_ConvAppl.vo
APPLS_VO += SemanticsDefinitionsAppl.vo

# System Semantics

SEMANTICS_REQ := SemanticsDefinitions.vo SystemState.vo OptionMap2.vo RefSets.vo \
		 References.vo Capabilities.vo Indices.vo Objects.vo 

Semantics.v : typeify.pl SemanticsImpl.v
	perl typeify.pl SemanticsImpl.v $@
GENERATED_V_FILES += Semantics.v
Semantics.vo: $(SEMANTICS_REQ)
TYPES_VO += Semantics.vo
SemanticsImpl.vo: $(SEMANTICS_REQ) Semantics.vo Sumbool_dec.vo 
IMPLS_VO += SemanticsImpl.vo
SemanticsAppl.vo: SemanticsImpl.vo Semantics.vo SemanticsDefinitionsAppl.vo
APPLS_VO += SemanticsAppl.vo

# Semantics Convenience

SEMANTICS_CONV_REQ := Semantics.vo CapIndexListFacts.vo OptionMap2.vo AccessRights.vo AccessRightSets.vo \
		      References.vo Capabilities.vo Indices.vo Objects.vo SystemState.vo SemanticsDefinitions.vo \
		      SemanticsDefinitionsImpl.vo

Semantics_Conv.v : typeify.pl Semantics_ConvImpl.v
	perl typeify.pl Semantics_ConvImpl.v $@
GENERATED_V_FILES += Semantics_Conv.v
Semantics_Conv.vo: $(SEMANTICS_CONV_REQ)
TYPES_VO += Semantics_Conv.vo
Semantics_ConvImpl.vo: $(SEMANTICS_CONV_REQ) Semantics_Conv.vo
IMPLS_VO += Semantics_ConvImpl.vo
Semantics_ConvAppl.vo: Semantics_ConvImpl.vo SemanticsAppl.vo
APPLS_VO += Semantics_ConvAppl.vo

# Execution

EXECUTION_REQ := Semantics_Conv.vo Semantics_ConvImpl.vo

Execution.v : typeify.pl ExecutionImpl.v
	perl typeify.pl ExecutionImpl.v $@
GENERATED_V_FILES += Execution.v
Execution.vo: $(EXECUTION_REQ)
TYPES_VO += Execution.vo
ExecutionImpl.vo: $(EXECUTION_REQ) Execution.vo
IMPLS_VO += ExecutionImpl.vo
ExecutionAppl.vo: ExecutionImpl.vo Semantics_ConvAppl.vo
APPLS_VO += ExecutionAppl.vo

# Access Graphs and Reasoning

# No longer used or needed
#Access.vo : References.vo AccessRights.vo

ACCESSEDGE_REQ := References.vo AccessRights.vo

AccessEdge.v: typeify.pl AccessEdgeImpl.v
	perl typeify.pl AccessEdgeImpl.v $@
GENERATED_V_FILES += AccessEdge.v
AccessEdge.vo: $(ACCESSEDGE_REQ)
TYPES_VO += AccessEdge.vo
AccessEdgeImpl.vo: $(ACCESSEDGE_REQ) AccessEdge.vo
IMPLS_VO += AccessEdgeImpl.vo
AccessEdgeAppl.vo: AccessEdge.vo AccessEdgeImpl.vo ReferencesImpl.vo
APPLS_VO += AccessEdgeAppl.vo

RefSets.vo : FSetAddEq.vo References.vo  FoldEqual.vo FSetEqEqual.vo

ACCESSGRAPHS_REQ := AccessEdge.vo FSetAddEq.vo FoldEqual.vo FSetEqEqual.vo FSetExists.vo

AccessGraphs.v: typeify.pl AccessGraphsImpl.v
	perl typeify.pl AccessGraphsImpl.v $@
GENERATED_V_FILES += AccessGraphs.v
AccessGraphs.vo: $(ACCESSGRAPHS_REQ)
TYPES_VO += AccessGraphs.vo
AccessGraphsImpl.vo: $(ACCESSGRAPHS_REQ) AccessGraphs.vo
IMPLS_VO += AccessGraphsImpl.vo
AccessGraphsAppl.vo: AccessGraphs.vo AccessGraphsImpl.vo ReferencesImpl.vo AccessEdgeAppl.vo
APPLS_VO += AccessGraphsAppl.vo

SEQUENTIALACCESS_REQ := AccessEdge.vo FSetAddEq.vo \
		     RefSets.vo Sumbool2.vo AccessGraphs.vo \
		     Sumbool_dec.vo OptionSumbool.vo

SequentialAccess.v: typeify.pl SequentialAccessImpl.v
	perl typeify.pl SequentialAccessImpl.v $@
GENERATED_V_FILES += SequentialAccess.v
SequentialAccess.vo: $(SEQUENTIALACCESS_REQ)
TYPES_VO += SequentialAccess.vo
SequentialAccessImpl.vo: $(SEQUENTIALACCESS_REQ) SequentialAccess.vo
IMPLS_VO += SequentialAccessImpl.vo
SequentialAccessAppl.vo: SequentialAccess.vo SequentialAccessImpl.vo ReferencesImpl.vo AccessEdgeAppl.vo AccessGraphsAppl.vo RefSetsAppl.vo
APPLS_VO += SequentialAccessAppl.vo

# Access Graphs to Semantics

# No longer used or needed
#PotentialAccess.vo : SequentialAccess.vo References.vo

# Direct Access definition and lemmas.

DIRECT_ACCESS_REQ := SequentialAccess.vo Sumbool_dec.vo OrdFMapEquiv.vo \
		  OptionMap2.vo OptionSumbool.vo FMapExists.vo OrdFMapEquiv.vo \
		  FMapAdd.vo FoldEqual.vo OrderedTypeEquiv.vo CapIndexListFacts.vo \
		  Semantics_Conv.vo FoldOrder.vo AccessRights.vo AccessRightSets.vo \
		  Semantics_ConvImpl.vo

#DirectAccess.v : typeify.pl DirectAccessImpl.v
#	perl typeify.pl DirectAccessImpl.v $@
#GENERATED_V_FILES += DirectAccess.v
#DirectAccess.vo : $(DIRECT_ACCESS_REQ)
#TYPES_VO += DirectAccess.vo
DirectAccessImpl.vo: $(DIRECT_ACCESS_REQ)
IMPLS_VO += DirectAccessImpl.vo
#DirectAccessAppl.vo: DirectAccessImpl.vo Semantics_ConvAppl.vo Semantics_Conv.vo
#APPLS_VO += DirectAccessAppl.vo

# Direct Access related to each semantic operation

DIRECT_ACCESS_SEMANTICS_REQ := SequentialAccess.vo Sumbool_dec.vo OrdFMapEquiv.vo \
		  OptionMap2.vo OptionSumbool.vo FMapExists.vo OrdFMapEquiv.vo \
		  FMapAdd.vo FoldEqual.vo OrderedTypeEquiv.vo CapIndexListFacts.vo \
		  Semantics_Conv.vo FoldOrder.vo Semantics_ConvImpl.vo

#DirectAccessSemantics.v : typeify.pl DirectAccessSemanticsImpl.v
#	perl typeify.pl DirectAccessSemanticsImpl.v $@
#GENERATED_V_FILES += DirectAccessSemantics.v
#DirectAccessSemantics.vo : $(DIRECT_ACCESS_SEMANTICS_REQ)
#TYPES_VO += DirectAccessSemantics.vo
DirectAccessSemanticsImpl.vo: DirectAccessImpl.vo $(DIRECT_ACCESS_SEMANTICS_REQ)
IMPLS_VO += DirectAccessSemanticsImpl.vo
#DirectAccessSemanticsAppl.vo: DirectAccessSemanticsImpl.vo DirectAccessAppl.vo
#APPLS_VO += DirectAccessSemanticsAppl.vo

# Direct Access approximating all operations

DIRECT_ACCESS_APPROX_REQ := SequentialAccess.vo Sumbool_dec.vo OrdFMapEquiv.vo \
		  OptionMap2.vo OptionSumbool.vo FMapExists.vo OrdFMapEquiv.vo \
		  FMapAdd.vo FoldEqual.vo OrderedTypeEquiv.vo CapIndexListFacts.vo \
		  Semantics_Conv.vo FoldOrder.vo Semantics_ConvImpl.vo \
		  DirectAccessSemanticsImpl.vo

#IMPLS_VO += DirectAccessApproxImpl.vo
#DirectAccessApprox.v : typeify.pl DirectAccessApproxImpl.v
#	perl typeify.pl DirectAccessApproxImpl.v $@
#GENERATED_V_FILES += DirectAccessApprox.v
#DirectAccessApprox.vo : $(DIRECT_ACCESS_APPROX_REQ)
#TYPES_VO += DirectAccessApprox.vo
DirectAccessApproxImpl.vo: DirectAccessSemanticsImpl.vo $(DIRECT_ACCESS_APPROX_REQ)
IMPLS_VO += DirectAccessApproxImpl.vo
#DirectAccessApproxAppl.vo: DirectAccessApproxImpl.vo DirectAccessSemanticsAppl.vo

# Potential Access approximating all operations

Attenuation.vo: DirectAccessApproxImpl.vo
IMPLS_VO += Attenuation.vo
AttenuationAppl.vo : Attenuation.vo Semantics_ConvAppl.vo ReferencesImpl.vo \
	 CapabilitiesAppl.vo IndicesImpl.vo ObjectsAppl.vo SystemStateAppl.vo \
	 SemanticsDefinitionsAppl.vo SemanticsAppl.vo
APPLS_VO += AttenuationAppl.vo 

AccessExecutionImpl.vo :  OptionSumbool.vo AccessRights.vo \
	 References.vo Capabilities.vo Indices.vo Objects.vo ObjectLabels.vo \
	 SystemState.vo SemanticsDefinitions.vo Semantics.vo Semantics_Conv.vo \
	 AccessRightSets.vo Execution.vo RefSets.vo Attenuation.vo \
	 OptionMap2.vo Iff_Equiv.vo Sumbool_dec.vo
IMPLS_VO += AccessExecutionImpl.vo
AccessExecutionAppl.vo : AccessExecutionImpl.vo Semantics_ConvAppl.vo ReferencesImpl.vo \
	 CapabilitiesAppl.vo IndicesImpl.vo ObjectsAppl.vo SystemStateAppl.vo \
	 SemanticsDefinitionsAppl.vo SemanticsAppl.vo ExecutionAppl.vo
APPLS_VO += AccessExecutionAppl.vo 

MUTABILITY_REQ:= Execution.vo SequentialAccess.vo

Mutability.v: typeify.pl MutabilityImpl.v
	perl typeify.pl MutabilityImpl.v $@
GENERATED_V_FILES += Mutability.v
Mutability.vo: $(MUTABILITY_REQ)
TYPES_VO += Mutability.vo
MutabilityImpl.vo: $(MUTABILITY_REQ) Mutability.vo
IMPLS_VO += Mutability.vo
MutabilityAppl.v: Mutability.vo MutabilityImpl.vo SequentialAccessAppl.vo
APPLS_VO += MutabilityAppl.vo


MUTATION_REQ:=Iff_Equiv.vo FSetExists.vo Execution.vo

Mutation.v: typeify.pl MutationImpl.v
	perl typeify.pl MutationImpl.v $@
GENERATED_V_FILES += Mutation.v
Mutation.vo: $(MUTATION_REQ)
TYPES_VO += Mutation.vo
MutationImpl.vo: $(MUTATION_REQ) Mutation.vo
IMPLS_VO += MutationImpl.vo
MutationAppl.vo: Mutation.vo MutationImpl.vo ExecutionAppl.vo SemanticsAppl.vo
APPLS_VO += MutationAppl.vo


MUTABLE_SUBSET_REQ:=Mutation.vo AccessExecutionImpl.vo SequentialAccess.vo FSetAddEq.vo MutabilityImpl.vo

MutableSubset.v: typeify.pl MutableSubsetImpl.v
	perl typeify.pl MutableSubsetImpl.v $@
GENERATED_V_FILES += MutableSubset.v
MutableSubset.vo: $(MUTABLE_SUBSET_REQ)
TYPES_VO += MutableSubset.vo
MutableSubsetImpl.vo: $(MUTABLE_SUBSET_REQ) MutableSubset.vo
IMPLS_VO += MutableSubsetImpl.vo
MutableSubsetAppl.vo: MutableSubset.vo MutableSubsetImpl.vo ExecutionAppl.vo SequentialAccessAppl.vo MutationAppl.vo
APPLS_VO += MutableSubsetAppl.vo



SUBSYSTEM_REQ:=Mutation.vo Mutability.vo Execution.vo RefSets.vo CapSets.vo

Subsystem.v: typeify.pl SubsystemImpl.v
	perl typeify.pl SubsystemImpl.v $@
GENERATED_V_FILES += Subsystem.v
Subsystem.vo: $(SUBSYSTEM_REQ)
TYPES_VO += Subsystem.vo
SubsystemImpl.vo: $(SUBSYSTEM_REQ) Subsystem.vo
IMPLS_VO += SubsystemImpl.vo
SubsystemAppl.vo: Subsystem.vo SubsystemImpl.vo ExecutionAppl.vo SequentialAccessAppl.vo CapSetsAppl.vo
APPLS_VO += SubsystemAppl.vo



CONFINEMENT_REQ:= MutableSubset.vo Mutation.vo AccessExecutionImpl.vo SequentialAccess.vo MutabilityImpl.vo \
		AccessExecutionImpl.vo Irrelevance.vo  MutableSubsetImpl.vo Subsystem.vo

Confinement.v: typeify.pl ConfinementImpl.v
	perl typeify.pl ConfinementImpl.v $@
GENERATED_V_FILES += Confinement.v
Confinement.vo: $(CONFINEMENT_REQ)
TYPES_VO += Confinement.vo
ConfinementImpl.vo: $(CONFINEMENT_REQ) Confinement.vo
IMPLS_VO += ConfinementImpl.vo
ConfinementAppl.vo: Confinement.vo ConfinementImpl.vo MutableSubsetAppl.vo SubsystemAppl.vo
APPLS_VO += ConfinementAppl.vo



.PHONY: all impls appls types clean coqdoc

types : $(TYPES_VO)

impls : $(IMPLS_VO)

appls : $(APPLS_VO)

all : coqdoc types impls appls

coqdoc : $(GENERATED_V_FILES)
	mkdir -p coqdoc
	coqdoc --latex -g --no-externals --no-index -d coqdoc *.v 

clean :
	rm -f *.vo *.glob *.html *.css *~ *.mem $(GENERATED_V_FILES)
	rm -rf coqdoc

