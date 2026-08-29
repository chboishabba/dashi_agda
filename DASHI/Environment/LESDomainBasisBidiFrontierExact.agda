module DASHI.Environment.LESDomainBasisBidiFrontierExact where

open import DASHI.Core.Prelude

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Chemistry.ExistingContentBridge as ChemistryReuse
import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Environment.FunctionalEcology as Ecology
import DASHI.Environment.QuantitiesConservation as Conservation
import DASHI.Environment.SpatialTransport as Spatial

------------------------------------------------------------------------
-- LES DOMAIN-BASIS BIDI FRONTIER
--
-- Repository-native architecture audit.
--
-- BIDI discipline:
--   FORWARD  : expose the strongest actual in-repo producers already present;
--   BACKWARD : expose the weakest domain sockets demanded by the Stage-7
--              inference / discrimination architecture;
--   FRONTIER : do not call a vocabulary/graph carrier a mechanistic model,
--              and do not rebuild chemistry/ecology/transport semantics here.
--
-- No external scientific claim is introduced in this module.  It only records
-- and composes existing DASHI theorem/grammar surfaces.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Forward producers already present in the repository.
------------------------------------------------------------------------

ChemistryStateCarrier : Set
ChemistryStateCarrier = Chemistry.ReactionNetwork

ChemistryProcessCarrier : Set
ChemistryProcessCarrier = Chemistry.Transition

ChemistrySpeciesCarrier : Set
ChemistrySpeciesCarrier = Chemistry.Species

EcologicalEntityCarrier : Set
EcologicalEntityCarrier = Ecology.FunctionalGroup

EcologicalInteractionCarrier : Set
EcologicalInteractionCarrier = Ecology.Interaction

FungalGuildCarrier : Set
FungalGuildCarrier = Ecology.FungalGuild

MycorrhizalCandidateCarrier : Set
MycorrhizalCandidateCarrier = Ecology.MycorrhizalCandidate

SpatialNodeCarrier : Set
SpatialNodeCarrier = Spatial.SpatialNode

SpatialTransportKindCarrier : Set
SpatialTransportKindCarrier = Spatial.TransportKind

ConservationCarrier : Set
ConservationCarrier = Conservation.ConservationBundle

------------------------------------------------------------------------
-- These labels are deliberately about formal producer strength, not scientific
-- truth or completeness.
------------------------------------------------------------------------

data ProducerStrength : Set where
  vocabularyOnly
  relationalGrammar
  transitionGrammar
  transportConservationGrammar
  quantitativeLawSurface
  empiricalMechanisticModel
  : ProducerStrength

data EnvironmentalDomain : Set where
  chemistry
  plantEcology
  fungalEcology
  trophicEcology
  hydrologyTransport
  soilBiogeochemistry
  geologyGeomorphology
  : EnvironmentalDomain

record ForwardDomainBasis : Set₁ where
  constructor forwardDomainBasis
  field
    domain : EnvironmentalDomain
    carrier : Set
    strength : ProducerStrength
    repositoryOwner : String
    exactBoundary : String

open ForwardDomainBasis public

chemistryForwardBasis : ForwardDomainBasis
chemistryForwardBasis =
  forwardDomainBasis
    chemistry
    Chemistry.ReactionNetwork
    transitionGrammar
    "DASHI.Chemistry.TransitionKernel + DASHI.Chemistry.ExistingContentBridge"
    "Species, reactions, rate-law kinds, environment fields, compartments, interfaces, conservation and hybrid-event grammar exist; quantitative-law and wet-lab authority remain separately gated."

plantForwardBasis : ForwardDomainBasis
plantForwardBasis =
  forwardDomainBasis
    plantEcology
    Ecology.FunctionalGroup
    relationalGrammar
    "DASHI.Environment.FunctionalEcology"
    "Producer, nitrogen-fixer, nutrient-scavenger, rooting, cover, riparian, pollination and habitat roles exist, but this is functional ecology rather than a plant physiology/growth model."

fungalForwardBasis : ForwardDomainBasis
fungalForwardBasis =
  forwardDomainBasis
    fungalEcology
    Ecology.FungalGuild
    relationalGrammar
    "DASHI.Environment.FunctionalEcology"
    "AM, ectomycorrhizal, ericoid, saprotrophic, endophytic and pathogenic fungal guilds plus compatibility-gated mycorrhizal candidates exist; no general fungal growth/network dynamics are asserted."

trophicForwardBasis : ForwardDomainBasis
trophicForwardBasis =
  forwardDomainBasis
    trophicEcology
    Ecology.Interaction
    relationalGrammar
    "DASHI.Environment.FunctionalEcology"
    "Predator, grazer, producer, decomposer and pathogen roles plus signed context-gated interactions exist; this is not yet a quantitative trophic-flow or population-dynamics model."

hydrologyTransportForwardBasis : ForwardDomainBasis
hydrologyTransportForwardBasis =
  forwardDomainBasis
    hydrologyTransport
    Spatial.TransportKind
    transportConservationGrammar
    "DASHI.Environment.SpatialTransport + DASHI.Environment.QuantitiesConservation"
    "Directed surface-water/groundwater/sediment/dissolved-nutrient transport and typed water/nutrient/sediment balance receipts exist; constitutive hydrology is not supplied by these grammars alone."

soilBiogeochemistryForwardBasis : ForwardDomainBasis
soilBiogeochemistryForwardBasis =
  forwardDomainBasis
    soilBiogeochemistry
    Conservation.ConservationBundle
    transportConservationGrammar
    "DASHI.Environment.QuantitiesConservation + DASHI.Chemistry.TransitionKernel + DASHI.Environment.FunctionalEcology"
    "Water/N/P/C/sediment accounting can be composed with chemistry and ecological roles, but no canonical soil profile, sorption/mineralisation, root-uptake or microbial process model is identified here."

geologyGeomorphologyForwardBasis : ForwardDomainBasis
geologyGeomorphologyForwardBasis =
  forwardDomainBasis
    geologyGeomorphology
    Spatial.TransportKind
    vocabularyOnly
    "DASHI.Environment.SpatialTransport + DASHI.Environment.QuantitiesConservation"
    "Sediment transport/balance and earthwork quantities provide adjacent infrastructure; no canonical geology/mineral/stratigraphy/weathering/geomorphic evolution owner is identified by this audit."

------------------------------------------------------------------------
-- 2. Backward from PR #636 / Stage 7.
--
-- RobustExperimentInferenceFrontierExact names the generic obligations.  A
-- real LES domain also needs an application-supplied state/evolution/observer
-- surface on which those obligations can be discharged.
------------------------------------------------------------------------

stage7Obligations : List Robust.RobustnessObligation
stage7Obligations =
  Robust.modelDiscrepancy
  ∷ Robust.vectorStateParameterControl
  ∷ Robust.correlatedUncertainty
  ∷ Robust.experimentDesign
  ∷ Robust.quantitativeLocalIdentifiability
  ∷ Robust.heldOutRepairValidation
  ∷ []

record DomainMechanismSocket : Set₁ where
  constructor domainMechanismSocket
  field
    State : Set
    Control : Set
    Observation : Set
    Experiment : Set
    Residual : Set

    evolve : Control → State → State
    observe : State → Observation
    experimentObserve : Experiment → State → Observation

    -- Kept as a carrier rather than silently choosing probability semantics.
    discrepancyCarrier : State → Residual

open DomainMechanismSocket public

------------------------------------------------------------------------
-- Cross-domain ecological models additionally need literal coupling seams.
-- This avoids pretending that putting chemistry, plants and fungi in one
-- product type has established a causal interaction.
------------------------------------------------------------------------

record DomainCouplingSocket
    (SourceState TargetState Flux : Set) : Set₁ where
  constructor domainCouplingSocket
  field
    sourceToFlux : SourceState → Flux
    applyFlux : Flux → TargetState → TargetState
    couplingEvidenceReference : String
    scaleCompatibilityReference : String
    conservationReference : String

open DomainCouplingSocket public

------------------------------------------------------------------------
-- 3. Forward/backward cutset.
--
-- The strongest current producers are not uniformly the same kind:
-- chemistry has a rich transition grammar; ecology has a useful relational
-- grammar including plants/fungi/trophic roles; spatial/conservation owners
-- carry transport and material ledgers.  The missing common seam is the
-- domain-specific executable/quantitative mechanism + observation interface,
-- followed by typed cross-domain couplings.
------------------------------------------------------------------------

record BidiDomainCutset : Set where
  constructor bidiDomainCutset
  field
    chemistryTransitionGrammarPresent : Bool
    functionalPlantGrammarPresent : Bool
    fungalGuildGrammarPresent : Bool
    trophicInteractionGrammarPresent : Bool
    spatialTransportGrammarPresent : Bool
    materialConservationGrammarPresent : Bool

    canonicalPlantPhysiologyMechanismStillRequired : Bool
    canonicalFungalDynamicsMechanismStillRequired : Bool
    canonicalTrophicDynamicsMechanismStillRequired : Bool
    canonicalGeologyGeomorphologyMechanismStillRequired : Bool
    canonicalSoilBiogeochemistryMechanismStillRequired : Bool
    crossDomainCouplingReceiptsStillRequired : Bool
    stage7DiscrepancyAndExperimentReceiptsStillRequired : Bool

open BidiDomainCutset public

canonicalBidiDomainCutset : BidiDomainCutset
canonicalBidiDomainCutset =
  bidiDomainCutset
    true true true true true true
    true true true true true true true

------------------------------------------------------------------------
-- 4. Anti-promotion boundary.
------------------------------------------------------------------------

record LESDomainBasisBoundary : Set where
  constructor lesDomainBasisBoundary
  field
    functionalRoleVocabularyIsPlantPhysiology : Bool
    functionalRoleVocabularyIsPlantPhysiologyIsFalse :
      functionalRoleVocabularyIsPlantPhysiology ≡ false

    fungalGuildClassificationIsFungalDynamics : Bool
    fungalGuildClassificationIsFungalDynamicsIsFalse :
      fungalGuildClassificationIsFungalDynamics ≡ false

    signedInteractionGraphIsTrophicFlowModel : Bool
    signedInteractionGraphIsTrophicFlowModelIsFalse :
      signedInteractionGraphIsTrophicFlowModel ≡ false

    sedimentTransportVocabularyIsGeomorphology : Bool
    sedimentTransportVocabularyIsGeomorphologyIsFalse :
      sedimentTransportVocabularyIsGeomorphology ≡ false

    chemistryTransitionGrammarIsWetLabValidatedMechanism : Bool
    chemistryTransitionGrammarIsWetLabValidatedMechanismIsFalse :
      chemistryTransitionGrammarIsWetLabValidatedMechanism ≡ false

    productOfDomainCarriersProvesCrossDomainCausality : Bool
    productOfDomainCarriersProvesCrossDomainCausalityIsFalse :
      productOfDomainCarriersProvesCrossDomainCausality ≡ false

canonicalLESDomainBasisBoundary : LESDomainBasisBoundary
canonicalLESDomainBasisBoundary =
  lesDomainBasisBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
