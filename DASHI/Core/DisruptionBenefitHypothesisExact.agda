module DASHI.Core.DisruptionBenefitHypothesisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- DISRUPTION-BENEFIT / CAPABILITY-AWARE HYPOTHESIS CORE
--
-- Evidence-gathering only.  A beneficiary, capability precedent, or economic
-- exposure is not a perpetrator identification.
------------------------------------------------------------------------

data DisruptionBenefitKind : Set where
  delaysCompetingCapability
  removesTacitKnowledge
  removesIntegrationKnowledge
  reducesKeyPersonRedundancy
  increasesProgrammeFriction
  shiftsFundingOrContractPosition
  preservesIncumbentEconomicRent
  strategicDenialBenefit
  unresolvedBenefit
  : DisruptionBenefitKind

data KnowledgeValueAxis : Set where
  publishedKnowledge
  tacitImplementationKnowledge
  failureModeKnowledge
  configurationKnowledge
  programmeIntegrationKnowledge
  technicalNetworkKnowledge
  lowReplaceabilityKnowledge
  : KnowledgeValueAxis

record CapabilityValueProfile : Set where
  constructor capability-value-profile
  field
    personOrRole : String
    axes : List KnowledgeValueAxis
    sourceReference : String
    boundedReading : String

open CapabilityValueProfile public

record DisruptionBeneficiaryHypothesis : Set where
  constructor disruption-beneficiary-hypothesis
  field
    actorClass : String
    affectedCapability : String
    benefitKind : DisruptionBenefitKind
    benefitMechanism : String
    sourceOrEconomicBasis : String
    evidenceNeededForCaseSpecificity : String

open DisruptionBeneficiaryHypothesis public

------------------------------------------------------------------------
-- Historical mode-of-action analogues are separate from case evidence.
------------------------------------------------------------------------

data PrecedentStrength : Set where
  sourceBackedHistoricalPrecedent
  boundedAnalogyOnly
  unresolvedPrecedent
  : PrecedentStrength

record MultidisciplinaryDisruptionPrecedent : Set where
  constructor multidisciplinary-disruption-precedent
  field
    precedentName : String
    actorAttribution : String
    integratedKnowledgeDomains : List String
    strategicObjective : String
    strength : PrecedentStrength
    sourceReference : String
    analogyBoundary : String

open MultidisciplinaryDisruptionPrecedent public

------------------------------------------------------------------------
-- Energy-transition hypotheses.
------------------------------------------------------------------------

data EnergyTransitionRelevance : Set where
  directFusionPower
  directFissionPower
  electrificationEnabling
  industrialHeatOrHydrogenEnabling
  propulsionOnly
  weakOrIndirectEnergyRelevance
  noEstablishedEnergyRelevance
  : EnergyTransitionRelevance

record EnergyTransitionProfile : Set where
  constructor energy-transition-profile
  field
    personOrWork : String
    relevance : EnergyTransitionRelevance
    incumbentExposureHypothesis : String
    sourceReference : String
    falsifier : String

open EnergyTransitionProfile public

------------------------------------------------------------------------
-- Matched-control discriminator.
------------------------------------------------------------------------

record MatchedControlDesign : Set where
  constructor matched-control-design
  field
    casePerson : String
    matchingAxes : List String
    candidateFeature : String
    requiredComparison : String
    antiCherryPickRule : String

open MatchedControlDesign public

record DisruptionBenefitBoundary : Set where
  constructor disruption-benefit-boundary
  field
    beneficiaryImpliesPerpetrator : Bool
    beneficiaryImpliesPerpetratorIsFalse : beneficiaryImpliesPerpetrator ≡ false
    historicalPrecedentImpliesCaseAttribution : Bool
    historicalPrecedentImpliesCaseAttributionIsFalse : historicalPrecedentImpliesCaseAttribution ≡ false
    publicWorkMeansNoTacitKnowledge : Bool
    publicWorkMeansNoTacitKnowledgeIsFalse : publicWorkMeansNoTacitKnowledge ≡ false
    economicExposureEstablishesMotive : Bool
    economicExposureEstablishesMotiveIsFalse : economicExposureEstablishesMotive ≡ false
    matchedControlsRequiredForRosterEnrichmentClaim : Bool
    matchedControlsRequiredForRosterEnrichmentClaimIsTrue : matchedControlsRequiredForRosterEnrichmentClaim ≡ true

canonicalDisruptionBenefitBoundary : DisruptionBenefitBoundary
canonicalDisruptionBenefitBoundary = disruption-benefit-boundary
  false refl
  false refl
  false refl
  false refl
  true refl
