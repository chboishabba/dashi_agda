module DASHI.Core.CriticalKnowledgeConcentrationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DisruptionBenefitHypothesisExact as Benefit
import DASHI.Core.CounterfactualDisruptionImpactExact as Impact
import DASHI.Core.CapabilityIndexedSelectorSalienceExact as Salience

------------------------------------------------------------------------
-- CRITICAL KNOWLEDGE CONCENTRATION, BIDI
--
-- Replaces the vague public phrase "knew too much" with explicit, separable
-- coordinates.  Forward direction assembles a bounded criticality profile from
-- source-backed receipts.  Reverse direction decomposes a strong criticality
-- claim back into the exact missing receipts required to justify it.
------------------------------------------------------------------------

data KnowledgeCoordinate : Set where
  publicKnowledge
  tacitImplementationKnowledge
  configurationSpecificKnowledge
  failureModeKnowledge
  integrationKnowledge
  networkKnowledge
  sensitiveOrRestrictedKnowledge
  : KnowledgeCoordinate

data CoordinateStatus : Set where
  coordinateSourceBacked
  coordinatePartial
  coordinateNotLocated
  coordinateKnownAbsent
  : CoordinateStatus

record KnowledgeCoordinateReceipt : Set where
  constructor knowledge-coordinate-receipt
  field
    personOrRole : String
    coordinate : KnowledgeCoordinate
    status : CoordinateStatus
    sourceReference : String
    boundedReading : String

open KnowledgeCoordinateReceipt public

------------------------------------------------------------------------
-- Criticality axes are separate from knowledge type.
------------------------------------------------------------------------

data CriticalityAxis : Set where
  uniqueness
  nonPublicness
  integrationBreadth
  replacementDifficulty
  strategicCapabilityRelevance
  : CriticalityAxis

record CriticalityReceipt : Set where
  constructor criticality-receipt
  field
    personOrRole : String
    axis : CriticalityAxis
    status : CoordinateStatus
    sourceReference : String
    boundedReading : String

open CriticalityReceipt public

record CriticalKnowledgeProfile : Set where
  constructor critical-knowledge-profile
  field
    personOrRole : String
    knowledgeReceipts : List KnowledgeCoordinateReceipt
    criticalityReceipts : List CriticalityReceipt
    profileReference : String
    boundedClaim : String

open CriticalKnowledgeProfile public

------------------------------------------------------------------------
-- Reverse BIDI obligations.
--
-- A strong "critical knowledge concentration" claim is not generated merely by
-- a senior title, long tenure, classification, publication count, or strategic
-- field.  It must discharge each required criticality axis independently.
------------------------------------------------------------------------

record StrongCriticalKnowledgeClaim : Set where
  constructor strong-critical-knowledge-claim
  field
    profile : CriticalKnowledgeProfile
    uniquenessReceipt : CriticalityReceipt
    uniquenessOwned : axis uniquenessReceipt ≡ uniqueness
    nonPublicnessReceipt : CriticalityReceipt
    nonPublicnessOwned : axis nonPublicnessReceipt ≡ nonPublicness
    integrationBreadthReceipt : CriticalityReceipt
    integrationBreadthOwned : axis integrationBreadthReceipt ≡ integrationBreadth
    replacementDifficultyReceipt : CriticalityReceipt
    replacementDifficultyOwned : axis replacementDifficultyReceipt ≡ replacementDifficulty
    strategicRelevanceReceipt : CriticalityReceipt
    strategicRelevanceOwned : axis strategicRelevanceReceipt ≡ strategicCapabilityRelevance

open StrongCriticalKnowledgeClaim public

data MissingCriticalityReceipt : Set where
  needUniquenessEvidence
  needNonPublicnessEvidence
  needIntegrationBreadthEvidence
  needReplacementDifficultyEvidence
  needStrategicRelevanceEvidence
  : MissingCriticalityReceipt

record CriticalKnowledgeAcquisitionTarget : Set where
  constructor critical-knowledge-acquisition-target
  field
    personOrRole : String
    missingReceipt : MissingCriticalityReceipt
    preferredEvidence : String
    fallbackEvidence : String
    promotionRule : String

open CriticalKnowledgeAcquisitionTarget public

------------------------------------------------------------------------
-- Cross-pollination bridges.
------------------------------------------------------------------------

knowledgeAxisFromBenefit : Benefit.KnowledgeValueAxis → KnowledgeCoordinate
knowledgeAxisFromBenefit Benefit.publishedKnowledge = publicKnowledge
knowledgeAxisFromBenefit Benefit.tacitImplementationKnowledge = tacitImplementationKnowledge
knowledgeAxisFromBenefit Benefit.failureModeKnowledge = failureModeKnowledge
knowledgeAxisFromBenefit Benefit.configurationKnowledge = configurationSpecificKnowledge
knowledgeAxisFromBenefit Benefit.programmeIntegrationKnowledge = integrationKnowledge
knowledgeAxisFromBenefit Benefit.technicalNetworkKnowledge = networkKnowledge
knowledgeAxisFromBenefit Benefit.lowReplaceabilityKnowledge = tacitImplementationKnowledge

record ImpactSupportsReplacementDifficulty
    (impact : Impact.DepartureImpactProfile) : Set where
  constructor impact-supports-replacement-difficulty
  field
    hasReplacementEvidence : Bool
    hasReplacementEvidenceIsTrue : hasReplacementEvidence ≡ true
    supportReference : String

open ImpactSupportsReplacementDifficulty public

record SelectorCanRecogniseCriticalKnowledge
    (selector : Salience.CapabilityAwareSelector)
    (contribution : Salience.CapabilityContribution)
    (profile : CriticalKnowledgeProfile) : Set where
  constructor selector-can-recognise-critical-knowledge
  field
    contributionSalient : Salience.PersonCapabilitySalientTo selector contribution
    criticalityRecognitionReference : String

open SelectorCanRecogniseCriticalKnowledge public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record CriticalKnowledgeBoundary : Set where
  constructor critical-knowledge-boundary
  field
    publishedWorkImpliesNoTacitKnowledge : Bool
    publishedWorkImpliesNoTacitKnowledgeIsFalse : publishedWorkImpliesNoTacitKnowledge ≡ false
    seniorityImpliesUniqueKnowledge : Bool
    seniorityImpliesUniqueKnowledgeIsFalse : seniorityImpliesUniqueKnowledge ≡ false
    classifiedFieldImpliesPersonHeldClassifiedKnowledge : Bool
    classifiedFieldImpliesPersonHeldClassifiedKnowledgeIsFalse :
      classifiedFieldImpliesPersonHeldClassifiedKnowledge ≡ false
    longTenureImpliesReplacementDifficulty : Bool
    longTenureImpliesReplacementDifficultyIsFalse : longTenureImpliesReplacementDifficulty ≡ false
    criticalKnowledgeImpliesTargeting : Bool
    criticalKnowledgeImpliesTargetingIsFalse : criticalKnowledgeImpliesTargeting ≡ false
    targetingImpliesHarm : Bool
    targetingImpliesHarmIsFalse : targetingImpliesHarm ≡ false
    strongClaimRequiresIndependentCriticalityReceipts : Bool
    strongClaimRequiresIndependentCriticalityReceiptsIsTrue :
      strongClaimRequiresIndependentCriticalityReceipts ≡ true

canonicalCriticalKnowledgeBoundary : CriticalKnowledgeBoundary
canonicalCriticalKnowledgeBoundary = critical-knowledge-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl
