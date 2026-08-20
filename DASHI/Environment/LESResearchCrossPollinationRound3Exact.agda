module DASHI.Environment.LESResearchCrossPollinationRound3Exact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Third LES cross-pollination round.  The main result of the Animalexic /
-- SeaMeInIt / LES comparison is not another LES-only record family: it is the
-- extraction of a project-neutral reopenable consumer/intervention kernel in
-- DASHI.Core.ReopenableConsumerInterventionKernelExact.
--
-- This module shows that existing LES round-2 spatial aggregation machinery is
-- an instance of that generic intertwining kernel and records the remaining
-- cross-project reuse boundaries.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core
import DASHI.Environment.LESResearchCrossPollinationRound2Exact as Round2

------------------------------------------------------------------------
-- 1. LES MAUP descent is a specialization of the generic intertwiner.
------------------------------------------------------------------------

spatialAggregationToGenericIntertwiner :
  ∀ {Fine Coarse FineResult CoarseResult}
    {aggregation : Round2.SpatialAggregation Fine Coarse}
    {analyseFine : Fine → FineResult}
    {analyseCoarse : Coarse → CoarseResult}
    {aggregateResult : FineResult → CoarseResult} →
  Round2.AggregationIntertwiner
    aggregation analyseFine analyseCoarse aggregateResult →
  Core.Intertwiner
    (Round2.aggregate aggregation)
    aggregateResult
    analyseFine
    analyseCoarse
spatialAggregationToGenericIntertwiner witness =
  Core.intertwiner (Round2.commutes witness)

maupDefectToGenericIntertwiningDefect :
  ∀ {Fine Coarse FineResult CoarseResult}
    {aggregation : Round2.SpatialAggregation Fine Coarse}
    {analyseFine : Fine → FineResult}
    {analyseCoarse : Coarse → CoarseResult}
    {aggregateResult : FineResult → CoarseResult} →
  Round2.MAUPDefect
    aggregation analyseFine analyseCoarse aggregateResult →
  Core.IntertwiningDefect
    (Round2.aggregate aggregation)
    aggregateResult
    analyseFine
    analyseCoarse
maupDefectToGenericIntertwiningDefect defect =
  Core.intertwiningDefect
    (Round2.witnessFineState defect)
    (Round2.descentFails defect)

maupDefectContradictsGenericIntertwiner :
  ∀ {Fine Coarse FineResult CoarseResult}
    {aggregation : Round2.SpatialAggregation Fine Coarse}
    {analyseFine : Fine → FineResult}
    {analyseCoarse : Coarse → CoarseResult}
    {aggregateResult : FineResult → CoarseResult} →
  Round2.AggregationIntertwiner
    aggregation analyseFine analyseCoarse aggregateResult →
  Round2.MAUPDefect
    aggregation analyseFine analyseCoarse aggregateResult →
  ⊥
maupDefectContradictsGenericIntertwiner intertwiner defect =
  Core.intertwiningDefectContradictsIntertwiner
    (spatialAggregationToGenericIntertwiner intertwiner)
    (maupDefectToGenericIntertwiningDefect defect)

------------------------------------------------------------------------
-- 2. LES-specific aliases for the project-neutral kernel.
------------------------------------------------------------------------

LESAlternativeFamily : Set → Set
LESAlternativeFamily = Core.LiveAlternativeFamily

LESBoundedEnumeration : ∀ {Item : Set} → (Item → Set) → Set₁
LESBoundedEnumeration = Core.BoundedEnumeration

LESProofCarryingReopenableState :
  (Carrier Change : Set) → (Carrier → Set) → Set₁
LESProofCarryingReopenableState = Core.ProofCarryingReopenableState

------------------------------------------------------------------------
-- 3. Cross-project reuse status.
------------------------------------------------------------------------

record LESRound3CrossProjectReuseStatus : Set where
  constructor lesRound3CrossProjectReuseStatus
  field
    consumerDescentExtractedToCore : Bool
    genericIntertwiningDefectExtractedToCore : Bool
    activeReopenableRefutedTriageExtractedToCore : Bool
    evidenceDispositionAndProvenanceRootsExtractedToCore : Bool
    uncertaintyAxesExtractedToCore : Bool
    authorityPromotionExtractedToCore : Bool
    proofCarryingReopenableStateExtractedToCore : Bool
    boundedLanguageCompletenessExtractedToCore : Bool
    lesMaupNowBridgesToGenericIntertwiner : Bool
    domainScienceRemainsOutsideGenericKernel : Bool

open LESRound3CrossProjectReuseStatus public

canonicalLESRound3CrossProjectReuseStatus : LESRound3CrossProjectReuseStatus
canonicalLESRound3CrossProjectReuseStatus =
  lesRound3CrossProjectReuseStatus
    true true true true true true true true true true

------------------------------------------------------------------------
-- 4. Feedback boundaries from Animalexic and SeaMeInIt.
--
-- These are architecture obligations exposed by cross-pollination, not claims
-- that those application repositories are imported here.
------------------------------------------------------------------------

record CrossProjectFeedbackBoundary : Set where
  constructor crossProjectFeedbackBoundary
  field
    animalAmbiguitySuggestsInactiveNotRefutedDistinction : Bool
    animalEvidenceSuggestsSupportOppositionIgnoranceConflictSeparation : Bool
    animalIncrementalInferenceSuggestsLocalDependencyReopening : Bool
    garmentSearchSuggestsBoundedBehaviouralExhaustionReceipts : Bool
    garmentFidelitySuggestsMaterialiseByDiscrepancyAndInformationValue : Bool
    garmentComplianceSuggestsPredicateCarryingReceipts : Bool
    lesCausalityFeedsInterventionalValidationBackToOtherDomains : Bool
    lesRobustnessFeedsContextAndScenarioRobustnessBackToOtherDomains : Bool
    lesAssimilationFeedsSelectiveInvalidationBackToOtherDomains : Bool
    oneGenericKernelMustNotEraseDomainSpecificEvidenceSemantics : Bool

open CrossProjectFeedbackBoundary public

canonicalCrossProjectFeedbackBoundary : CrossProjectFeedbackBoundary
canonicalCrossProjectFeedbackBoundary =
  crossProjectFeedbackBoundary
    true true true true true true true true true true

------------------------------------------------------------------------
-- 5. Shared uncertainty constitution.
------------------------------------------------------------------------

record LESUncertaintyConstitution : Set where
  constructor lesUncertaintyConstitution
  field
    epistemicNotFidelity : Bool
    fidelityNotScenario : Bool
    scenarioNotAleatoric : Bool
    scalarCombinationNeedsDeclaredConsumerRule : Bool
    provenanceRetainedPerAxis : Bool

open LESUncertaintyConstitution public

canonicalLESUncertaintyConstitution : LESUncertaintyConstitution
canonicalLESUncertaintyConstitution =
  lesUncertaintyConstitution true true true true true

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record LESRound3Boundary : Set where
  constructor lesRound3Boundary
  field
    genericKernelReuseDoesNotProveDomainModelValidity : Bool
    sharedFormalShapeDoesNotMakeEvidenceSemanticsIdentical : Bool
    genericIntertwinerDoesNotSupplyDomainMetricOrTolerance : Bool
    boundedCompletenessRemainsRelativeToDeclaredLanguage : Bool
    authorityPromotionNeedsDomainGovernancePolicy : Bool
    reopeningNeedsActualDependencyEvidence : Bool

open LESRound3Boundary public

canonicalLESRound3Boundary : LESRound3Boundary
canonicalLESRound3Boundary =
  lesRound3Boundary true true true true true true
