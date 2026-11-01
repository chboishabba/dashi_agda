module DASHI.Law.SensibLawResearchCompoundingLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawMultiResidualProofFrontierExact as Frontier
import DASHI.Law.SensibLawParsedAuthorityReasoningGraphExact as Reasoning
import DASHI.Law.SensibLawImmutableLegalResearchWorldExact as World
import DASHI.Law.SensibLawProofSearchIterationReceiptABIExact as Receipt

------------------------------------------------------------------------
-- RESEARCH COMPOUNDING LOOP
--
-- Each useful parsed result may enrich reusable legal/world memory, alter the
-- consumer-relative proof frontier, and thereby change the next ranked search.
------------------------------------------------------------------------

record ParsedResultEnrichment : Set₁ where
  constructor parsedResultEnrichment
  field
    reasoningDelta : Reasoning.ParsedAuthorityReasoningDelta
    changedCoordinateReferences : List String
    newCitationNeighbourhoodReferences : List String
    newLexicalVocabularyReferences : List String
    newConditionPatternReferences : List String
    enrichmentReference : String

open ParsedResultEnrichment public

record ResearchCompoundingIteration : Set₂ where
  constructor researchCompoundingIteration
  field
    priorFrontier : Frontier.ProofFrontier
    selectedMoveReference : String
    enrichment : ParsedResultEnrichment
    priorWorld : World.LegalResearchWorldSnapshot
    posteriorWorld : World.LegalResearchWorldSnapshot
    appendOnlyExtension : World.AppendOnlyResearchExtension priorWorld posteriorWorld
    posteriorFrontier : Frontier.ProofFrontier
    nextFrontierCandidates : List Frontier.FrontierMoveCandidate
    runtimeReceipt : Receipt.ProofSearchIterationReceipt
    candidateOnlyReceipt : Set
    iterationReference : String

open ResearchCompoundingIteration public

record CompoundingSearchReadiness : Set where
  constructor compoundingSearchReadiness
  field
    parsedReasoningFeedsWorld : Bool
    parsedReasoningFeedsWorldIsTrue : parsedReasoningFeedsWorld ≡ true
    worldMemoryFeedsNextSearch : Bool
    worldMemoryFeedsNextSearchIsTrue : worldMemoryFeedsNextSearch ≡ true
    localReuseMayReduceFutureNetworkCost : Bool
    localReuseMayReduceFutureNetworkCostIsTrue : localReuseMayReduceFutureNetworkCost ≡ true
    conclusionsMayStillReverse : Bool
    conclusionsMayStillReverseIsTrue : conclusionsMayStillReverse ≡ true

canonicalCompoundingSearchReadiness : CompoundingSearchReadiness
canonicalCompoundingSearchReadiness =
  compoundingSearchReadiness true refl true refl true refl true refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MoreResearchAutomaticallyImprovesProof : Set where
data MoreCitationsAutomaticallyIncreaseAuthority : Set where
data ParsedConditionPatternAutomaticallyLegalCondition : Set where
data ReusedVocabularyAutomaticallySemanticTruth : Set where
data WorldMemoryGrowthMeansConclusionMonotone : Set where

moreResearchDoesNotAutomaticallyImproveProof :
  MoreResearchAutomaticallyImprovesProof → ⊥
moreResearchDoesNotAutomaticallyImproveProof ()

moreCitationsDoNotAutomaticallyIncreaseAuthority :
  MoreCitationsAutomaticallyIncreaseAuthority → ⊥
moreCitationsDoNotAutomaticallyIncreaseAuthority ()

parsedPatternDoesNotBecomeLegalCondition :
  ParsedConditionPatternAutomaticallyLegalCondition → ⊥
parsedPatternDoesNotBecomeLegalCondition ()

reusedVocabularyDoesNotBecomeTruth :
  ReusedVocabularyAutomaticallySemanticTruth → ⊥
reusedVocabularyDoesNotBecomeTruth ()

worldGrowthDoesNotForceConclusionMonotonicity :
  WorldMemoryGrowthMeansConclusionMonotone → ⊥
worldGrowthDoesNotForceConclusionMonotonicity ()

record ResearchCompoundingBoundary : Set where
  constructor researchCompoundingBoundary
  field
    parsedResultsMayEnrichFutureSearch : Bool
    parsedResultsMayEnrichFutureSearchIsTrue : parsedResultsMayEnrichFutureSearch ≡ true
    reasoningConditionsAndTreatmentMayBeReused : Bool
    reasoningConditionsAndTreatmentMayBeReusedIsTrue :
      reasoningConditionsAndTreatmentMayBeReused ≡ true
    retainedHistoryDoesNotForceRetainedConclusion : Bool
    retainedHistoryDoesNotForceRetainedConclusionIsTrue :
      retainedHistoryDoesNotForceRetainedConclusion ≡ true
    compoundingEqualsAutomaticTruth : Bool
    compoundingEqualsAutomaticTruthIsFalse : compoundingEqualsAutomaticTruth ≡ false

canonicalResearchCompoundingBoundary : ResearchCompoundingBoundary
canonicalResearchCompoundingBoundary =
  researchCompoundingBoundary true refl true refl true refl false refl
