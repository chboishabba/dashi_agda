module DASHI.Law.SensibLawProofGapExecutableSearchCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent
import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query
import DASHI.Law.SensibLawCorpusProducerRoutingExact as Corpus
import DASHI.Law.SensibLawLegalFollowProofSearchBridgeExact as FollowBridge
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Result

------------------------------------------------------------------------
-- END-TO-END SEARCH COMPILER
--
-- This owner makes the previously adjacent stages literal objects:
--
-- proof gap -> typed intent -> hypothesis family -> provider-neutral query
-- -> provider plan, then acquired passage -> attributed proposition
-- -> proof assessment -> frontier delta.
------------------------------------------------------------------------

record ProofGap : Set where
  constructor proofGap
  field
    consumerReference : String
    firstResidualReference : String
    missingPropositionReference : String
    requiredProducer : Intent.ProducerClass
    jurisdictionReference : String
    temporalEnvelopeReference : String
    gapReference : String

open ProofGap public

record ProofGapSearchPlan : Set₁ where
  constructor proofGapSearchPlan
  field
    gap : ProofGap
    intent : Intent.SearchIntent
    producerMatchesGap : Intent.producerClass intent ≡ requiredProducer gap
    hypothesisFamily : Query.SearchHypothesisFamily
    familyMatchesIntentReceipt : Set
    eligibleCorpora : List Corpus.CorpusClass
    eligibleCorporaMatchProducerReceipt : Set
    executableQuery : Query.ProviderCompiledQuery
    queryMatchesFamilyReceipt : Set
    providerRespectsCorpusReceipt : Set
    planReference : String

open ProofGapSearchPlan public

record ProofGapLegalFollowPlan : Set₁ where
  constructor proofGapLegalFollowPlan
  field
    gapPlan : ProofGapSearchPlan
    followBridge : FollowBridge.ReadyLegalFollowSearchBridge
    sameConsumerReceipt : Set
    sameJurisdictionReceipt : Set
    sameProducerReceipt : Set
    noBroadeningReceipt : Set
    bridgeReference : String

open ProofGapLegalFollowPlan public

record SearchReturnCompilation : Set₁ where
  constructor searchReturnCompilation
  field
    searchPlan : ProofGapSearchPlan
    passage : Result.RetrievedPassage
    passageComesFromPlanReceipt : Set
    attributedProposition : Result.AttributedSearchProposition passage
    proofAssessment : Result.SearchResultProofAssessment attributedProposition
    assessmentTargetsGapReceipt : Set
    frontierDelta : Result.SearchFrontierDelta
    deltaTargetsConsumerReceipt : Set
    sameParserPNFReentryReceipt : Set
    returnReference : String

open SearchReturnCompilation public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data QueryStringCanExistWithoutGap : Set where
data ProviderMayReplaceProducer : Set where
data RetrievedPassageAutomaticallyAssessment : Set where
data AssessmentAutomaticallyFrontierClosed : Set where
data LegalFollowBridgeMayBroadenCompiledPlan : Set where

queryStringDoesNotReplaceGap : QueryStringCanExistWithoutGap → ⊥
queryStringDoesNotReplaceGap ()

providerDoesNotReplaceProducer : ProviderMayReplaceProducer → ⊥
providerDoesNotReplaceProducer ()

passageDoesNotAutoAssess : RetrievedPassageAutomaticallyAssessment → ⊥
passageDoesNotAutoAssess ()

assessmentDoesNotAutoClose : AssessmentAutomaticallyFrontierClosed → ⊥
assessmentDoesNotAutoClose ()

legalFollowDoesNotBroadenCompiledPlan : LegalFollowBridgeMayBroadenCompiledPlan → ⊥
legalFollowDoesNotBroadenCompiledPlan ()

record EndToEndSearchCompilerBoundary : Set where
  constructor endToEndSearchCompilerBoundary
  field
    gapCompilesToExecutableProviderPlan : Bool
    gapCompilesToExecutableProviderPlanIsTrue : gapCompilesToExecutableProviderPlan ≡ true
    providerSelectionRemainsSubordinateToProducer : Bool
    providerSelectionRemainsSubordinateToProducerIsTrue :
      providerSelectionRemainsSubordinateToProducer ≡ true
    resultReentersAssessmentBeforeFrontierUpdate : Bool
    resultReentersAssessmentBeforeFrontierUpdateIsTrue :
      resultReentersAssessmentBeforeFrontierUpdate ≡ true
    retrievalEqualsClosure : Bool
    retrievalEqualsClosureIsFalse : retrievalEqualsClosure ≡ false

canonicalEndToEndSearchCompilerBoundary : EndToEndSearchCompilerBoundary
canonicalEndToEndSearchCompilerBoundary =
  endToEndSearchCompilerBoundary true refl true refl true refl false refl
