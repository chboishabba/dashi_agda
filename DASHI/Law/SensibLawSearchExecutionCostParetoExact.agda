module DASHI.Law.SensibLawSearchExecutionCostParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.CostedResidualInformationChoiceExact as Costed
import DASHI.Law.SensibLawGovernedLegalNetworkStrategyExact as Network
import DASHI.Law.SensibLawProofSearchParetoSaturationExact as SearchPareto

------------------------------------------------------------------------
-- GOVERNED EXECUTION COST SURFACE
--
-- The proof-search value surface already keeps proof reduction, discrimination,
-- authority fitness, novelty, coverage and acquisition cost separate. This
-- owner refines acquisition cost by making the execution strategy visible:
-- local fixture / persisted receipt / governed live search and fetch / bounded
-- citation follow. No network cost is hidden inside semantic relevance.
------------------------------------------------------------------------

data ExecutionStrategy : Set where
  localFixtureExecution
  persistedAuthorityReceiptExecution
  localWorldGraphExecution
  governedLiveSearchExecution
  governedExactFetchExecution
  governedCitationFollowExecution
  : ExecutionStrategy

record LegalExecutionCostVector : Set where
  constructor legalExecutionCostVector
  field
    strategy : ExecutionStrategy
    networkRequests : Nat
    minimumPacingSeconds : Nat
    citationDepth : Nat
    maximumNewDocuments : Nat
    cacheMisses : Nat
    localBytesReadCost : Nat
    parserPNFCost : Nat
    semanticAssessmentCost : Nat
    operatorReviewCost : Nat
    costReference : String

open LegalExecutionCostVector public

------------------------------------------------------------------------
-- Cost calibration remains explicit rather than inferred from strategy names.
------------------------------------------------------------------------

record LegalSearchMove : Set₁ where
  constructor legalSearchMove
  field
    queryReference : String
    providerOperationReference : String
    executionCost : LegalExecutionCostVector
    expectedProofReduction : Nat
    discriminativeValue : Nat
    authorityFitness : Nat
    novelty : Nat
    coverageGain : Nat
    admissibilityReceipt : Set
    calibrationReference : String
    moveReference : String

open LegalSearchMove public

record LegalSearchMoveDominates (left right : LegalSearchMove) : Set where
  constructor legalSearchMoveDominates
  field
    noMoreNetworkRequests :
      networkRequests (executionCost left) ≤ networkRequests (executionCost right)
    noMorePacingDelay :
      minimumPacingSeconds (executionCost left) ≤ minimumPacingSeconds (executionCost right)
    noMoreCitationDepth :
      citationDepth (executionCost left) ≤ citationDepth (executionCost right)
    noMoreDocumentBreadth :
      maximumNewDocuments (executionCost left) ≤ maximumNewDocuments (executionCost right)
    noMoreCacheMisses :
      cacheMisses (executionCost left) ≤ cacheMisses (executionCost right)
    noMoreLocalBytesCost :
      localBytesReadCost (executionCost left) ≤ localBytesReadCost (executionCost right)
    noMoreParserCost :
      parserPNFCost (executionCost left) ≤ parserPNFCost (executionCost right)
    noMoreAssessmentCost :
      semanticAssessmentCost (executionCost left) ≤ semanticAssessmentCost (executionCost right)
    noMoreReviewCost :
      operatorReviewCost (executionCost left) ≤ operatorReviewCost (executionCost right)
    noLessProofReduction : expectedProofReduction right ≤ expectedProofReduction left
    noLessDiscrimination : discriminativeValue right ≤ discriminativeValue left
    noLessAuthorityFitness : authorityFitness right ≤ authorityFitness left
    noLessNovelty : novelty right ≤ novelty left
    noLessCoverageGain : coverageGain right ≤ coverageGain left

open LegalSearchMoveDominates public

record LegalExecutionParetoChoice
    (Declared : LegalSearchMove → Set) : Set₂ where
  constructor legalExecutionParetoChoice
  field
    selected : LegalSearchMove
    selectedDeclared : Declared selected
    undominated :
      (alternative : LegalSearchMove) →
      Declared alternative →
      LegalSearchMoveDominates alternative selected →
      LegalSearchMoveDominates selected alternative
    consumerReference : String
    choiceReference : String

open LegalExecutionParetoChoice public

------------------------------------------------------------------------
-- Bridge to the existing generic residual-information cost/gain calculus.
------------------------------------------------------------------------

record GenericResidualCostProjection : Set where
  constructor genericResidualCostProjection
  field
    legalMoveReference : String
    declaredAggregateCost : Nat
    certifiedResidualGain : Nat
    moveKind : Costed.ResidualInformationMoveKind
    moveKindIsProofSearch : moveKind ≡ Costed.proofSearchResidualMove
    fullVectorRetainedReceipt : Set
    aggregateCalibrationReference : String
    projectionReference : String

open GenericResidualCostProjection public

record SearchParetoCompatibility : Set where
  constructor searchParetoCompatibility
  field
    legalExecutionAxesRefineExistingSearchPareto : Bool
    legalExecutionAxesRefineExistingSearchParetoIsTrue :
      legalExecutionAxesRefineExistingSearchPareto ≡ true
    genericCostGainOwnerReused : Bool
    genericCostGainOwnerReusedIsTrue : genericCostGainOwnerReused ≡ true
    fullVectorMayBeCollapsedWithoutDeclaredProjection : Bool
    fullVectorMayBeCollapsedWithoutDeclaredProjectionIsFalse :
      fullVectorMayBeCollapsedWithoutDeclaredProjection ≡ false

open SearchParetoCompatibility public

canonicalSearchParetoCompatibility : SearchParetoCompatibility
canonicalSearchParetoCompatibility =
  searchParetoCompatibility true refl true refl false refl

------------------------------------------------------------------------
-- Canonical execution classes for first SLR implementation.
------------------------------------------------------------------------

localFixtureCost : LegalExecutionCostVector
localFixtureCost = legalExecutionCostVector
  localFixtureExecution 0 0 0 0 0 1 1 1 0
  "offline fixture: zero network and pacing cost"

persistedReceiptCost : LegalExecutionCostVector
persistedReceiptCost = legalExecutionCostVector
  persistedAuthorityReceiptExecution 0 0 0 0 0 1 1 1 0
  "persisted authority receipt: zero live network cost"

liveSingleFetchCost : LegalExecutionCostVector
liveSingleFetchCost = legalExecutionCostVector
  governedExactFetchExecution 1 4 0 1 1 0 1 1 0
  "governed legal-host single fetch: one request with four-second pacing floor"

boundedLiveFollowCost : Nat → Nat → Nat → LegalExecutionCostVector
boundedLiveFollowCost requests depth breadth = legalExecutionCostVector
  governedCitationFollowExecution requests (4 ∗ requests) depth breadth breadth 0 1 1 0
  "governed citation follow: pacing and explicit depth/breadth exposed as cost coordinates"

------------------------------------------------------------------------
-- Governance welds.
------------------------------------------------------------------------

canonicalPacingPolicy : Network.LegalHostPacingPolicy
canonicalPacingPolicy = Network.canonicalLegalHostPacing

existingGenericProofSearchMove : Costed.ResidualInformationMoveKind
existingGenericProofSearchMove = Costed.proofSearchResidualMove

existingSearchParetoBoundary : SearchPareto.SearchParetoRefinementBoundary
existingSearchParetoBoundary = SearchPareto.canonicalSearchParetoRefinementBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OfflineExecutionAutomaticallyBest : Set where
data LiveExecutionAutomaticallyMoreInformative : Set where
data ZeroNetworkCostEqualsZeroSemanticCost : Set where
data PacingCostMayBeIgnoredInLiveSearch : Set where
data BreadthDepthMayBeHiddenInsideSingleCost : Set where
data CheapestMoveAutomaticallyPaysProofGap : Set where
data NetworkRequestCountEqualsAuthorityFitness : Set where

offlineDoesNotAutomaticallyWin : OfflineExecutionAutomaticallyBest → ⊥
offlineDoesNotAutomaticallyWin ()

liveDoesNotAutomaticallyGainMore : LiveExecutionAutomaticallyMoreInformative → ⊥
liveDoesNotAutomaticallyGainMore ()

zeroNetworkDoesNotMeanZeroSemanticCost : ZeroNetworkCostEqualsZeroSemanticCost → ⊥
zeroNetworkDoesNotMeanZeroSemanticCost ()

pacingCostRemainsVisible : PacingCostMayBeIgnoredInLiveSearch → ⊥
pacingCostRemainsVisible ()

breadthDepthRemainSeparate : BreadthDepthMayBeHiddenInsideSingleCost → ⊥
breadthDepthRemainSeparate ()

cheapestDoesNotAutoPayGap : CheapestMoveAutomaticallyPaysProofGap → ⊥
cheapestDoesNotAutoPayGap ()

requestCountDoesNotMeanAuthority : NetworkRequestCountEqualsAuthorityFitness → ⊥
requestCountDoesNotMeanAuthority ()

record SearchExecutionCostBoundary : Set where
  constructor searchExecutionCostBoundary
  field
    networkStrategyIsExplicitCostCoordinate : Bool
    networkStrategyIsExplicitCostCoordinateIsTrue :
      networkStrategyIsExplicitCostCoordinate ≡ true
    offlineFirstHasZeroNetworkRequests : Bool
    offlineFirstHasZeroNetworkRequestsIsTrue :
      offlineFirstHasZeroNetworkRequests ≡ true
    livePacingIsCosted : Bool
    livePacingIsCostedIsTrue : livePacingIsCosted ≡ true
    depthAndBreadthRemainIndependent : Bool
    depthAndBreadthRemainIndependentIsTrue : depthAndBreadthRemainIndependent ≡ true
    proofGainAndExecutionCostRemainIndependent : Bool
    proofGainAndExecutionCostRemainIndependentIsTrue :
      proofGainAndExecutionCostRemainIndependent ≡ true
    scalarCostRequiredForEveryConsumer : Bool
    scalarCostRequiredForEveryConsumerIsFalse : scalarCostRequiredForEveryConsumer ≡ false

canonicalSearchExecutionCostBoundary : SearchExecutionCostBoundary
canonicalSearchExecutionCostBoundary =
  searchExecutionCostBoundary true refl true refl true refl true refl true refl false refl
