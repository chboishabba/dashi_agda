module DASHI.Biology.SoTLEpistemicQuotientPipeline where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (proj₁)

import DASHI.Core.MinimalSufficientResidual as Minimal
import DASHI.Core.ReopenableProjectionComposition as Reopenable

------------------------------------------------------------------------
-- Concrete research-pipeline instance.
--
-- This is a finite DASHI model of
--
--   lived state -> expressed response -> coded response
--              -> aggregate finding -> pedagogical recommendation.
--
-- It reuses #521's canonical ExactReopenableProjection composition law.
-- Only the first projection deliberately collapses a live fine distinction;
-- the later stages are renamed surfaces.  Exact composition proves that the
-- original hidden distinction remains reopenable through the complete chain.
-- The construction is a methodological countermodel/reference object, not an
-- empirical claim that any particular SoTL study uses these exact states.
------------------------------------------------------------------------

data ExpressedResponse : Set where
  expressedZero expressedOne : ExpressedResponse

data CodedResponse : Set where
  codedZero codedOne : CodedResponse

data AggregateFinding : Set where
  aggregateZero aggregateOne : AggregateFinding

data PedagogicalRecommendation : Set where
  recommendationZero recommendationOne : PedagogicalRecommendation

expressedBit : ExpressedResponse → Bool
expressedBit expressedZero = false
expressedBit expressedOne = true

expressFromBit : Bool → ExpressedResponse
expressFromBit false = expressedZero
expressFromBit true = expressedOne

codeFromExpression : ExpressedResponse → CodedResponse
codeFromExpression expressedZero = codedZero
codeFromExpression expressedOne = codedOne

expressionFromCode : CodedResponse → ExpressedResponse
expressionFromCode codedZero = expressedZero
expressionFromCode codedOne = expressedOne

aggregateFromCode : CodedResponse → AggregateFinding
aggregateFromCode codedZero = aggregateZero
aggregateFromCode codedOne = aggregateOne

codeFromAggregate : AggregateFinding → CodedResponse
codeFromAggregate aggregateZero = codedZero
codeFromAggregate aggregateOne = codedOne

recommendFromAggregate : AggregateFinding → PedagogicalRecommendation
recommendFromAggregate aggregateZero = recommendationZero
recommendFromAggregate aggregateOne = recommendationOne

aggregateFromRecommendation : PedagogicalRecommendation → AggregateFinding
aggregateFromRecommendation recommendationZero = aggregateZero
aggregateFromRecommendation recommendationOne = aggregateOne

expressionProjection : Minimal.FineBitState → ExpressedResponse
expressionProjection state =
  expressFromBit (Minimal.coarseFirstBit state)

expressionReopen :
  ExpressedResponse → Bool → Minimal.FineBitState
expressionReopen response hidden =
  Minimal.reopenFromHiddenBit (expressedBit response) hidden

expressionReopensExactly :
  (state : Minimal.FineBitState) →
  expressionReopen
    (expressionProjection state)
    (Minimal.hiddenSecondBit state)
  ≡ state
expressionReopensExactly Minimal.fine00 = refl
expressionReopensExactly Minimal.fine01 = refl
expressionReopensExactly Minimal.fine10 = refl
expressionReopensExactly Minimal.fine11 = refl

expressionMap :
  Reopenable.ExactReopenableProjection Minimal.FineBitState ExpressedResponse
expressionMap =
  Reopenable.exactReopenableProjection
    Bool
    expressionProjection
    Minimal.hiddenSecondBit
    expressionReopen
    expressionReopensExactly

codingMap :
  Reopenable.ExactReopenableProjection ExpressedResponse CodedResponse
codingMap =
  Reopenable.exactReopenableProjection
    ⊤
    codeFromExpression
    (λ response → tt)
    (λ code receipt → expressionFromCode code)
    codingExact
  where
    codingExact :
      (response : ExpressedResponse) →
      expressionFromCode (codeFromExpression response) ≡ response
    codingExact expressedZero = refl
    codingExact expressedOne = refl

aggregationMap :
  Reopenable.ExactReopenableProjection CodedResponse AggregateFinding
aggregationMap =
  Reopenable.exactReopenableProjection
    ⊤
    aggregateFromCode
    (λ code → tt)
    (λ aggregate receipt → codeFromAggregate aggregate)
    aggregationExact
  where
    aggregationExact :
      (code : CodedResponse) →
      codeFromAggregate (aggregateFromCode code) ≡ code
    aggregationExact codedZero = refl
    aggregationExact codedOne = refl

recommendationMap :
  Reopenable.ExactReopenableProjection
    AggregateFinding PedagogicalRecommendation
recommendationMap =
  Reopenable.exactReopenableProjection
    ⊤
    recommendFromAggregate
    (λ aggregate → tt)
    (λ recommendation receipt → aggregateFromRecommendation recommendation)
    recommendationExact
  where
    recommendationExact :
      (aggregate : AggregateFinding) →
      aggregateFromRecommendation (recommendFromAggregate aggregate) ≡ aggregate
    recommendationExact aggregateZero = refl
    recommendationExact aggregateOne = refl

expressionCodingMap :
  Reopenable.ExactReopenableProjection Minimal.FineBitState CodedResponse
expressionCodingMap =
  Reopenable.composeExactReopenableProjection expressionMap codingMap

expressionCodingAggregationMap :
  Reopenable.ExactReopenableProjection Minimal.FineBitState AggregateFinding
expressionCodingAggregationMap =
  Reopenable.composeExactReopenableProjection
    expressionCodingMap aggregationMap

fullResearchPipeline :
  Reopenable.ExactReopenableProjection
    Minimal.FineBitState PedagogicalRecommendation
fullResearchPipeline =
  Reopenable.composeExactReopenableProjection
    expressionCodingAggregationMap
    recommendationMap

fullResearchPipelineReopensExactly :
  (state : Minimal.FineBitState) →
  Reopenable.reopen fullResearchPipeline
    (Reopenable.project fullResearchPipeline state)
    (Reopenable.receipt fullResearchPipeline state)
  ≡ state
fullResearchPipelineReopensExactly =
  Reopenable.reopenExact fullResearchPipeline

------------------------------------------------------------------------
-- The earliest hidden distinction survives every later stage of the chain.
-- The canonical composition receipt is nested products, so following the left
-- receipt at each stage returns the original expression-stage hidden bit.
------------------------------------------------------------------------

expressionResidualSurvivesFullPipeline :
  (state : Minimal.FineBitState) →
  proj₁
    (proj₁
      (proj₁
        (Reopenable.receipt fullResearchPipeline state)))
  ≡ Minimal.hiddenSecondBit state
expressionResidualSurvivesFullPipeline state = refl
