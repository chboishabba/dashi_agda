module DASHI.Analysis.RiemannG2CutoffGrowthBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2NarrowWindowNoCancellationReturnExact as Narrow
import DASHI.Analysis.RiemannAristotleG2CurrentCutExact as Current

------------------------------------------------------------------------
-- CUTOFF-GROWTH BIDI SEAM
--
-- The narrow-window Lean return removes a false degree of freedom: while
-- J*Lambda <= pi/2, the same literal near scalar is positively pinned and no
-- direct or explicit-formula evaluation can manufacture cancellation.
--
-- Therefore a surviving route must first cross the quarter-period threshold on
-- the SAME taper/cutoff pair, and must then prove that all downstream near/far,
-- Gamma, and cluster consumers remain admissible under that changed cutoff.
------------------------------------------------------------------------

data CutoffStrategy : Set where
  fixedCutoff
  subcriticalGrowth
  quarterPeriodCrossingGrowth
  adaptiveLiteralCutoff
  : CutoffStrategy

data CutoffGrowthStage : Set where
  narrowNoCancellationKnown
  crossingLawRequired
  crossingLawOwned
  downstreamCompatibilityRequired
  oscillatoryConsumerReady
  : CutoffGrowthStage

currentCutoffGrowthStage : CutoffGrowthStage
currentCutoffGrowthStage = crossingLawRequired

record LiteralCutoffTaperPair : Set₁ where
  field
    Scalar : Set
    targetHeight cutoff supportRadius : Scalar
    QuarterPeriodCrossed : Set

    exactCutoffIsNearOffFinsetCutoff : Set
    exactSupportRadiusIsConstructedTaperRadius : Set
    exactTargetHeightIsLiteralConsumerTarget : Set

open LiteralCutoffTaperPair public

record QuarterPeriodCrossingReceipt
    (P : LiteralCutoffTaperPair) : Set₁ where
  field
    crossing : QuarterPeriodCrossed P
    growthReference : String
    sameLiteralPairUsed : Set

open QuarterPeriodCrossingReceipt public

record DownstreamCutoffCompatibility
    (P : LiteralCutoffTaperPair) : Set₁ where
  field
    nearCarrierRemainsFinite : Set
    farRemainderFormulaUsesSameCutoff : Set
    gammaErrorBudgetValidAtSameCutoff : Set
    clusterMarginComparisonUsesSameCutoff : Set
    explicitFormulaWindowUsesSameCutoff : Set
    compatibilityReference : String

open DownstreamCutoffCompatibility public

record OscillatoryCutoffAdmission
    (P : LiteralCutoffTaperPair) : Set₁ where
  constructor oscillatory-cutoff-admission
  field
    quarterPeriodCrossing : QuarterPeriodCrossingReceipt P
    downstreamCompatibility : DownstreamCutoffCompatibility P

open OscillatoryCutoffAdmission public

crossingAndCompatibilityAdmitOscillatoryRoute :
  (P : LiteralCutoffTaperPair) ->
  QuarterPeriodCrossingReceipt P ->
  DownstreamCutoffCompatibility P ->
  OscillatoryCutoffAdmission P
crossingAndCompatibilityAdmitOscillatoryRoute P crossing compatibility =
  oscillatory-cutoff-admission crossing compatibility

------------------------------------------------------------------------
-- Search pruning.
------------------------------------------------------------------------

SearchRelevant : CutoffStrategy -> Set
SearchRelevant fixedCutoff = ⊥
SearchRelevant subcriticalGrowth = ⊥
SearchRelevant quarterPeriodCrossingGrowth = ⊤
SearchRelevant adaptiveLiteralCutoff = ⊤

fixedCutoffPruned : SearchRelevant fixedCutoff -> ⊥
fixedCutoffPruned x = x

subcriticalGrowthPruned : SearchRelevant subcriticalGrowth -> ⊥
subcriticalGrowthPruned x = x

narrowWindowNecessityOwnedInLean :
  Narrow.survivingRouteRequiresQuarterPeriodCrossing
    Narrow.canonicalNarrowWindowNoCancellationReturn ≡ true
narrowWindowNecessityOwnedInLean =
  Narrow.survivingRouteRequiresQuarterPeriodCrossingIsTrue
    Narrow.canonicalNarrowWindowNoCancellationReturn

currentTargetCenteredLeafStillOpen :
  Current.targetCenteredLocalZeroExponentialSumBoundClosed
    Current.canonicalAristotleG2CurrentCut ≡ false
currentTargetCenteredLeafStillOpen =
  Current.targetCenteredLocalZeroExponentialSumBoundClosedIsFalse
    Current.canonicalAristotleG2CurrentCut

record CutoffGrowthBidiBoundary : Set where
  constructor cutoff-growth-bidi-boundary
  field
    narrowFixedCutoffCancellationRoutePruned : Bool
    narrowFixedCutoffCancellationRoutePrunedIsTrue :
      narrowFixedCutoffCancellationRoutePruned ≡ true

    directAndExplicitFormulaNarrowRoutesCollapseToSameNoGo : Bool
    directAndExplicitFormulaNarrowRoutesCollapseToSameNoGoIsTrue :
      directAndExplicitFormulaNarrowRoutesCollapseToSameNoGo ≡ true

    quarterPeriodCrossingIsNextNecessaryPayment : Bool
    quarterPeriodCrossingIsNextNecessaryPaymentIsTrue :
      quarterPeriodCrossingIsNextNecessaryPayment ≡ true

    crossingAloneIsEnoughForFinalConsumer : Bool
    crossingAloneIsEnoughForFinalConsumerIsFalse :
      crossingAloneIsEnoughForFinalConsumer ≡ false

    sameCutoffDownstreamCompatibilityRequired : Bool
    sameCutoffDownstreamCompatibilityRequiredIsTrue :
      sameCutoffDownstreamCompatibilityRequired ≡ true

    cutoffGrowthAutomaticallyProvesRH : Bool
    cutoffGrowthAutomaticallyProvesRHIsFalse :
      cutoffGrowthAutomaticallyProvesRH ≡ false

    highestAlphaReading : String

canonicalCutoffGrowthBidiBoundary : CutoffGrowthBidiBoundary
canonicalCutoffGrowthBidiBoundary =
  cutoff-growth-bidi-boundary
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    "The checked Lean pinning theorem forces the RH scalar search out of the fixed narrow-window regime. The next payment is a same-object quarter-period crossing pi/2 < J*Lambda, naturally suggesting J on the inverse taper-width scale (and hence order |t| for the high-ordinate taper when Lambda is order 1/|t|). But crossing is only admission to an oscillatory regime: the same enlarged cutoff must also preserve the literal near/far decomposition, Gamma budget, cluster margin, and explicit-formula window before any cancellation theorem can reach the final consumer."
