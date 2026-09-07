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
-- Therefore a surviving route must cross the quarter-period threshold on the
-- SAME taper/cutoff pair. After crossing, J remains a coordinate only of the
-- finite-near/far Off producer. Gamma and cluster are not cutoff-indexed in the
-- final pole-quotient API; their downstream compatibility is same-TAPER, not
-- same-J compatibility.
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

    -- Deterministic complement channels are taper-only. These receipts assert
    -- same literal taper, not fictitious Gamma(J)/cluster(J) laws.
    gammaBudgetUsesSameLiteralTaper : Set
    clusterMarginUsesSameLiteralTaper : Set

    -- Explicit-formula route is optional/fallback; if used, its finite window
    -- must share the actual Off cutoff.
    explicitFormulaWindowUsesSameOffCutoff : Set
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
    "The checked Lean pinning theorem forces the scalar search out of the fixed narrow-window regime. A surviving Off route needs pi/2 < J*Lambda on the literal taper/cutoff pair. After crossing, preserve the same J only through the finite-near/far Off decomposition. Gamma and cluster remain taper-only and require same-literal-taper compatibility, not Gamma(J) or cluster(J). Crossing is admission to oscillatory analysis, not the cancellation theorem itself. RH is not derived."

------------------------------------------------------------------------
-- Coordinate correction pins.
------------------------------------------------------------------------

gammaIsCutoffIndexedDownstream : Bool
gammaIsCutoffIndexedDownstream = false

gammaIsCutoffIndexedDownstreamIsFalse :
  gammaIsCutoffIndexedDownstream ≡ false
gammaIsCutoffIndexedDownstreamIsFalse = refl

clusterIsCutoffIndexedDownstream : Bool
clusterIsCutoffIndexedDownstream = false

clusterIsCutoffIndexedDownstreamIsFalse :
  clusterIsCutoffIndexedDownstream ≡ false
clusterIsCutoffIndexedDownstreamIsFalse = refl
