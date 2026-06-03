module DASHI.Physics.Closure.ClaySolvedLedgerLemmas where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat; _-_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Clay solved ledger lemmas.
--
-- This module only inhabits the currently solved bookkeeping facts:
-- threshold constants, gap arithmetic, route status, T7A demotion,
-- live-target names, and fail-closed promotion flags.  It deliberately does
-- not inhabit the Clay-grade analytic blockers.

------------------------------------------------------------------------
-- 1. Threshold ledger, integer-scaled by 100.

connectedAnimalThreshold : Nat
connectedAnimalThreshold =
  959

btTreeThreshold : Nat
btTreeThreshold =
  1013

strictAbsorptionThreshold : Nat
strictAbsorptionThreshold =
  1364

t7aDirectThreshold : Nat
t7aDirectThreshold =
  1656

connectedAnimalThresholdIs959 :
  connectedAnimalThreshold ≡ 959
connectedAnimalThresholdIs959 =
  refl

btTreeThresholdIs1013 :
  btTreeThreshold ≡ 1013
btTreeThresholdIs1013 =
  refl

strictAbsorptionThresholdIs1364 :
  strictAbsorptionThreshold ≡ 1364
strictAbsorptionThresholdIs1364 =
  refl

t7aDirectThresholdIs1656 :
  t7aDirectThreshold ≡ 1656
t7aDirectThresholdIs1656 =
  refl

------------------------------------------------------------------------
-- 2. Gap arithmetic from physical beta ~= 6.00.

physicalBetaBaseline : Nat
physicalBetaBaseline =
  600

connectedAnimalGap : Nat
connectedAnimalGap =
  connectedAnimalThreshold - physicalBetaBaseline

btTreeGap : Nat
btTreeGap =
  btTreeThreshold - physicalBetaBaseline

strictAbsorptionGap : Nat
strictAbsorptionGap =
  strictAbsorptionThreshold - physicalBetaBaseline

t7aDirectGap : Nat
t7aDirectGap =
  t7aDirectThreshold - physicalBetaBaseline

connectedAnimalGapIs359 :
  connectedAnimalGap ≡ 359
connectedAnimalGapIs359 =
  refl

btTreeGapIs413 :
  btTreeGap ≡ 413
btTreeGapIs413 =
  refl

strictAbsorptionGapIs764 :
  strictAbsorptionGap ≡ 764
strictAbsorptionGapIs764 =
  refl

t7aDirectGapIs1056 :
  t7aDirectGap ≡ 1056
t7aDirectGapIs1056 =
  refl

------------------------------------------------------------------------
-- 2a. Higher-precision guardrails for thresholds that should not be stated
--     as bare hundredths-level theorem targets.

connectedAnimalThresholdTenThousandths : Nat
connectedAnimalThresholdTenThousandths =
  95936

connectedAnimalSafeThresholdTenThousandths : Nat
connectedAnimalSafeThresholdTenThousandths =
  95937

connectedAnimalThresholdMillis : Nat
connectedAnimalThresholdMillis =
  9594

strictAbsorptionExactThresholdMillionths : Nat
strictAbsorptionExactThresholdMillionths =
  13631603

strictAbsorptionSafeSampleTenths : Nat
strictAbsorptionSafeSampleTenths =
  137

connectedAnimalThresholdMillisIs9594 :
  connectedAnimalThresholdMillis ≡ 9594
connectedAnimalThresholdMillisIs9594 =
  refl

connectedAnimalThresholdTenThousandthsIs95936 :
  connectedAnimalThresholdTenThousandths ≡ 95936
connectedAnimalThresholdTenThousandthsIs95936 =
  refl

connectedAnimalSafeThresholdTenThousandthsIs95937 :
  connectedAnimalSafeThresholdTenThousandths ≡ 95937
connectedAnimalSafeThresholdTenThousandthsIs95937 =
  refl

strictAbsorptionExactThresholdMillionthsIs13631603 :
  strictAbsorptionExactThresholdMillionths ≡ 13631603
strictAbsorptionExactThresholdMillionthsIs13631603 =
  refl

strictAbsorptionSafeSampleTenthsIs137 :
  strictAbsorptionSafeSampleTenths ≡ 137
strictAbsorptionSafeSampleTenthsIs137 =
  refl

------------------------------------------------------------------------
-- 3. Strict Balaban target is not the weak connected-animal target.

strictMinusConnected : Nat
strictMinusConnected =
  strictAbsorptionThreshold - connectedAnimalThreshold

strictMinusConnectedIs405 :
  strictMinusConnected ≡ 405
strictMinusConnectedIs405 =
  refl

t7aMinusStrict : Nat
t7aMinusStrict =
  t7aDirectThreshold - strictAbsorptionThreshold

t7aMinusStrictIs292 :
  t7aMinusStrict ≡ 292
t7aMinusStrictIs292 =
  refl

------------------------------------------------------------------------
-- 4. Route classification.

data YMRoute : Set where
  connectedAnimalKPRoute :
    YMRoute

  btTreeKPRoute :
    YMRoute

  strictBalabanSeedRoute :
    YMRoute

  t7aDirectRoute :
    YMRoute

  t7aSuppressionEnvelope :
    YMRoute

data RouteStatus : Set where
  standard :
    RouteStatus

  tighter :
    RouteStatus

  strictestSeed :
    RouteStatus

  demoted :
    RouteStatus

  auxiliaryOnly :
    RouteStatus

routeStatus : YMRoute → RouteStatus
routeStatus connectedAnimalKPRoute =
  standard
routeStatus btTreeKPRoute =
  tighter
routeStatus strictBalabanSeedRoute =
  strictestSeed
routeStatus t7aDirectRoute =
  demoted
routeStatus t7aSuppressionEnvelope =
  auxiliaryOnly

connectedAnimalRouteIsStandard :
  routeStatus connectedAnimalKPRoute ≡ standard
connectedAnimalRouteIsStandard =
  refl

btTreeRouteIsTighter :
  routeStatus btTreeKPRoute ≡ tighter
btTreeRouteIsTighter =
  refl

strictBalabanRouteIsStrictestSeed :
  routeStatus strictBalabanSeedRoute ≡ strictestSeed
strictBalabanRouteIsStrictestSeed =
  refl

t7aDirectRouteIsDemoted :
  routeStatus t7aDirectRoute ≡ demoted
t7aDirectRouteIsDemoted =
  refl

t7aSuppressionEnvelopeIsAuxiliaryOnly :
  routeStatus t7aSuppressionEnvelope ≡ auxiliaryOnly
t7aSuppressionEnvelopeIsAuxiliaryOnly =
  refl

------------------------------------------------------------------------
-- 5. T7A governance.

t7aDirectCountingAllowedAsPrimary : Bool
t7aDirectCountingAllowedAsPrimary =
  false

t7aPerPolymerSuppressionAllowed : Bool
t7aPerPolymerSuppressionAllowed =
  true

t7aDirectCountingDemoted :
  t7aDirectCountingAllowedAsPrimary ≡ false
t7aDirectCountingDemoted =
  refl

t7aPerPolymerSuppressionOnly :
  t7aPerPolymerSuppressionAllowed ≡ true
t7aPerPolymerSuppressionOnly =
  refl

------------------------------------------------------------------------
-- 6. Clay/Gate promotion flags remain false.

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

gate3Closed : Bool
gate3Closed =
  false

w4Closed : Bool
w4Closed =
  false

gravityPromoted : Bool
gravityPromoted =
  false

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse =
  refl

clayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted ≡ false
clayNavierStokesPromotedIsFalse =
  refl

gate3ClosedIsFalse :
  gate3Closed ≡ false
gate3ClosedIsFalse =
  refl

w4ClosedIsFalse :
  w4Closed ≡ false
w4ClosedIsFalse =
  refl

gravityPromotedIsFalse :
  gravityPromoted ≡ false
gravityPromotedIsFalse =
  refl

------------------------------------------------------------------------
-- 7. First live targets are names, not solved Clay lemmas.

ymFirstLiveTarget : String
ymFirstLiveTarget =
  "StrictKPSeedAtActiveMargin"

ymSecondLiveTarget : String
ymSecondLiveTarget =
  "ConditionalBalabanScaleTransfer"

nsFirstLiveTarget : String
nsFirstLiveTarget =
  "FixedKTailFluxIdentityWithDefect"

nsSecondLiveTarget : String
nsSecondLiveTarget =
  "ProjectionDefectAbsorbedByTailDissipation"

nsHardTarget : String
nsHardTarget =
  "CumulativeTailDissipationDominance"

gate3FirstLiveTarget : String
gate3FirstLiveTarget =
  "PhysicalSSPSpreadBound"

ymFirstLiveTargetIsStrictKPSeed :
  ymFirstLiveTarget ≡ "StrictKPSeedAtActiveMargin"
ymFirstLiveTargetIsStrictKPSeed =
  refl

ymSecondLiveTargetIsConditionalBalaban :
  ymSecondLiveTarget ≡ "ConditionalBalabanScaleTransfer"
ymSecondLiveTargetIsConditionalBalaban =
  refl

nsFirstLiveTargetIsFixedKTailWithDefect :
  nsFirstLiveTarget ≡ "FixedKTailFluxIdentityWithDefect"
nsFirstLiveTargetIsFixedKTailWithDefect =
  refl

nsSecondLiveTargetIsProjectionDefectAbsorption :
  nsSecondLiveTarget ≡ "ProjectionDefectAbsorbedByTailDissipation"
nsSecondLiveTargetIsProjectionDefectAbsorption =
  refl

nsHardTargetIsCumulativeTailDominance :
  nsHardTarget ≡ "CumulativeTailDissipationDominance"
nsHardTargetIsCumulativeTailDominance =
  refl

gate3FirstLiveTargetIsPhysicalSSPSpread :
  gate3FirstLiveTarget ≡ "PhysicalSSPSpreadBound"
gate3FirstLiveTargetIsPhysicalSSPSpread =
  refl

------------------------------------------------------------------------
-- 8. Receipt boundary.

receiptBoundary : List String
receiptBoundary =
  "This module proves only ledger, threshold, routing, demotion, and fail-closed promotion facts." ∷
  "The rounded connected-animal 9.59 entry is not a safe strict numeric theorem statement; use beta > 9.593637, the millesimal ceiling 9.594, or the exact q/(1-p*q)^2 inequality." ∷
  "The BT-tree hundredths entry is corrected to 10.13, with gap 4.13 from beta=6." ∷
  "The strict Balaban seed should be stated as beta*c_min-a>log(2p), or numerically with a robust sample such as beta_eff>=13.7." ∷
  "It does not prove NonperturbativeBalabanScaleTransfer." ∷
  "It does not prove HyperbolicShimuraToEuclideanUniversality." ∷
  "It does not prove OSWightmanReconstruction." ∷
  "It does not prove MassGapSurvivesContinuumLimit." ∷
  "It does not prove Nontrivial4DSU3YangMills." ∷
  "It does not prove CumulativeTailDissipationDominance." ∷
  "It does not prove NSFlowProjectionTransport." ∷
  "It does not prove ProjectionDefectAbsorbedByTailDissipation." ∷
  "It does not prove PhysicalSSPSpreadBound." ∷
  "It does not prove UniformFrameLowerBound." ∷
  "All Clay, Gate3, W4, and gravity promotion flags remain false." ∷
  []
