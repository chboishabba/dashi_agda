{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravitySameStateFourChannelDiscriminatorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve; solve-∀)

import DASHI.Physics.Foundations.GRQFTNambuGotoRepulsiveBubbleMaxCutExact as Bubble
import DASHI.Physics.Foundations.GRQFTNambuGotoRepulsiveShellFamilyExact as Shell
import DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact as Junction
import DASHI.Physics.Foundations.GRQFTSingleVacuumIsraelKottlerExact as SingleVacuum

------------------------------------------------------------------------
-- SAME-STATE FOUR-CHANNEL DISCRIMINATOR
--
-- This is repository-owned experimental/compiler structure.  It does not
-- attribute the four-channel protocol to any external source and it does not
-- promote an observed anomaly into a metric claim.  The central requirement is
-- stronger: one selected metric state must feed weight/support, free-fall,
-- clock and optical consumers on the same candidate/apparatus.
------------------------------------------------------------------------

record SameStateFourChannelPrediction : Set₁ where
  constructor same-state-four-channel-prediction
  field
    MetricState : Set
    metricState : MetricState

    WeightObservation FreeFallObservation ClockObservation OpticalObservation : Set

    weightFromSameMetric : MetricState → WeightObservation
    freeFallFromSameMetric : MetricState → FreeFallObservation
    clockFromSameMetric : MetricState → ClockObservation
    opticalFromSameMetric : MetricState → OpticalObservation

    sameMetricFeedsAllFourChannels : Bool
    sameMetricFeedsAllFourChannelsIsTrue :
      sameMetricFeedsAllFourChannels ≡ true

open SameStateFourChannelPrediction public

------------------------------------------------------------------------
-- SOURCE -> STRESS -> METRIC PROVENANCE CHAIN
--
-- The four-channel prediction is not allowed to float free of the source-side
-- object.  One selected source is compiled into one selected stress and then
-- one selected metric, and the metric stored in the four-channel prediction
-- must be literally that stress-derived metric.
------------------------------------------------------------------------

record SameStateStressMetricFourChannelChain : Set₁ where
  constructor same-state-stress-metric-four-channel-chain
  field
    SourceState StressState MetricState : Set
    selectedSource : SourceState
    sourceToStress : SourceState → StressState
    stressToMetric : StressState → MetricState

    selectedPrediction : SameStateFourChannelPrediction
    predictionMetricTypeIsSame :
      SameStateFourChannelPrediction.MetricState selectedPrediction ≡ MetricState
    predictionMetricIsSameStressDerivedMetric :
      SameStateFourChannelPrediction.metricState selectedPrediction
      ≡ stressToMetric (sourceToStress selectedSource)

open SameStateStressMetricFourChannelChain public

sameSourceStressMetricChainRequired : Bool
sameSourceStressMetricChainRequired = true

-- Cross-pollinated lesson from the repo's consumer-relative stress machinery:
-- agreement after one projection (trace, active stress, one component, etc.)
-- cannot identify the complete stress object.
sharedProjectionDoesNotIdentifyFullStress : Bool
sharedProjectionDoesNotIdentifyFullStress = true

weightOnlyCannotPromoteMetricClaim : Bool
weightOnlyCannotPromoteMetricClaim = true

anomalyAloneIsNotGeometry : Bool
anomalyAloneIsNotGeometry = true

------------------------------------------------------------------------
-- OLDER EXACT NAMBU/KOTTLER FIXTURE, RETAINED AS A REGRESSION/DONOR EXAMPLE.
--
-- #1120's preferred source route is now the single-vacuum normalized fixture
-- below.  Keeping these exact values prevents accidental loss of the earlier
-- A->E geometry while avoiding promotion of the older two-vacuum source path.
------------------------------------------------------------------------

fixtureOutwardFreeFall : ℚ
fixtureOutwardFreeFall = Bubble.fixtureOutwardAcceleration

fixtureOutwardFreeFallIsFiveTwentyFourths :
  fixtureOutwardFreeFall ≡ Int.+ 5 / 24
fixtureOutwardFreeFallIsFiveTwentyFourths = refl

fixtureSupportWeightChange : ℚ → ℚ
fixtureSupportWeightChange passiveMass =
  - (passiveMass * fixtureOutwardFreeFall)

fixtureExteriorLapseRoot : ℚ
fixtureExteriorLapseRoot = Shell.y

fixtureInteriorLapseRoot : ℚ
fixtureInteriorLapseRoot = Shell.x

fixtureExteriorLapseRootIsHalf :
  fixtureExteriorLapseRoot ≡ Int.+ 1 / 2
fixtureExteriorLapseRootIsHalf = refl

fixtureInteriorLapseRootIsThreeQuarters :
  fixtureInteriorLapseRoot ≡ Int.+ 3 / 4
fixtureInteriorLapseRootIsThreeQuarters = refl

olderNambuFixtureIsRegressionNotPreferredSourceRoute : Bool
olderNambuFixtureIsRegressionNotPreferredSourceRoute = true

------------------------------------------------------------------------
-- PREFERRED SINGLE-VACUUM NORMALIZED FIXTURE.
--
-- This consumes #1120's current static source route: one vacuum amplitude on
-- both sides, positive metric mass, positive shell energy, DEC compatibility,
-- SEC violation, and outward Kottler acceleration.
------------------------------------------------------------------------

preferredSingleVacuumFixtureRadius : ℚ
preferredSingleVacuumFixtureRadius = SingleVacuum.fixtureRadius

preferredSingleVacuumFixtureLambda : ℚ
preferredSingleVacuumFixtureLambda = SingleVacuum.fixtureLambda

preferredSingleVacuumInteriorLapseRoot : ℚ
preferredSingleVacuumInteriorLapseRoot = SingleVacuum.fixtureX

preferredSingleVacuumExteriorLapseRoot : ℚ
preferredSingleVacuumExteriorLapseRoot = SingleVacuum.fixtureY

preferredSingleVacuumOutwardScaled : ℚ
preferredSingleVacuumOutwardScaled =
  SingleVacuum.sameVacuumOutwardScaled
    SingleVacuum.fixtureRadius
    SingleVacuum.fixtureX
    SingleVacuum.fixtureY

preferredSingleVacuumOutwardScaledIsSeventySevenSeventyFifths :
  preferredSingleVacuumOutwardScaled ≡ Int.+ 77 / 75
preferredSingleVacuumOutwardScaledIsSeventySevenSeventyFifths =
  SingleVacuum.fixtureOutwardScaledIsSeventySevenSeventyFifths

preferredSingleVacuumOutwardFreeFall : ℚ
preferredSingleVacuumOutwardFreeFall =
  preferredSingleVacuumOutwardScaled
    / (preferredSingleVacuumFixtureRadius * preferredSingleVacuumFixtureRadius)

preferredSingleVacuumOutwardFreeFallIsSeventySevenThreeHundredths :
  preferredSingleVacuumOutwardFreeFall ≡ Int.+ 77 / 300
preferredSingleVacuumOutwardFreeFallIsSeventySevenThreeHundredths = solve []

preferredSingleVacuumSupportWeightChange : ℚ → ℚ
preferredSingleVacuumSupportWeightChange passiveMass =
  - (passiveMass * preferredSingleVacuumOutwardFreeFall)

------------------------------------------------------------------------
-- KOTTLER SCALAR METRIC RESPONSE.
------------------------------------------------------------------------

kottlerLapseDelta : ℚ → ℚ → ℚ → ℚ → ℚ
kottlerLapseDelta radius mass lambda deltaLambda =
  Junction.fExterior radius mass (lambda + deltaLambda)
  - Junction.fExterior radius mass lambda

kottlerLapseDeltaLinear :
  ∀ radius mass lambda deltaLambda →
  kottlerLapseDelta radius mass lambda deltaLambda
  ≡ - (deltaLambda * radius * radius / (Int.+ 3 / 1))
kottlerLapseDeltaLinear = solve-∀

-- Signature convention of the selected static ansatz: g_tt = -f.
fixtureMetricDelta : ℚ → ℚ
fixtureMetricDelta deltaLambda =
  - (kottlerLapseDelta
      Bubble.fixtureRadius
      Bubble.fixtureMass
      Bubble.fixtureExteriorLambda
      deltaLambda)

fixtureMetricDeltaIsFourThirdsDeltaLambda :
  ∀ deltaLambda →
  fixtureMetricDelta deltaLambda ≡ (Int.+ 4 / 3) * deltaLambda
fixtureMetricDeltaIsFourThirdsDeltaLambda = solve-∀

preferredSingleVacuumMetricDelta : ℚ → ℚ
preferredSingleVacuumMetricDelta deltaLambda =
  - (kottlerLapseDelta
      SingleVacuum.fixtureRadius
      SingleVacuum.fixtureMass
      SingleVacuum.fixtureLambda
      deltaLambda)

preferredSingleVacuumMetricDeltaIsFourThirdsDeltaLambda :
  ∀ deltaLambda →
  preferredSingleVacuumMetricDelta deltaLambda
    ≡ (Int.+ 4 / 3) * deltaLambda
preferredSingleVacuumMetricDeltaIsFourThirdsDeltaLambda = solve-∀

scalarMetricPerturbationIsNotTTMode : Bool
scalarMetricPerturbationIsNotTTMode = true

------------------------------------------------------------------------
-- MECHANISM-SIGNATURE TEMPLATES
--
-- These are DASHI-authored hypothesis templates for discriminator design, not
-- source-entitled statements that any real device has these signatures.
------------------------------------------------------------------------

data MechanismClass : Set where
  ordinaryForceConfounder : MechanismClass
  inertiaOnlyCandidate : MechanismClass
  scalarMetricCandidate : MechanismClass
  propagatingTTCandidate : MechanismClass

record MechanismSignature : Set where
  constructor mechanism-signature
  field
    supportWeightChannel : Bool
    freeFallMetricChannel : Bool
    clockMetricChannel : Bool
    opticalMetricChannel : Bool
    propagatingTTChannel : Bool

open MechanismSignature public

signature : MechanismClass → MechanismSignature
signature ordinaryForceConfounder =
  mechanism-signature true false false false false
signature inertiaOnlyCandidate =
  mechanism-signature true false false false false
signature scalarMetricCandidate =
  mechanism-signature true true true true false
signature propagatingTTCandidate =
  mechanism-signature true true true true true

ordinaryForceHasNoIndependentMetricChannels : Bool
ordinaryForceHasNoIndependentMetricChannels = true

scalarMetricHasClockAndOpticalMetricChannels : Bool
scalarMetricHasClockAndOpticalMetricChannels = true

ttRequiresAdditionalWaveSectorReceipt : Bool
ttRequiresAdditionalWaveSectorReceipt = true

------------------------------------------------------------------------
-- CANDIDATE-BOUND EXPERIMENT CONTRACT
--
-- Cross-pollinates only the generic discipline of the newer field/geometry/
-- matter and precision-closure work: candidate identity, nuisance closure,
-- matched channels and replication are proof-relevant on the same experiment.
-- No sibling-PR theorem authority is imported here.
------------------------------------------------------------------------

record CandidateBoundFourChannelExperiment : Set₁ where
  constructor candidate-bound-four-channel-experiment
  field
    Candidate : Set
    candidate : Candidate

    prediction : SameStateFourChannelPrediction

    sameCandidateAcrossAllChannels : Bool
    sameCandidateAcrossAllChannelsIsTrue :
      sameCandidateAcrossAllChannels ≡ true

    ordinaryMomentumClosed : Bool
    ordinaryMomentumClosedIsTrue : ordinaryMomentumClosed ≡ true

    electromagneticBackgroundClosed : Bool
    electromagneticBackgroundClosedIsTrue :
      electromagneticBackgroundClosed ≡ true

    thermalMechanicalBackgroundClosed : Bool
    thermalMechanicalBackgroundClosedIsTrue :
      thermalMechanicalBackgroundClosed ≡ true

    crossChannelMetricConsistency : Bool
    crossChannelMetricConsistencyIsTrue :
      crossChannelMetricConsistency ≡ true

    nullAndCalibrationChannelsPresent : Bool
    nullAndCalibrationChannelsPresentIsTrue :
      nullAndCalibrationChannelsPresent ≡ true

    replicationRequired : Bool
    replicationRequiredIsTrue : replicationRequired ≡ true

open CandidateBoundFourChannelExperiment public

record FourChannelPromotionBoundary : Set where
  constructor four-channel-promotion-boundary
  field
    weightOnlyPromotesMetric : Bool
    supportForceAnomalyPromotesFreeFall : Bool
    scalarMetricPromotesTT : Bool
    sameMetricAcrossChannelsRequired : Bool
    nuisanceClosureRequired : Bool
    crossChannelConsistencyRequired : Bool
    replicationStillRequired : Bool

canonicalFourChannelPromotionBoundary : FourChannelPromotionBoundary
canonicalFourChannelPromotionBoundary =
  four-channel-promotion-boundary
    false false false true true true true
