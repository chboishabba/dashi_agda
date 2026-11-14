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
    sameMetricFeedsAllFourChannelsIsTrue : sameMetricFeedsAllFourChannels ≡ true

open SameStateFourChannelPrediction public

------------------------------------------------------------------------
-- SOURCE -> STRESS -> METRIC PROVENANCE CHAIN
--
-- The metric carrier is taken definitionally from the selected prediction, so
-- no auxiliary equality between metric carrier types or hidden transport is
-- required.  The stored metric state itself must be literally the result of
-- applying stressToMetric to the stress compiled from the selected source.
------------------------------------------------------------------------

record SameStateStressMetricFourChannelChain : Set₁ where
  constructor same-state-stress-metric-four-channel-chain
  field
    SourceState StressState : Set
    selectedSource : SourceState
    sourceToStress : SourceState → StressState
    selectedPrediction : SameStateFourChannelPrediction
    stressToMetric :
      StressState → SameStateFourChannelPrediction.MetricState selectedPrediction
    predictionMetricIsSameStressDerivedMetric :
      SameStateFourChannelPrediction.metricState selectedPrediction
      ≡ stressToMetric (sourceToStress selectedSource)

open SameStateStressMetricFourChannelChain public

sameSourceStressMetricChainRequired : Bool
sameSourceStressMetricChainRequired = true

sharedProjectionDoesNotIdentifyFullStress : Bool
sharedProjectionDoesNotIdentifyFullStress = true

weightOnlyCannotPromoteMetricClaim : Bool
weightOnlyCannotPromoteMetricClaim = true

anomalyAloneIsNotGeometry : Bool
anomalyAloneIsNotGeometry = true

------------------------------------------------------------------------
-- OLDER EXACT NAMBU/KOTTLER FIXTURE, RETAINED AS A REGRESSION/DONOR EXAMPLE.
------------------------------------------------------------------------

fixtureOutwardFreeFall : ℚ
fixtureOutwardFreeFall = Bubble.fixtureOutwardAcceleration

fixtureOutwardFreeFallIsFiveTwentyFourths :
  fixtureOutwardFreeFall ≡ Int.+ 5 / 24
fixtureOutwardFreeFallIsFiveTwentyFourths = refl

fixtureSupportWeightChange : ℚ → ℚ
fixtureSupportWeightChange passiveMass = - (passiveMass * fixtureOutwardFreeFall)

fixtureExteriorLapseRoot : ℚ
fixtureExteriorLapseRoot = Shell.y

fixtureInteriorLapseRoot : ℚ
fixtureInteriorLapseRoot = Shell.x

fixtureExteriorLapseRootIsHalf : fixtureExteriorLapseRoot ≡ Int.+ 1 / 2
fixtureExteriorLapseRootIsHalf = refl

fixtureInteriorLapseRootIsThreeQuarters : fixtureInteriorLapseRoot ≡ Int.+ 3 / 4
fixtureInteriorLapseRootIsThreeQuarters = refl

olderNambuFixtureIsRegressionNotPreferredSourceRoute : Bool
olderNambuFixtureIsRegressionNotPreferredSourceRoute = true

------------------------------------------------------------------------
-- PREFERRED SINGLE-VACUUM NORMALIZED FIXTURE.
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
    SingleVacuum.fixtureRadius SingleVacuum.fixtureX SingleVacuum.fixtureY

preferredSingleVacuumOutwardScaledIsSeventySevenSeventyFifths :
  preferredSingleVacuumOutwardScaled ≡ Int.+ 77 / 75
preferredSingleVacuumOutwardScaledIsSeventySevenSeventyFifths =
  SingleVacuum.fixtureOutwardScaledIsSeventySevenSeventyFifths

preferredSingleVacuumOutwardFreeFall : ℚ
preferredSingleVacuumOutwardFreeFall =
  preferredSingleVacuumOutwardScaled /
  (preferredSingleVacuumFixtureRadius * preferredSingleVacuumFixtureRadius)

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

fixtureMetricDelta : ℚ → ℚ
fixtureMetricDelta deltaLambda =
  - (kottlerLapseDelta Bubble.fixtureRadius Bubble.fixtureMass
      Bubble.fixtureExteriorLambda deltaLambda)

fixtureMetricDeltaIsFourThirdsDeltaLambda :
  ∀ deltaLambda → fixtureMetricDelta deltaLambda ≡ (Int.+ 4 / 3) * deltaLambda
fixtureMetricDeltaIsFourThirdsDeltaLambda = solve-∀

preferredSingleVacuumMetricDelta : ℚ → ℚ
preferredSingleVacuumMetricDelta deltaLambda =
  - (kottlerLapseDelta SingleVacuum.fixtureRadius SingleVacuum.fixtureMass
      SingleVacuum.fixtureLambda deltaLambda)

preferredSingleVacuumMetricDeltaIsFourThirdsDeltaLambda :
  ∀ deltaLambda →
  preferredSingleVacuumMetricDelta deltaLambda ≡ (Int.+ 4 / 3) * deltaLambda
preferredSingleVacuumMetricDeltaIsFourThirdsDeltaLambda = solve-∀

scalarMetricPerturbationIsNotTTMode : Bool
scalarMetricPerturbationIsNotTTMode = true

------------------------------------------------------------------------
-- MECHANISM-SIGNATURE TEMPLATES
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
signature ordinaryForceConfounder = mechanism-signature true false false false false
signature inertiaOnlyCandidate = mechanism-signature true false false false false
signature scalarMetricCandidate = mechanism-signature true true true true false
signature propagatingTTCandidate = mechanism-signature true true true true true

ordinaryForceHasNoIndependentMetricChannels : Bool
ordinaryForceHasNoIndependentMetricChannels = true

scalarMetricHasClockAndOpticalMetricChannels : Bool
scalarMetricHasClockAndOpticalMetricChannels = true

ttRequiresAdditionalWaveSectorReceipt : Bool
ttRequiresAdditionalWaveSectorReceipt = true

------------------------------------------------------------------------
-- CANDIDATE-BOUND EXPERIMENT CONTRACT
------------------------------------------------------------------------

record CandidateBoundFourChannelExperiment : Set₁ where
  constructor candidate-bound-four-channel-experiment
  field
    Candidate : Set
    candidate : Candidate
    prediction : SameStateFourChannelPrediction
    sameCandidateAcrossAllChannels : Bool
    sameCandidateAcrossAllChannelsIsTrue : sameCandidateAcrossAllChannels ≡ true
    ordinaryMomentumClosed : Bool
    ordinaryMomentumClosedIsTrue : ordinaryMomentumClosed ≡ true
    electromagneticBackgroundClosed : Bool
    electromagneticBackgroundClosedIsTrue : electromagneticBackgroundClosed ≡ true
    thermalMechanicalBackgroundClosed : Bool
    thermalMechanicalBackgroundClosedIsTrue : thermalMechanicalBackgroundClosed ≡ true
    crossChannelMetricConsistency : Bool
    crossChannelMetricConsistencyIsTrue : crossChannelMetricConsistency ≡ true
    nullAndCalibrationChannelsPresent : Bool
    nullAndCalibrationChannelsPresentIsTrue : nullAndCalibrationChannelsPresent ≡ true
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
  four-channel-promotion-boundary false false false true true true true
