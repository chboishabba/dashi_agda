{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityNambuKottlerObservableCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve; solve-∀)

import DASHI.Physics.Foundations.GRQFTNambuGotoRepulsiveBubbleMaxCutExact as Bubble
import DASHI.Physics.Foundations.GRQFTNambuGotoRepulsiveShellFamilyExact as Shell
import DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact as Junction
import DASHI.Physics.ExoticGravity.AntigravityDeviceMetricObservableCompilerExact as Generic

------------------------------------------------------------------------
-- CONCRETE OBSERVABLE PROJECTIONS OF THE SELECTED NAMBU/KOTTLER FIXTURE
------------------------------------------------------------------------

fixtureOutwardFreeFall : ℚ
fixtureOutwardFreeFall = Int.+ 5 / 24

fixtureOutwardFreeFallIsGeometryValue :
  Bubble.fixtureOutwardAcceleration ≡ fixtureOutwardFreeFall
fixtureOutwardFreeFallIsGeometryValue = refl

fixtureSupportWeightChange : ℚ → ℚ
fixtureSupportWeightChange passiveMass =
  Generic.supportWeightPrediction passiveMass fixtureOutwardFreeFall

fixtureSupportWeightChangeIsMinusFiveTwentyFourthsMass :
  ∀ passiveMass →
  fixtureSupportWeightChange passiveMass
  ≡ - (passiveMass * (Int.+ 5 / 24))
fixtureSupportWeightChangeIsMinusFiveTwentyFourthsMass = solve-∀

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

------------------------------------------------------------------------
-- EXACT DYNAMIC KOTTLER RESPONSE TO VACUUM-AMPLITUDE MODULATION
--
-- f(r,M,Lambda)=1-2M/r-Lambda r^2/3.  At fixed r and M,
--
--   f(Lambda+dLambda)-f(Lambda) = -(r^2/3)dLambda.
--
-- Since g_tt=-f in the signature used by this static ansatz, the corresponding
-- metric-component perturbation is +(r^2/3)dLambda.  At the selected R=2 this
-- is exactly +(4/3)dLambda.  This pays the geometry response to an amplitude
-- modulation.  It does NOT identify this scalar/time-time perturbation with the
-- transverse-traceless Schuetzhold GW mode; that same-object mode conversion is
-- a distinct dynamical/source problem.
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

kottlerMetricTTDelta : ℚ → ℚ → ℚ → ℚ → ℚ
kottlerMetricTTDelta radius mass lambda deltaLambda =
  - (kottlerLapseDelta radius mass lambda deltaLambda)

fixtureMetricTTDelta : ℚ → ℚ
fixtureMetricTTDelta deltaLambda =
  kottlerMetricTTDelta
    Bubble.fixtureRadius Bubble.fixtureMass Bubble.fixtureExteriorLambda deltaLambda

fixtureMetricTTDeltaIsFourThirdsDeltaLambda :
  ∀ deltaLambda →
  fixtureMetricTTDelta deltaLambda
  ≡ (Int.+ 4 / 3) * deltaLambda
fixtureMetricTTDeltaIsFourThirdsDeltaLambda = solve-∀

------------------------------------------------------------------------
-- Clock and optical calibration surfaces.
------------------------------------------------------------------------

record NambuKottlerClockCalibration : Set₁ where
  constructor nambu-kottler-clock-calibration
  field
    ClockObservable : Set
    compareLapseRoots : ℚ → ℚ → ClockObservable
    commonReferenceCalibration : Set
    commonReferenceCalibrationReceipt : commonReferenceCalibration

open NambuKottlerClockCalibration public

record NambuKottlerDynamicOpticalBridge : Set₁ where
  constructor nambu-kottler-dynamic-optical-bridge
  field
    DeviceControl : Set
    OpticalReadout : Set

    controlToDeltaLambda : DeviceControl → ℚ
    metricTTDeltaToOpticalReadout : ℚ → OpticalReadout

    sameStaticBackground : Set
    sameStaticBackgroundReceipt : sameStaticBackground

    physicalAmplitudeModulation : Set
    physicalAmplitudeModulationReceipt : physicalAmplitudeModulation

    SchuetzholdTTModeSameObject : Set
    schutzholdTTModeSameObjectReceipt : SchuetzholdTTModeSameObject

open NambuKottlerDynamicOpticalBridge public

record NambuKottlerObservableBoundary : Set where
  constructor nambu-kottler-observable-boundary
  field
    exactOutwardFreeFallProjectionConstructed : Bool
    exactSupportWeightProjectionConstructed : Bool
    exactInteriorExteriorLapseRootsReused : Bool
    sameNambuKottlerGeometryFeedsMechanicalAndClockChannels : Bool
    coordinateLapseDifferenceAloneIsPhysicalClockComparison : Bool
    kottlerLambdaModulationToMetricPerturbationClosed : Bool
    selectedMetricTTResponseIsFourThirdsDeltaLambda : Bool
    physicalDeviceAmplitudeModulationStillRequired : Bool
    SchutzholdTTModeIdentificationStillOpen : Bool
    opticalModulationMustUseSameStaticBackground : Bool

canonicalNambuKottlerObservableBoundary : NambuKottlerObservableBoundary
canonicalNambuKottlerObservableBoundary =
  nambu-kottler-observable-boundary
    true true true true false true true true true true
