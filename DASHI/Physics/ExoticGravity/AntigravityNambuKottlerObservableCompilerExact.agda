{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityNambuKottlerObservableCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve; solve-∀)

import DASHI.Physics.Foundations.GRQFTNambuGotoRepulsiveBubbleMaxCutExact as Bubble
import DASHI.Physics.Foundations.GRQFTNambuGotoRepulsiveShellFamilyExact as Shell
import DASHI.Physics.ExoticGravity.AntigravityDeviceMetricObservableCompilerExact as Generic

------------------------------------------------------------------------
-- CONCRETE OBSERVABLE PROJECTIONS OF THE SELECTED NAMBU/KOTTLER FIXTURE
--
-- Selected exact geometry:
--   R = 2
--   M = 2/9
--   Lambda_in  = 21/64
--   Lambda_out = 19/48
--   a_out(R)   = 5/24
--   sqrt(f_in(R))  = 3/4
--   sqrt(f_out(R)) = 1/2.
--
-- The mechanical and lapse/clock carriers below are therefore projections of
-- one already-constructed nonlinear geometry, not independent fit parameters.
-- The Schuetzhold controlled EM<->GW method is intrinsically dynamical: to use
-- that exact energy-exchange readout on this static candidate, the device must
-- be modulated so the metric acquires a time-dependent perturbation h(t).
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

-- Coordinate lapse roots are exact geometry carriers.  A physical comparison
-- of clocks in different charts still requires a common-reference worldline or
-- signal-exchange calibration; we do not manufacture that identification.
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
    MetricPerturbation : Set
    OpticalReadout : Set

    controlToMetricPerturbation : DeviceControl → MetricPerturbation
    metricPerturbationToOpticalReadout : MetricPerturbation → OpticalReadout

    TimeDependentModulationReceipt : Set
    timeDependentModulationReceipt : TimeDependentModulationReceipt

    SameStaticBackgroundReceipt : Set
    sameStaticBackgroundReceipt : SameStaticBackgroundReceipt

open NambuKottlerDynamicOpticalBridge public

record NambuKottlerObservableBoundary : Set where
  constructor nambu-kottler-observable-boundary
  field
    exactOutwardFreeFallProjectionConstructed : Bool
    exactSupportWeightProjectionConstructed : Bool
    exactInteriorExteriorLapseRootsReused : Bool
    sameNambuKottlerGeometryFeedsMechanicalAndClockChannels : Bool
    coordinateLapseDifferenceAloneIsPhysicalClockComparison : Bool
    SchutzholdDynamicOpticalUseRequiresTimeDependentModulation : Bool
    staticCandidateAutomaticallySuppliesDynamicMetricPerturbation : Bool
    opticalModulationMustUseSameStaticBackground : Bool

canonicalNambuKottlerObservableBoundary : NambuKottlerObservableBoundary
canonicalNambuKottlerObservableBoundary =
  nambu-kottler-observable-boundary
    true true true true false true false true
