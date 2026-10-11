module DASHI.Physics.Closure.E6HyperformAtomicClockCalibrationNoGoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge as Clock
import DASHI.Physics.Closure.E6HyperformPoissonLorentzMetricExact as Metric

------------------------------------------------------------------------
-- ATOMIC-CLOCK EMPIRICAL CALIBRATION / NAIVE-SCALE NO-GO
--
-- External empirical donor: dashi_agda PR #1117, public Bothwell--Ye 2022
-- redshift comparison.  Its same-scale published theory is approximately
-- 1.09e-19 fractional-frequency gradient per millimetre; corrected measured
-- central value is approximately 0.98e-19 mm^-1 with 0.23e-19 uncertainty.
--
-- Candidate SI identification used deliberately as a falsifier:
-- one ternary lattice edge = light-travel distance during one Cs-133 defining
-- transition period,
--
--   a = c / Delta nu_Cs
--     = 299792458 / 9192631770 m
--     ~= 32.61225571749406 mm.
--
-- For the unit-amplitude metric Omega=1+phi, the largest vertical derivative
-- on the 27 chart occurs at (0,-1,-1) (and the sign-related partner), where
--
--   phi=-11/54, |d_z phi|=5/9,
--   |d_z log Omega|=30/43.
--
-- Therefore this candidate scale predicts about
--   0.02139301324778956 mm^-1,
-- over 1e17 times the laboratory gravitational-redshift gradient.  The naive
-- identification is empirically excluded.
--
-- A weak-amplitude family Omega_epsilon=1+epsilon phi can match the published
-- theory at this selected maximum-gradient point only with
--   epsilon ~= 6.39852457177233e-18
-- (corrected central measurement: ~=5.752801908565952e-18).
-- This epsilon is a required calibration/derivation target, not a fitted
-- fundamental constant promoted from one experiment.
------------------------------------------------------------------------

record ExceptionalAtomicClockCalibrationReceipt : Set where
  constructor exceptional-atomic-clock-calibration-receipt
  field
    existingCs133SISecondBridgeConsumed : Bool
    candidateEdgeDefinition : String
    candidateEdgeMillimetres : String
    selectedVerticalChartPoint : String
    selectedPhi : String
    selectedAbsoluteDPhiDZ : String
    unitAmplitudeAbsoluteDLogOmegaDZ : String
    unitAmplitudeGradientPerMillimetre : String
    bothwellYePublishedTheoryGradientPerMillimetre : String
    bothwellYeCorrectedCentralGradientPerMillimetre : String
    unitAmplitudeMismatchExceeds1e17 : Bool
    naiveAtomicEdgeUnitAmplitudeIdentificationRefuted : Bool
    weakAmplitudeEpsilonTheoryMatch : String
    weakAmplitudeEpsilonCorrectedCentralMatch : String
    epsilonDerivedFromFirstPrinciples : Bool
    oneExperimentCreatesUniversalEpsilon : Bool
    physicalGravityBridgeClosed : Bool
    boundary : String
open ExceptionalAtomicClockCalibrationReceipt public

canonicalExceptionalAtomicClockCalibrationReceipt : ExceptionalAtomicClockCalibrationReceipt
canonicalExceptionalAtomicClockCalibrationReceipt =
  exceptional-atomic-clock-calibration-receipt
    true
    "candidate only: one edge = c / Delta nu_Cs"
    "32.61225571749406"
    "(0,-1,-1)"
    "-11/54" "5/9" "30/43"
    "0.02139301324778956"
    "1.09e-19"
    "0.98e-19"
    true true
    "6.39852457177233e-18"
    "5.752801908565952e-18"
    false false false
    "The unit-amplitude exceptional conformal field together with the candidate one-Cs-period light-travel edge is excluded by the public millimetre-scale clock gradient by more than 17 orders of magnitude. A weak coupling/refinement factor is mandatory if this field is to enter physical gravity. Matching one experiment estimates epsilon but does not derive or universalize it."

record ExceptionalGravityScaleReceipt : Set₁ where
  field
    scaleParameter : Set
    finiteToContinuumLengthScaleReceipt : Set
    fieldAmplitudeScaleReceipt : Set
    SIUnitCalibrationReceipt : Set
    heldOutClockPredictionReceipt : Set
    independentGravityObservableReceipt : Set
open ExceptionalGravityScaleReceipt public

data NaiveScaleNoGoRefutesExceptionalGeometry : Set where

naiveScaleNoGoDoesNotRefuteExceptionalGeometry :
  NaiveScaleNoGoRefutesExceptionalGeometry → {A : Set} → A
naiveScaleNoGoDoesNotRefuteExceptionalGeometry ()
