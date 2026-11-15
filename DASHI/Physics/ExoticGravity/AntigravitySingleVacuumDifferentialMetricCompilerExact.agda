{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravitySingleVacuumDifferentialMetricCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Physics.Foundations.GRQFTVacuumAmplitudeDifferentialRenormalizationExact as Differential
import DASHI.Physics.ExoticGravity.AntigravityNambuKottlerObservableCompilerExact as Metric

------------------------------------------------------------------------
-- DIFFERENTIAL SOURCE AMPLITUDE -> SELECTED KOTTLER METRIC RESPONSE
------------------------------------------------------------------------

fixtureMetricResponseFromVacuumModulation :
  Differential.CommonCountertermVacuumModulation → ℚ
fixtureMetricResponseFromVacuumModulation modulation =
  Metric.fixtureMetricTTDelta
    (Differential.physicalVacuumDifference modulation)

fixtureMetricResponseIsFourThirdsSourceDifference :
  ∀ modulation →
  fixtureMetricResponseFromVacuumModulation modulation
  ≡
  (Int.+ 4 / 3)
    * Differential.multiplicative modulation
    * (Differential.sourceOn modulation - Differential.sourceOff modulation)
fixtureMetricResponseIsFourThirdsSourceDifference modulation
  rewrite Metric.fixtureMetricTTDeltaIsFourThirdsDeltaLambda
    (Differential.physicalVacuumDifference modulation)
        | Differential.physicalVacuumDifferenceIsMultiplicativeSourceDifference modulation =
  solve-∀
    (Differential.multiplicative modulation)
    (Differential.sourceOn modulation)
    (Differential.sourceOff modulation)

record DifferentialMetricCompilerBoundary : Set where
  constructor differential-metric-compiler-boundary
  field
    commonAdditiveVacuumZeroRemovedFromMetricDifference : Bool
    sourceDifferenceToMetricResponseClosedModuloMultiplicativeCalibration : Bool
    absoluteStaticLambdaNeededForLockInDifference : Bool
    physicalControlToSourceDifferenceStillOpen : Bool
    multiplicativeSICalibrationStillOpen : Bool
    scalarMetricPerturbationAlreadyEqualsSchutzholdTTMode : Bool

canonicalDifferentialMetricCompilerBoundary : DifferentialMetricCompilerBoundary
canonicalDifferentialMetricCompilerBoundary =
  differential-metric-compiler-boundary
    true true false true true false
