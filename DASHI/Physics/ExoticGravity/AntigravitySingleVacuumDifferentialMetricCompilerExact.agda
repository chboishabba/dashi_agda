{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravitySingleVacuumDifferentialMetricCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Physics.Foundations.GRQFTVacuumAmplitudeDifferentialRenormalizationExact as Differential

-- Lambda-dependent part of g_tt = -f for Kottler
-- f = 1 - 2M/r - Lambda r^2/3.
kottlerMetricTTLambdaTerm : ℚ → ℚ → ℚ
kottlerMetricTTLambdaTerm radius lambda =
  lambda * radius * radius / (Int.+ 3 / 1)

kottlerMetricTTDelta : ℚ → ℚ → ℚ → ℚ
kottlerMetricTTDelta radius lambdaOff lambdaOn =
  kottlerMetricTTLambdaTerm radius lambdaOn
  - kottlerMetricTTLambdaTerm radius lambdaOff

kottlerMetricTTDeltaIsRadiusSquaredThirdDeltaLambda :
  ∀ radius lambdaOff lambdaOn →
  kottlerMetricTTDelta radius lambdaOff lambdaOn
  ≡ (radius * radius / (Int.+ 3 / 1)) * (lambdaOn - lambdaOff)
kottlerMetricTTDeltaIsRadiusSquaredThirdDeltaLambda = solve-∀

sourceModulationMetricTTDelta :
  ℚ → Differential.CommonCountertermVacuumModulation → ℚ
sourceModulationMetricTTDelta radius modulation =
  (radius * radius / (Int.+ 3 / 1))
  * Differential.physicalVacuumDifference modulation

sourceModulationMetricTTDeltaIsCalibratedSourceDifference :
  ∀ radius modulation →
  sourceModulationMetricTTDelta radius modulation
  ≡ (radius * radius / (Int.+ 3 / 1))
    * Differential.multiplicative modulation
    * (Differential.sourceOn modulation - Differential.sourceOff modulation)
sourceModulationMetricTTDeltaIsCalibratedSourceDifference radius modulation
  rewrite Differential.physicalVacuumDifferenceIsMultiplicativeSourceDifference modulation =
  solve-∀ radius
    (Differential.multiplicative modulation)
    (Differential.sourceOn modulation)
    (Differential.sourceOff modulation)

fixtureRadiusTwoMetricGain :
  ∀ deltaLambda →
  (Int.+ 2 / 1 * (Int.+ 2 / 1) / (Int.+ 3 / 1)) * deltaLambda
  ≡ (Int.+ 4 / 3) * deltaLambda
fixtureRadiusTwoMetricGain = solve-∀

record DifferentialMetricCompilerBoundary : Set where
  constructor differential-metric-compiler-boundary
  field
    commonAdditiveVacuumZeroRemovedFromMetricDifference : Bool
    sourceDifferenceToScalarMetricResponseClosedModuloMultiplicativeCalibration : Bool
    absoluteStaticLambdaNeededForLockInDifference : Bool
    physicalControlToSourceDifferenceStillOpen : Bool
    multiplicativeSICalibrationStillOpen : Bool
    scalarMetricPerturbationAlreadyEqualsSchutzholdTTMode : Bool

canonicalDifferentialMetricCompilerBoundary : DifferentialMetricCompilerBoundary
canonicalDifferentialMetricCompilerBoundary =
  differential-metric-compiler-boundary true true false true true false
