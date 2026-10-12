{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTVacuumLockInReversalEstimatorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Physics.Foundations.GRQFTVacuumAmplitudeDifferentialRenormalizationExact as Differential
import DASHI.Physics.Foundations.CMP119AntigravityDifferentialMetricResponseFirewallExact as Response

------------------------------------------------------------------------
-- DIFFERENTIAL / REVERSAL LOCK-IN ALGEBRA
--
-- Generic odd/even estimator algebra is exact.  Two signal levels are kept
-- distinct:
--
--   1. the legacy/source-normalization modulation from the pre-gravity lane;
--   2. the physical Delta-Lambda supplied by a same-state metric-response
--      receipt.
--
-- The former is not silently promoted into the latter.
------------------------------------------------------------------------

half : ℚ
half = Int.+ 1 / 2

positiveReadout : ℚ → ℚ → ℚ
positiveReadout signal background = signal + background

negativeReadout : ℚ → ℚ → ℚ
negativeReadout signal background = - signal + background

oddEstimator : ℚ → ℚ → ℚ
oddEstimator plus minus = half * (plus - minus)

evenEstimator : ℚ → ℚ → ℚ
evenEstimator plus minus = half * (plus + minus)

oddEstimatorRecoversSignal :
  ∀ signal background →
  oddEstimator
    (positiveReadout signal background)
    (negativeReadout signal background)
  ≡ signal
oddEstimatorRecoversSignal = solve-∀

evenEstimatorRecoversCommonBackground :
  ∀ signal background →
  evenEstimator
    (positiveReadout signal background)
    (negativeReadout signal background)
  ≡ background
evenEstimatorRecoversCommonBackground = solve-∀

------------------------------------------------------------------------
-- LEGACY NORMALIZATION-LEVEL MODULATION
------------------------------------------------------------------------

vacuumPositiveReadout :
  Differential.CommonCountertermVacuumModulation → ℚ → ℚ
vacuumPositiveReadout modulation background =
  positiveReadout (Differential.physicalVacuumDifference modulation) background

vacuumNegativeReadout :
  Differential.CommonCountertermVacuumModulation → ℚ → ℚ
vacuumNegativeReadout modulation background =
  negativeReadout (Differential.physicalVacuumDifference modulation) background

vacuumOddEstimator :
  Differential.CommonCountertermVacuumModulation → ℚ → ℚ
vacuumOddEstimator modulation background =
  oddEstimator
    (vacuumPositiveReadout modulation background)
    (vacuumNegativeReadout modulation background)

vacuumEvenEstimator :
  Differential.CommonCountertermVacuumModulation → ℚ → ℚ
vacuumEvenEstimator modulation background =
  evenEstimator
    (vacuumPositiveReadout modulation background)
    (vacuumNegativeReadout modulation background)

vacuumOddEstimatorRecoversPhysicalDifference :
  ∀ modulation background →
  vacuumOddEstimator modulation background
  ≡ Differential.physicalVacuumDifference modulation
vacuumOddEstimatorRecoversPhysicalDifference modulation background =
  oddEstimatorRecoversSignal
    (Differential.physicalVacuumDifference modulation)
    background

vacuumEvenEstimatorRecoversCommonBackground :
  ∀ modulation background →
  vacuumEvenEstimator modulation background ≡ background
vacuumEvenEstimatorRecoversCommonBackground modulation background =
  evenEstimatorRecoversCommonBackground
    (Differential.physicalVacuumDifference modulation)
    background

vacuumOddEstimatorIsCalibratedSourceDifference :
  ∀ modulation background →
  vacuumOddEstimator modulation background
  ≡ Differential.multiplicative modulation
      * (Differential.sourceOn modulation - Differential.sourceOff modulation)
vacuumOddEstimatorIsCalibratedSourceDifference modulation background
  rewrite vacuumOddEstimatorRecoversPhysicalDifference modulation background
        | Differential.physicalVacuumDifferenceIsMultiplicativeSourceDifference modulation =
  solve-∀
    (Differential.multiplicative modulation)
    (Differential.sourceOn modulation)
    (Differential.sourceOff modulation)

legacyPhysicalVacuumDifferenceNameIsNotYetGravitationalDeltaLambda : Bool
legacyPhysicalVacuumDifferenceNameIsNotYetGravitationalDeltaLambda = true

------------------------------------------------------------------------
-- PHYSICAL METRIC-RESPONSE / DELTA-LAMBDA MODULATION
------------------------------------------------------------------------

metricResponsePositiveReadout :
  Response.DifferentialMetricResponseReceipt → ℚ → ℚ
metricResponsePositiveReadout receipt background =
  positiveReadout (Response.physicalDeltaLambda receipt) background

metricResponseNegativeReadout :
  Response.DifferentialMetricResponseReceipt → ℚ → ℚ
metricResponseNegativeReadout receipt background =
  negativeReadout (Response.physicalDeltaLambda receipt) background

metricResponseOddEstimator :
  Response.DifferentialMetricResponseReceipt → ℚ → ℚ
metricResponseOddEstimator receipt background =
  oddEstimator
    (metricResponsePositiveReadout receipt background)
    (metricResponseNegativeReadout receipt background)

metricResponseEvenEstimator :
  Response.DifferentialMetricResponseReceipt → ℚ → ℚ
metricResponseEvenEstimator receipt background =
  evenEstimator
    (metricResponsePositiveReadout receipt background)
    (metricResponseNegativeReadout receipt background)

metricResponseOddEstimatorRecoversPhysicalDeltaLambda :
  ∀ receipt background →
  metricResponseOddEstimator receipt background
  ≡ Response.physicalDeltaLambda receipt
metricResponseOddEstimatorRecoversPhysicalDeltaLambda receipt background =
  oddEstimatorRecoversSignal
    (Response.physicalDeltaLambda receipt)
    background

metricResponseEvenEstimatorRecoversCommonBackground :
  ∀ receipt background →
  metricResponseEvenEstimator receipt background ≡ background
metricResponseEvenEstimatorRecoversCommonBackground receipt background =
  evenEstimatorRecoversCommonBackground
    (Response.physicalDeltaLambda receipt)
    background

metricResponseOddEstimatorIsScaledNormalizationDifference :
  ∀ receipt background →
  metricResponseOddEstimator receipt background
  ≡ Response.normalizationToGravityScale receipt
    * (Response.normalizationOn receipt - Response.normalizationOff receipt)
metricResponseOddEstimatorIsScaledNormalizationDifference receipt background
  rewrite metricResponseOddEstimatorRecoversPhysicalDeltaLambda receipt background
        | Response.normalizationDifferenceMatchesMetricResponseDifference receipt =
  solve-∀

record VacuumLockInReversalBoundary : Set where
  constructor vacuum-lock-in-reversal-boundary
  field
    oddHalfDifferenceCancelsCommonEvenBackground : Bool
    evenHalfSumRecoversCommonBackground : Bool
    normalizationLevelSignalFitsOddEstimatorAlgebra : Bool
    physicalDeltaLambdaFitsOddEstimatorAfterMetricResponseReceipt : Bool
    normalizationSignalAlreadyIsPhysicalDeltaLambda : Bool
    reversalParityStillNeedsPhysicalReceipt : Bool
    commonBackgroundParityStillNeedsPhysicalReceipt : Bool
    estimatorAlgebraAloneProvesPhysicalVacuumModulation : Bool

canonicalVacuumLockInReversalBoundary : VacuumLockInReversalBoundary
canonicalVacuumLockInReversalBoundary =
  vacuum-lock-in-reversal-boundary
    true true true true false true true false

reversalParityStillNeedsPhysicalReceipt : Bool
reversalParityStillNeedsPhysicalReceipt = true

estimatorAlgebraAloneProvesPhysicalVacuumModulation : Bool
estimatorAlgebraAloneProvesPhysicalVacuumModulation = false
