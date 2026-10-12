{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTVacuumLockInReversalEstimatorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Physics.Foundations.GRQFTVacuumAmplitudeDifferentialRenormalizationExact as Differential

------------------------------------------------------------------------
-- DIFFERENTIAL / REVERSAL LOCK-IN ALGEBRA
--
-- If a physical reversal really sends the target signal S -> -S while leaving
-- one nuisance/background coordinate B unchanged, then the odd half-difference
-- exactly recovers S and the even half-sum exactly recovers B:
--
--   y+ =  S + B
--   y- = -S + B
--   (y+ - y-)/2 = S
--   (y+ + y-)/2 = B.
--
-- This is only the estimator algebra.  The experiment still owes same-object
-- receipts that the selected control produces the sign reversal and that the
-- nuisance term is common/even under that reversal.
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

record VacuumLockInReversalBoundary : Set where
  constructor vacuum-lock-in-reversal-boundary
  field
    oddHalfDifferenceCancelsCommonEvenBackground : Bool
    evenHalfSumRecoversCommonBackground : Bool
    differentialVacuumSignalFitsOddEstimatorAlgebra : Bool
    reversalParityStillNeedsPhysicalReceipt : Bool
    commonBackgroundParityStillNeedsPhysicalReceipt : Bool
    estimatorAlgebraAloneProvesPhysicalVacuumModulation : Bool

canonicalVacuumLockInReversalBoundary : VacuumLockInReversalBoundary
canonicalVacuumLockInReversalBoundary =
  vacuum-lock-in-reversal-boundary
    true true true true true false

reversalParityStillNeedsPhysicalReceipt : Bool
reversalParityStillNeedsPhysicalReceipt = true

estimatorAlgebraAloneProvesPhysicalVacuumModulation : Bool
estimatorAlgebraAloneProvesPhysicalVacuumModulation = false
