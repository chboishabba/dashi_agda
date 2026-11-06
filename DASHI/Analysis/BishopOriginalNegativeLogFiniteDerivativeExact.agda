{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalNegativeLogFiniteDerivativeExact where

------------------------------------------------------------------------
-- K04d-LOG: DERIVATIVE OF THE *ACTUAL* SOURCE BISHOP LOG PARTIAL.
--
-- This directly eliminates F.3's original negative-log finite-term
-- derivative seam. It reuses the original factor derivative,
-- Nat-scale vs embedded-Nat multiplicative theorem, and the
-- EXISTING reciprocalNatCancels certificate, with no alternative
-- log function or abstract term-derivative authority.
--
-- Source literal:
--   sourceNegativeLogTerm x n = x^(n+1) * (1/(n+1)).
-- Result for EVERY n, x:
--   derivative_x(sourceNegativeLogTerm x n) = x^n.
-- Result for EVERY finite count N:
--   derivative_x(sum_(n<N) sourceNegativeLogTerm x n)
--       = sum_(n<N) x^n.
--
-- These are genuine BishopFactorDerivativeAt theorems, not
-- classical quotient-based differentiability claims. Uniform
-- derivative-limit interchange for infinite L_B remains a
-- distinct genuinely analytic obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as Power
import DASHI.Analysis.BishopNaturalScaleEmbeddingBridgeExact as Scale
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Reciprocal
import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as Log
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geometric

sourceLogCoefficient : Nat → R.ℝ
sourceLogCoefficient n =
  R._⋆ (Reciprocal.reciprocalNatRational n)

originalLogTermDerivativeCoefficient :
  (x : R.ℝ) (n : Nat) →
  R._≃_
    (R._*_
      (sourceLogCoefficient n)
      (Power.powerDerivative (suc n) x))
    (R.pow x n)
originalLogTermDerivativeCoefficient x n =
  let
    coefficient = sourceLogCoefficient n
    power = R.pow x n
    natural = NatReal.natReal (suc n)
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.*-cong RP.≃-refl (Power.powerDerivativeNatScale n x))
    (RP.≃-trans
      (RP.*-cong RP.≃-refl
        (Scale.recursiveScaleIsEmbeddedNaturalMultiply
          (suc n) power))
      (RP.≃-trans
        (solve 3
          (λ c v p →
            c ⊗ (v ⊗ p)
            ⊜ (c ⊗ v) ⊗ p)
          RP.≃-refl coefficient natural power)
        (RP.≃-trans
          (RP.*-cong
            (Reciprocal.embeddedReciprocalNatCancels n)
            RP.≃-refl)
          (RP.*-identityˡ power))))

-- The derivative is attached to the literal Native Log term, not a
-- hand-selected polynomial with a convenient derivative.
originalLogTermFactorDerivative :
  (x : R.ℝ) (n : Nat) →
  Factor.BishopFactorDerivativeAt
    (λ y → Log.sourceNegativeLogTerm y n)
    x
    (R.pow x n)
originalLogTermFactorDerivative x n =
  Factor.factorDerivativeCongruence
    (λ y →
      RP.*-comm
        (R.pow y (suc n))
        (sourceLogCoefficient n))
    (originalLogTermDerivativeCoefficient x n)
    (Factor.factorDerivativeScale
      (sourceLogCoefficient n)
      (Factor.powerFactorDerivative (suc n) x))

originalLogFinitePartial : R.ℝ → Nat → R.ℝ
originalLogFinitePartial x count =
  Seq.SeriesOf (Log.sourceNegativeLogTerm x) count

originalLogFinitePartialFactorDerivative :
  (x : R.ℝ) (count : Nat) →
  Factor.BishopFactorDerivativeAt
    (λ y → originalLogFinitePartial y count)
    x
    (Geometric.negativeLogDerivativePolynomial x count)
originalLogFinitePartialFactorDerivative x zero =
  Factor.factorDerivativeZero x
originalLogFinitePartialFactorDerivative x (suc count) =
  Factor.factorDerivativeAdd
    (originalLogFinitePartialFactorDerivative x count)
    (originalLogTermFactorDerivative x count)
