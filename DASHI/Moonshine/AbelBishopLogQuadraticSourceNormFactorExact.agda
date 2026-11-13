module DASHI.Moonshine.AbelBishopLogQuadraticSourceNormFactorExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP LOG: EXACT SOURCE QUADRATIC FACTOR AND NORM SQUARE
--
-- Literal coefficient stream:
--   a_(n+1)(w) = (-1)^(n+1)/(n+2) * w^(n+2).
--
-- The earlier upper-disk convergence and half-geometric majorant
-- bound each coordinate by r^(n+2)/2. That is NOT sufficient by
-- itself to produce the sharp |w|^2 remainder bound at every w.
--
-- This module proves the missing finite, SAME-OBJECT identity:
--   a_(n+1)(w) ~= coefficient * ((w*w) * w^n)
-- and its ORIGINAL BISHOP norm-square identity
--   N(a_(n+1)(w)) ~= coefficient^2 * N(w)^(n+2).
--
-- Uses original Bishop setoid multiplication, original source
-- coefficient, original Norm.normSqScale and Norm.normSqPower;
-- no new analytic structure, norm oracle or completeness premise.
--
-- The infinite finite-sum triangle/norm-limit order step remains
-- mathematically OPEN; these source lemmas are not a proof of the
-- selected 8/27 analytic remainder, nor of a fixed point/Kneser.
-- Source-written; local Agda 2.9 kernel receipt pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Moonshine.AbelBishopLogQuadraticHalfCoefficientExact as Half
import Sequence as BishopSequence
import DASHI.Moonshine.AbelBishopLogOnePlusOriginalSeriesExact as Log
import DASHI.Moonshine.AbelBishopSelectedLogAffineReconstructionExact as Affine
import DASHI.Moonshine.AbelBishopInverseKoenigsRemainderFactorExact as Ring

-- Actual shifted logarithm term, no replacement of the coefficient.
originalBishopQuadraticSourceTerm :
  Complex.BishopComplex → Nat → Complex.BishopComplex
originalBishopQuadraticSourceTerm w n =
  Log.originalBishopLogOnePlusTerm w (suc n)

originalBishopQuadraticSourceTermFactor :
  ∀ w n →
  Complex._≈C_
    (originalBishopQuadraticSourceTerm w n)
    (Algebra.scaleC
      (Log.logCoefficient (suc n))
      (Algebra._*C_
        (Algebra._*C_ w w)
        (Algebra.powC w n)))
originalBishopQuadraticSourceTermFactor w n =
  Algebra.scaleCCongruent
    (Affine.complexMulAssociative w w (Algebra.powC w n))
    (Log.logCoefficient (suc n))

originalBishopQuadraticSourceFirstTerm :
  ∀ w →
  Complex._≈C_
    (originalBishopQuadraticSourceTerm w zero)
    (Algebra.scaleC
      (Log.logCoefficient (suc zero))
      (Algebra._*C_ w w))
originalBishopQuadraticSourceFirstTerm w =
  Ring.complexTrans
    (originalBishopQuadraticSourceTermFactor w zero)
    (Algebra.scaleCCongruent
      (Affine.complexOneRight (Algebra._*C_ w w))
      (Log.logCoefficient (suc zero)))

-- This exact identity retains the true N(w)^(n+2) factor.
-- Replacing it by a disk-radius bound too early loses precisely
-- the sharp quadratic dependence required for the Koenigs estimate.
originalBishopQuadraticSourceNormSquare :
  ∀ w n →
  BishopReal._≃_
    (Norm.normSqC (originalBishopQuadraticSourceTerm w n))
    (BishopReal._*_
      (Norm.square (Log.logCoefficient (suc n)))
      (BishopReal.pow (Norm.normSqC w) (suc (suc n))))
originalBishopQuadraticSourceNormSquare w n =
  BishopP.≃-trans
    (Norm.normSqScale
      (Log.logCoefficient (suc n))
      (Algebra.powC w (suc (suc n))))
    (BishopP.*-congˡ
      (Norm.normSqPower w (suc (suc n))))

-- Both results are exact original-setoid equalities; no need for an
-- arbitrary complex scalar, selected exponentiation or branch axiom.

------------------------------------------------------------------------
-- SHARP TRUE-SOURCE NORM-SQUARE TERM MAJORANT (NO DISK ASSUMPTION).
--
-- N(a_(n+1)(w)) <= (1/2)^2 * N(w)^(n+2).
-- Unlike the component envelopes at a chosen radius, this retains
-- N(w) at each coefficient and supplies the missing input for a
-- finite COMPLEX triangle and Bishop limit-order comparison.
------------------------------------------------------------------------

originalBishopShiftedCoefficientSquareBelowQuarter :
  ∀ n →
  BishopReal._≤_
    (Norm.square (Log.logCoefficient (suc n)))
    (Norm.square Half.bishopHalf)
originalBishopShiftedCoefficientSquareBelowQuarter n =
  let
    coefficient = Log.logCoefficient (suc n)
    absoluteNonnegative = BishopP.nonNeg∣x∣ coefficient
    coefficientBelowHalf =
      Half.originalShiftedBishopLogCoefficientBelowHalf n
  in
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm (Norm.absoluteSquare coefficient))
    (BishopP.*-mono-≤
      absoluteNonnegative
      absoluteNonnegative
      coefficientBelowHalf
      coefficientBelowHalf)

originalBishopQuadraticSourceNormSquareUpper :
  ∀ w n →
  BishopReal._≤_
    (Norm.normSqC (originalBishopQuadraticSourceTerm w n))
    (BishopReal._*_
      (Norm.square Half.bishopHalf)
      (BishopReal.pow (Norm.normSqC w) (suc (suc n))))
originalBishopQuadraticSourceNormSquareUpper w n =
  BishopP.≤-respˡ-≃
    (originalBishopQuadraticSourceNormSquare w n)
    (BishopP.*-monoʳ-≤-nonNeg
      (originalBishopShiftedCoefficientSquareBelowQuarter n)
      (BishopSequence.nonNegx⇒nonNegxⁿ
        (suc (suc n))
        (Upper.normSquareNonnegative w)))

