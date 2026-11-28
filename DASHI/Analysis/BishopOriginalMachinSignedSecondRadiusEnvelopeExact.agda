module DASHI.Analysis.BishopOriginalMachinSignedSecondRadiusEnvelopeExact where

-- ORIGINAL NATIVE BISHOP SIGNED FINITE SECOND-DEFECT ENVELOPE.
-- All-N, genuine original source coefficients, negative x/h permitted.
-- This composes:
--   original term sign/odd reciprocal absolute readback;
--   source-native all-N finite series triangle;
--   signed power-second absolute-to-nonnegative endpoint bridge;
--   pre-existing original LOG power-second radius order theorem.
--
-- For |x|,|x+h|<=1/2, the literal original Bishop S_N satisfies
--
--   |S_N(x,h)| <= Σ_{k<N}
--       (1/(2k+1)) * T_(2k+1)(1/2,0).
--
-- Remaining ONLY: actual Bishop finite-positive sum identification
-- with B_N=8/9*(1-(3N+1)/4^N), then B_N<=8/9.
-- SOURCE-WRITTEN, Agda native kernel pending.

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopOriginalMachinAtanQuotientSecondOrderExact as Original
import DASHI.Analysis.BishopOriginalMachinSignedSecondTriangleExact as Triangle
import DASHI.Analysis.BishopOriginalMachinSignedPowerRadiusExact as Radius
import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as PowerSecond
import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimate

sourceRadiusTerm : Nat → R.ℝ
sourceRadiusTerm k =
  R._*_
    (R._⋆ (Atan.inverseOddRational k))
    (PowerSecond.sourcePowerSecondQuotient
      Half.bishopHalf R.0ℝ (Estimate.oddExponent k))

sourceRadiusBudget : Nat → R.ℝ
sourceRadiusBudget n = Seq.SeriesOf sourceRadiusTerm n

originalTermAbsoluteBelowRadius :
  (x h : R.ℝ) →
  (xInside : R._≤_ (R.∣ x ∣) Half.bishopHalf) →
  (yInside : R._≤_ (R.∣ R._+_ x h ∣) Half.bishopHalf) →
  (k : Nat) →
  R._≤_
    (R.∣ Original.termSecond x h k ∣)
    (sourceRadiusTerm k)
originalTermAbsoluteBelowRadius x h xInside yInside k =
  P.≤-respˡ-≃
    (Triangle.originalSecondTermAbsoluteOdd x h k)
    (P.*-monoˡ-≤-nonNeg
      (Radius.originalSignedSecondBelowHalf
        x h xInside yInside (Estimate.oddExponent k))
      (Atan.embeddedInverseOddNonnegative k))

originalCoefficientAbsoluteSumBelowRadius :
  (x h : R.ℝ) →
  (xInside : R._≤_ (R.∣ x ∣) Half.bishopHalf) →
  (yInside : R._≤_ (R.∣ R._+_ x h ∣) Half.bishopHalf) →
  (n : Nat) →
  R._≤_
    (Seq.SeriesOf
      (λ k → R.∣ Original.termSecond x h k ∣) n)
    (sourceRadiusBudget n)
originalCoefficientAbsoluteSumBelowRadius
  x h xInside yInside zero = P.≤-refl
originalCoefficientAbsoluteSumBelowRadius
  x h xInside yInside (suc n) =
  P.+-mono-≤
    (originalCoefficientAbsoluteSumBelowRadius
      x h xInside yInside n)
    (originalTermAbsoluteBelowRadius
      x h xInside yInside n)

originalSignedFiniteSecondBelowRadius :
  (x h : R.ℝ) →
  (xInside : R._≤_ (R.∣ x ∣) Half.bishopHalf) →
  (yInside : R._≤_ (R.∣ R._+_ x h ∣) Half.bishopHalf) →
  (n : Nat) →
  R._≤_
    (R.∣ Original.finiteSecond x h n ∣)
    (sourceRadiusBudget n)
originalSignedFiniteSecondBelowRadius
  x h xInside yInside n =
  P.≤-trans
    (Triangle.originalSignedFiniteSecondTriangle x h n)
    (originalCoefficientAbsoluteSumBelowRadius
      x h xInside yInside n)

-- Diagnostic boundary: do not add a field "S_N<=8/9" as a
-- theorem assumption; prove the single remaining exact source
-- radiusBudget(n)=embedded(8/9*(1-(3n+1)/4^n)) with existing
-- nonnegative Bishop power/reciprocal embedding constructors.
