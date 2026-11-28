module DASHI.Analysis.BishopOriginalMachinSignedSecondTriangleExact where

-- ALL-N, ORIGINAL BISHOP NATIVE FINITE-TRIANGLE WELD.
--
-- The original source finite arctangent second quotient is a finite
-- SeriesOf with the literal signed odd reciprocal coefficients.
-- Use the existing universal Bishop finite series triangle theorem.
-- The alternating sign has absolute value ONE; the odd reciprocal is
-- already a constructive nonnegative Bishop real.
--
-- No extra quotient, no new atan, no classical abs/sum carrier.
-- The only remaining analytic/order task is the pointwise bound
--   |T_(2k+1)(x,x+h)| <= (2k+1)*k*(1/2)^(2k-1)
-- and transport of the exact finite rational budget 8/9 into Bishop.
-- SOURCE-WRITTEN; kernel acceptance not yet executed.

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Foundations.BishopFiniteSeriesAbsoluteBoundExact as Triangle
import DASHI.Analysis.BishopOriginalMachinAtanQuotientSecondOrderExact as Original
import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as PowerSecond
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Sign
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimate

originalSecondAsActualFiniteSeries :
  (x h : R.ℝ) (n : Nat) →
  R._≃_
    (Original.finiteSecond x h n)
    (Seq.SeriesOf (Original.termSecond x h) n)
originalSecondAsActualFiniteSeries x h zero = P.≃-refl
originalSecondAsActualFiniteSeries x h (suc n) =
  P.+-cong
    (originalSecondAsActualFiniteSeries x h n)
    P.≃-refl

originalCoefficientAbsolute :
  (k : Nat) →
  R._≃_
    (R.∣ Original.coefficient k ∣)
    (R._⋆ (Atan.inverseOddRational k))
originalCoefficientAbsolute k =
  P.≃-trans
    (P.∣x*y∣≃∣x∣*∣y∣
      (Sign.alternatingSign k)
      (R._⋆ (Atan.inverseOddRational k)))
    (P.≃-trans
      (P.*-cong
        (Atan.alternatingSignAbsOne k)
        (Atan.embeddedInverseOddAbs k))
      (P.*-identityˡ (R._⋆ (Atan.inverseOddRational k))))

originalSecondTermAbsoluteOdd :
  (x h : R.ℝ) (k : Nat) →
  R._≃_
    (R.∣ Original.termSecond x h k ∣)
    (R._*_
      (R._⋆ (Atan.inverseOddRational k))
      (R.∣ PowerSecond.sourcePowerSecondQuotient
        x h (Estimate.oddExponent k) ∣))
originalSecondTermAbsoluteOdd x h k =
  P.≃-trans
    (P.∣x*y∣≃∣x∣*∣y∣
      (Original.coefficient k)
      (PowerSecond.sourcePowerSecondQuotient
        x h (Estimate.oddExponent k)))
    (P.*-cong
      (originalCoefficientAbsolute k)
      P.≃-refl)

originalSignedFiniteSecondTriangle :
  (x h : R.ℝ) (n : Nat) →
  R._≤_
    (R.∣ Original.finiteSecond x h n ∣)
    (Seq.SeriesOf
      (λ k → R.∣ Original.termSecond x h k ∣) n)
originalSignedFiniteSecondTriangle x h n =
  P.≤-respˡ-≃
    (P.∣-∣-cong
      (originalSecondAsActualFiniteSeries x h n))
    (Triangle.finiteSeriesAbsoluteBound
      (Original.termSecond x h) n)

-- Stronger signed-coefficient readback for the SAME series.
originalSignedFiniteSecondAbsoluteCoefficients :
  (x h : R.ℝ) (n : Nat) →
  R._≃_
    (Seq.SeriesOf
      (λ k → R.∣ Original.termSecond x h k ∣) n)
    (Seq.SeriesOf
      (λ k → R._*_
        (R._⋆ (Atan.inverseOddRational k))
        (R.∣ PowerSecond.sourcePowerSecondQuotient
          x h (Estimate.oddExponent k) ∣)) n)
originalSignedFiniteSecondAbsoluteCoefficients x h zero =
  P.≃-refl
originalSignedFiniteSecondAbsoluteCoefficients x h (suc n) =
  P.+-cong
    (originalSignedFiniteSecondAbsoluteCoefficients x h n)
    (originalSecondTermAbsoluteOdd x h n)
