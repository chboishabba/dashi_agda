module DASHI.Analysis.BishopAbsoluteCauchyProductSpecializationExact where

-- SOURCE-WRITTEN, UNCOMPILED.
-- Specialize the already-owned positive and signed triangle theorems
-- (as in BishopNativeComplexRectangleExact) to two arbitrary actual
-- absolutely convergent real streams. No new convergence authority.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _*_)
import RealProperties as P
import Sequence as S
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Foundations.BishopFiniteCauchyWingAbsoluteBoundExact as Wing
import DASHI.Analysis.BishopPositiveCauchyTriangleFromAbsoluteSeriesExact as Positive
import DASHI.Analysis.BishopGenericCauchyFromAbsoluteTriangleExact as Signed

Terms : Set
Terms = Nat → ℝ

abs : Terms → Terms
abs = Wing.absoluteTerms

conv : Terms → Terms → Terms
conv = Row.cauchyCoefficient

norm : (f : Terms) → S.SeriesOf_ConvergesAbsolutely f → ℝ
norm f h = proj₁ h

-- The actual absolute triangular history converges by the existing
-- positive rectangle/triangle squeeze. No extra caller-supplied limit.
absoluteTriangleConverges : (f g : Terms) →
  (hf : S.SeriesOf_ConvergesAbsolutely f) →
  (hg : S.SeriesOf_ConvergesAbsolutely g) →
  S._ConvergesTo_ (Signed.absoluteTriangle f g) (norm f hf * norm g hg)
absoluteTriangleConverges f g hf hg =
  Positive.positiveCauchyTriangleConverges (abs f) (abs g)
    (λ n → P.nonNeg∣x∣ (f n)) (λ n → P.nonNeg∣x∣ (g n)) hf hg

absoluteRowConverges : (f g : Terms) →
  (hf : S.SeriesOf_ConvergesAbsolutely f) →
  (hg : S.SeriesOf_ConvergesAbsolutely g) →
  S._ConvergesTo_ (S.SeriesOf (conv (abs f) (abs g))) (norm f hf * norm g hg)
absoluteRowConverges f g hf hg =
  S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n → FinSum.finSumIsSeriesOf (conv (abs f) (abs g)) n)
    (norm f hf * norm g hg , absoluteTriangleConverges f g hf hg)

-- Pointwise absolute domination, directly on the same finite Cauchy
-- row head recurrence. This is independent of evaluation radius.
rowBound : (f g : Terms) (n : Nat) →
  R.∣ conv f g n ∣ ≤ conv (abs f) (abs g) n
rowBound f g zero =
  P.≤-reflexive
    (P.≃-trans (P.∣-∣-cong (Row.cauchyCoefficientZero f g))
      (P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ (f zero) (g zero))
        (P.≃-symm (Row.cauchyCoefficientZero (abs f) (abs g)))))
rowBound f g (suc n) =
  P.≤-respʳ-≃ (P.≃-symm (Row.cauchyCoefficientSuccessor (abs f) (abs g) n))
    (P.≤-respˡ-≃ (P.≃-symm (P.∣-∣-cong (Row.cauchyCoefficientSuccessor f g n)))
      (P.≤-trans
        (P.∣x+y∣≤∣x∣+∣y∣ (f zero * g (suc n)) (conv (Row.shift f) g n))
        (P.+-mono-≤
          (P.≤-reflexive (P.∣x*y∣≃∣x∣*∣y∣ (f zero) (g (suc n))))
          (rowBound (Row.shift f) g n))))

-- Native comparison theorem, not a finite cutoff or a classical
-- complete-Banach-algebra assumption.
productAbsolute : (f g : Terms) →
  S.SeriesOf_ConvergesAbsolutely f → S.SeriesOf_ConvergesAbsolutely g →
  S.SeriesOf_ConvergesAbsolutely (conv f g)
productAbsolute f g hf hg =
  S.proposition-3-5
    (norm f hf * norm g hg , absoluteRowConverges f g hf hg)
    (zero , λ n _ →
      P.≤-respˡ-≃
        (P.≃-symm (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ (conv f g n))))
        (rowBound f g n))

normSubmultiplicative : (f g : Terms) →
  (hf : S.SeriesOf_ConvergesAbsolutely f) →
  (hg : S.SeriesOf_ConvergesAbsolutely g) →
  norm (conv f g) (productAbsolute f g hf hg) ≤ norm f hf * norm g hg
normSubmultiplicative f g hf hg =
  S.xₙ≤yₙ⇒limxₙ≤limyₙ
    (S.∑₀-mono-≤ (rowBound f g))
    (productAbsolute f g hf hg)
    (norm f hf * norm g hg , absoluteRowConverges f g hf hg)

-- Signed Cauchy evaluation. The limit names are the actual input
-- series limits, not newly chosen equivalent values.
productConverges : (f g : Terms) (x y : ℝ) →
  (hf : S.SeriesOf_ConvergesAbsolutely f) →
  (hg : S.SeriesOf_ConvergesAbsolutely g) →
  S._ConvergesTo_ (S.SeriesOf f) x →
  S._ConvergesTo_ (S.SeriesOf g) y →
  S._ConvergesTo_ (S.SeriesOf (conv f g)) (x * y)
productConverges f g x y hf hg fx gy =
  S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n → FinSum.finSumIsSeriesOf (conv f g) n)
    (x * y , Signed.cauchyTriangleConvergesToActualProduct
      f g x y (norm f hf * norm g hg) fx gy
      (absoluteTriangleConverges f g hf hg))
