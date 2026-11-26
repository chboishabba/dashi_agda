module DASHI.Moonshine.JInvariantBishopWeightedCauchyEvaluationExact where

-- SOURCE-WRITTEN, UNCOMPILED. Generalize the existing original
-- sign-twisted finite row theorem to the actual signed radius q.
-- No convergence interchange or independently chosen evaluation.
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (toℕ)
import Data.Fin.Properties as FP
import Data.Nat.Base as N
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _*_)
import RealProperties as P
import Sequence as S
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as C
import DASHI.Foundations.BishopSignTwistedFiniteCauchyCoefficientExact as T
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Analysis.BishopAbsoluteCauchyProductSpecializationExact as Abs
import DASHI.Moonshine.JInvariantBishopEisensteinEulerJetExact as Jet

Series : Set
Series = Nat → ℝ

weighted : ℝ → Series → Series
weighted q f n = R.pow q n * f n

weightedSummand : (q : ℝ) (f g : Series) (n k : Nat) →
  k N.≤ n →
  (weighted q f k * weighted q g (n N.∸ k)) ≃
    (R.pow q n * (f k * g (n N.∸ k)))
weightedSummand q f g n k bound =
  P.≃-trans
    (let open P.ℝ-Solver in
      solve 4 (λ a b c d → (a ⊗ c) ⊗ (b ⊗ d) ⊜
        (a ⊗ b) ⊗ (c ⊗ d)) P.≃-refl
        (R.pow q k) (R.pow q (n N.∸ k)) (f k) (g (n N.∸ k)))
    (P.*-congʳ (P.≃-trans (Jet.powAdd q k (n N.∸ k))
      (P.≃-refl₂ (cong (R.pow q) (T.indexPlusTruncatedComplement n k bound)))))

weightedCauchy : (q : ℝ) (f g : Series) (n : Nat) →
  C.cauchyCoefficient (weighted q f) (weighted q g) n ≃
    weighted q (C.cauchyCoefficient f g) n
weightedCauchy q f g n =
  P.≃-trans (C.BishopSum.sum-cong-≋ (λ i →
    weightedSummand q f g n (toℕ i) (FP.toℕ≤pred[n] i)))
    (P.≃-symm (C.BishopSum.*-distribˡ-sum (R.pow q n)
      (λ i → f (toℕ i) * g (n N.∸ toℕ i))))

weightedProductLimit : (q : ℝ) (f g : Series) (x y : ℝ) →
  (hf : S.SeriesOf_ConvergesAbsolutely (weighted q f)) →
  (hg : S.SeriesOf_ConvergesAbsolutely (weighted q g)) →
  S._ConvergesTo_ (S.SeriesOf (weighted q f)) x →
  S._ConvergesTo_ (S.SeriesOf (weighted q g)) y →
  S._ConvergesTo_ (S.SeriesOf (weighted q (C.cauchyCoefficient f g))) (x * y)
weightedProductLimit q f g x y hf hg fx gy =
  S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n → Ext.seriesPartialSumsCongruent (weightedCauchy q f g) n)
    (x * y , Abs.productConverges (weighted q f) (weighted q g)
      x y hf hg fx gy)

weightedProductAbsolute : (q : ℝ) (f g : Series) →
  S.SeriesOf_ConvergesAbsolutely (weighted q f) →
  S.SeriesOf_ConvergesAbsolutely (weighted q g) →
  S.SeriesOf_ConvergesAbsolutely (weighted q (C.cauchyCoefficient f g))
weightedProductAbsolute q f g hf hg =
  let h = Abs.productAbsolute (weighted q f) (weighted q g) hf hg in
  proj₁ h , S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n → Ext.seriesPartialSumsCongruent (λ k → P.∣-∣-cong (weightedCauchy q f g k)) n)
    h
