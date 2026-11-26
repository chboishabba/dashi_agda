module DASHI.Moonshine.JInvariantBishopWeightedPowerLimitExact where

-- SOURCE-WRITTEN, UNCOMPILED. Reuse the original Cauchy product,
-- weighted evaluation and positive prefix order. No new series carrier.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
import Real as R
open R using (ℝ; _≃_; _≤_; _*_; _+_; ∣_∣)
import RealProperties as P
import Sequence as S
import DASHI.Analysis.BishopAbsoluteCauchyProductSpecializationExact as A
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as O
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopWeightedCauchyEvaluationExact as W
open W using (Series; weighted)

oneNN : R.NonNegative R.1ℝ
oneNN = P.pos⇒nonNeg (P.posp⇒posp⋆ 1ℚᵘ (QP.positive⁻¹ 1ℚᵘ))

unitPartial : (n : Nat) → S.SeriesOf H.unitSeries (suc n) ≃ R.1ℝ
unitPartial zero = P.+-identityˡ R.1ℝ
unitPartial (suc n) =
  P.≃-trans (P.+-identityʳ (S.SeriesOf H.unitSeries (suc n))) (unitPartial n)

weightedUnit : (q : ℝ) (n : Nat) → weighted q H.unitSeries n ≃ H.unitSeries n
weightedUnit q zero = P.*-identityˡ R.1ℝ
weightedUnit q (suc n) = P.*-zeroʳ (R.pow q (suc n))

unitAbs : (n : Nat) → ∣ H.unitSeries n ∣ ≃ H.unitSeries n
unitAbs zero = P.nonNegx⇒∣x∣≃x oneNN
unitAbs (suc n) = P.nonNegx⇒∣x∣≃x P.nonNeg0

weightedUnitAbsolute : (q : ℝ) → S.SeriesOf_ConvergesAbsolutely (weighted q H.unitSeries)
weightedUnitAbsolute q = R.1ℝ , S.xₙ≃c⇒xₙ→c
  (λ { (suc n) → P.≃-trans
    (Ext.seriesPartialSumsCongruent
      (λ k → P.≃-trans (P.∣-∣-cong (weightedUnit q k)) (unitAbs k)) (suc n))
    (unitPartial n) })

weightedUnitLimit : (q : ℝ) → S._ConvergesTo_ (S.SeriesOf (weighted q H.unitSeries)) R.1ℝ
weightedUnitLimit q = S.xₙ≃c⇒xₙ→c
  (λ { (suc n) → P.≃-trans
    (Ext.seriesPartialSumsCongruent (weightedUnit q) (suc n)) (unitPartial n) })

powerAbsolute : (q : ℝ) (b : Series) →
  S.SeriesOf_ConvergesAbsolutely (weighted q b) →
  (k : Nat) → S.SeriesOf_ConvergesAbsolutely (weighted q (H.power b k))
powerAbsolute q b hb zero = weightedUnitAbsolute q
powerAbsolute q b hb (suc k) =
  W.weightedProductAbsolute q b (H.power b k) hb (powerAbsolute q b hb k)

powerLimit : (q : ℝ) (b : Series) (v : ℝ) →
  (hb : S.SeriesOf_ConvergesAbsolutely (weighted q b)) →
  S._ConvergesTo_ (S.SeriesOf (weighted q b)) v →
  (k : Nat) → S._ConvergesTo_ (S.SeriesOf (weighted q (H.power b k))) (R.pow v k)
powerLimit q b v hb hv zero = weightedUnitLimit q
powerLimit q b v hb hv (suc k) =
  S.xₙ→x∧x≃y⇒xₙ→y
    (W.weightedProductLimit q b (H.power b k) v (R.pow v k)
      hb (powerAbsolute q b hb k) hv (powerLimit q b v hb hv k))
    (P.*-comm v (R.pow v k))

absPrefixNN : (u : Series) (n : Nat) →
  R.NonNegative (S.SeriesOf (λ j → ∣ u j ∣) n)
absPrefixNN u = O.finiteSumNonnegative (λ j → P.nonNeg∣x∣ (u j))

absNormNN : (u : Series) (h : S.SeriesOf_ConvergesAbsolutely u) →
  R.NonNegative (proj₁ h)
absNormNN u h = P.0≤x⇒nonNegx
  (S.0≤xₙ⇒0≤limxₙ (λ n → P.nonNegx⇒0≤x (absPrefixNN u n)) h)

absPrefixBound : (u : Series) (h : S.SeriesOf_ConvergesAbsolutely u) →
  (n : Nat) → S.SeriesOf (λ j → ∣ u j ∣) n ≤ proj₁ h
absPrefixBound u h n =
  S.xₙisIncreasing⇒xₙ≤limxₙ
    (O.partialSumsIncreasing (λ j → P.nonNeg∣x∣ (u j))) h n

weightedNormProduct : (q : ℝ) (b c : Series) →
  (hb : S.SeriesOf_ConvergesAbsolutely (weighted q b)) →
  (hc : S.SeriesOf_ConvergesAbsolutely (weighted q c)) →
  proj₁ (W.weightedProductAbsolute q b c hb hc) ≤ proj₁ hb * proj₁ hc
weightedNormProduct q b c hb hc =
  A.normSubmultiplicative (weighted q b) (weighted q c) hb hc

powerNorm : (q : ℝ) (b : Series) →
  (hb : S.SeriesOf_ConvergesAbsolutely (weighted q b)) →
  (k : Nat) → proj₁ (powerAbsolute q b hb k) ≤ R.pow (proj₁ hb) k
powerNorm q b hb zero = P.≤-refl
powerNorm q b hb (suc k) =
  P.≤-respʳ-≃ (P.*-comm (proj₁ hb) (R.pow (proj₁ hb) k))
    (P.≤-trans (weightedNormProduct q b (H.power b k) hb (powerAbsolute q b hb k))
      (P.*-monoˡ-≤-nonNeg (powerNorm q b hb k) (absNormNN (weighted q b) hb)))

powerPrefixAbsolute : (q : ℝ) (b : Series) →
  (hb : S.SeriesOf_ConvergesAbsolutely (weighted q b)) →
  (k n : Nat) → S.SeriesOf (λ j → ∣ weighted q (H.power b k) j ∣) n ≤ R.pow (proj₁ hb) k
powerPrefixAbsolute q b hb k n =
  P.≤-trans (absPrefixBound (weighted q (H.power b k)) (powerAbsolute q b hb k) n)
    (powerNorm q b hb k)

signedPrefixAbs : (u : Series) (n : Nat) →
  ∣ S.SeriesOf u n ∣ ≤ S.SeriesOf (λ j → ∣ u j ∣) n
signedPrefixAbs u zero = P.≤-reflexive (P.nonNegx⇒∣x∣≃x P.nonNeg0)
signedPrefixAbs u (suc n) = P.≤-trans
  (P.∣x+y∣≤∣x∣+∣y∣ (S.SeriesOf u n) (u n))
  (P.+-mono-≤ (signedPrefixAbs u n) P.≤-refl)

powerPrefixBound : (q : ℝ) (b : Series) →
  (hb : S.SeriesOf_ConvergesAbsolutely (weighted q b)) →
  (k n : Nat) → ∣ S.SeriesOf (weighted q (H.power b k)) n ∣ ≤ R.pow (proj₁ hb) k
powerPrefixBound q b hb k n =
  P.≤-trans (signedPrefixAbs (weighted q (H.power b k)) n)
    (powerPrefixAbsolute q b hb k n)

powerValueBound : (q : ℝ) (b : Series) (v : ℝ) →
  (hb : S.SeriesOf_ConvergesAbsolutely (weighted q b)) →
  S._ConvergesTo_ (S.SeriesOf (weighted q b)) v →
  (k : Nat) → ∣ R.pow v k ∣ ≤ R.pow (proj₁ hb) k
powerValueBound q b v hb hv k =
  S.xₙ≤y⇒limxₙ≤y (powerPrefixBound q b hb k)
    (∣ R.pow v k ∣ , S.∣xₙ∣→∣x₀∣ (R.pow v k , powerLimit q b v hb hv k))
