module DASHI.Moonshine.JInvariantBishopCompositionLimitExact where

-- SOURCE-WRITTEN, UNCOMPILED. The actual composition is evaluated
-- using two cuts, original weighted powers and literal finite exchange.
-- Absolute convergence is proved separately using a positive triangular
-- majorant, not inferred from the signed limit or from a bounded prefix.
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Nat.Base using (_<_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _*_; ∣_∣)
import RealProperties as P
import Sequence as S
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as O
import DASHI.Analysis.BishopTwoCutDiagonalLimitExact as T
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopWeightedCauchyEvaluationExact as W
import DASHI.Moonshine.JInvariantBishopWeightedPowerLimitExact as V
import DASHI.Moonshine.JInvariantBishopFiniteCompositionExchangeExact as EX
open W using (Series; weighted)

module At (q : ℝ) (c b : Series) (b0 : b zero ≃ R.0ℝ)
  (hb : S.SeriesOf_ConvergesAbsolutely (weighted q b)) where

  B : ℝ
  B = proj₁ hb

  m : Series
  m k = ∣ c k ∣ * R.pow B k

  mNN : (k : Nat) → R.NonNegative (m k)
  mNN k = P.nonNegx,y⇒nonNegx*y (P.nonNeg∣x∣ (c k))
    (S.nonNegx⇒nonNegxⁿ k (V.absNormNN (weighted q b) hb))

  wp : Nat → Series
  wp k = weighted q (H.power b k)

  signedRow positiveRow : T.Rows
  signedRow k n = c k * S.SeriesOf (wp k) n
  positiveRow k n = ∣ c k ∣ * S.SeriesOf (λ j → ∣ wp k j ∣) n

  signedBound : (k n : Nat) → ∣ signedRow k n ∣ ≤ m k
  signedBound k n = P.≤-respˡ-≃
    (P.≃-symm (P.∣x*y∣≃∣x∣*∣y∣ (c k) (S.SeriesOf (wp k) n)))
    (P.*-monoˡ-≤-nonNeg (V.powerPrefixBound q b hb k n) (P.nonNeg∣x∣ (c k)))

  posNN : (k n : Nat) → R.NonNegative (positiveRow k n)
  posNN k n = P.nonNegx,y⇒nonNegx*y (P.nonNeg∣x∣ (c k)) (V.absPrefixNN (wp k) n)

  positiveBound : (k n : Nat) → ∣ positiveRow k n ∣ ≤ m k
  positiveBound k n = P.≤-respˡ-≃
    (P.≃-symm (P.nonNegx⇒∣x∣≃x (posNN k n)))
    (P.*-monoˡ-≤-nonNeg (V.powerPrefixAbsolute q b hb k n) (P.nonNeg∣x∣ (c k)))

  positiveLimit : Series
  positiveLimit k = ∣ c k ∣ * proj₁ (V.powerAbsolute q b hb k)

  positiveLimitNN : (k : Nat) → R.NonNegative (positiveLimit k)
  positiveLimitNN k = P.nonNegx,y⇒nonNegx*y (P.nonNeg∣x∣ (c k))
    (V.absNormNN (wp k) (V.powerAbsolute q b hb k))

  positiveLimitBound : (k : Nat) → ∣ positiveLimit k ∣ ≤ m k
  positiveLimitBound k = P.≤-respˡ-≃
    (P.≃-symm (P.nonNegx⇒∣x∣≃x (positiveLimitNN k)))
    (P.*-monoˡ-≤-nonNeg (V.powerNorm q b hb k) (P.nonNeg∣x∣ (c k)))

  positiveRowLimit : (k : Nat) → S._ConvergesTo_ (positiveRow k) (positiveLimit k)
  positiveRowLimit k = S.xₙyₙ→x₀y₀
    (∣ c k ∣ , S.xₙ≃c⇒xₙ→c (λ n → P.≃-refl)) (V.powerAbsolute q b hb k)

  majorantSummand : Nat → Nat → ℝ
  majorantSummand n k = ∣ c k ∣ * ∣ wp k n ∣

  majorantSummandZero : (n k : Nat) → n < k → majorantSummand n k ≃ R.0ℝ
  majorantSummandZero n k h = P.≃-trans (P.*-congˡ
    (P.≃-trans (P.∣-∣-cong (P.≃-trans
      (P.*-congˡ (H.powerBelow b b0 k n h)) (P.*-zeroʳ (R.pow q n))))
      (P.nonNegx⇒∣x∣≃x P.nonNeg0)))
    (P.*-zeroʳ (∣ c k ∣))

  majorantCoeff : Series
  majorantCoeff n = S.SeriesOf (majorantSummand n) (suc n)

  majorantExchange : (n : Nat) → S.SeriesOf majorantCoeff n ≃ T.diagonal positiveRow n
  majorantExchange n =
    P.≃-trans (EX.triangleExchange majorantSummand n majorantSummandZero)
      (Ext.seriesPartialSumsCongruent (λ k → P.≃-symm
        (EX.scaleSum (∣ c k ∣) (λ j → ∣ wp k j ∣) n)) n)

  coeffBound : (n : Nat) → ∣ weighted q (H.compose c b) n ∣ ≤ majorantCoeff n
  coeffBound n =
    P.≤-respˡ-≃ (P.≃-symm (P.∣-∣-cong (EX.weightedComposeRow q c b n)))
      (P.≤-trans
        (V.signedPrefixAbs (EX.compositionSummand q c b n) (suc n))
        (S.∑₀-mono-≤ (λ k → P.≤-reflexive
          (P.∣x*y∣≃∣x∣*∣y∣ (c k) (wp k n))) (suc n)))

  compositionAbsolute : S._isConvergent (S.SeriesOf m) →
    S.SeriesOf_ConvergesAbsolutely (weighted q (H.compose c b))
  compositionAbsolute hm =
    let hl = S.proposition-3-5 hm (zero , λ k _ → positiveLimitBound k)
        diag = T.diagonalLimit positiveRow positiveLimit m mNN positiveBound
          positiveRowLimit hm hl
        majorantConv : S._isConvergent (S.SeriesOf majorantCoeff)
        majorantConv = proj₁ hl , S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
          (λ n → P.≃-symm (majorantExchange n)) (proj₁ hl , diag)
    in S.proposition-3-5 majorantConv (zero , λ k _ →
      P.≤-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ _)))
        (coeffBound k))

  module Signed (v : ℝ) (hv : S._ConvergesTo_ (S.SeriesOf (weighted q b)) v) where

    l : Series
    l k = c k * R.pow v k

    signedRowLimit : (k : Nat) → S._ConvergesTo_ (signedRow k) (l k)
    signedRowLimit k = S.xₙyₙ→x₀y₀
      (c k , S.xₙ≃c⇒xₙ→c (λ n → P.≃-refl))
      (R.pow v k , V.powerLimit q b v hb hv k)

    signedValueBound : (k : Nat) → ∣ l k ∣ ≤ m k
    signedValueBound k =
      P.≤-respˡ-≃ (P.≃-symm (P.∣x*y∣≃∣x∣*∣y∣ (c k) (R.pow v k)))
        (P.*-monoˡ-≤-nonNeg (V.powerValueBound q b v hb hv k) (P.nonNeg∣x∣ (c k)))

    outerConverges : S._isConvergent (S.SeriesOf m) → S._isConvergent (S.SeriesOf l)
    outerConverges hm = S.proposition-3-5 hm (zero , λ k _ → signedValueBound k)

    -- The caller supplies the ORIGINAL outer evaluation; it is not
    -- replaced by a newly constructed but unconnected real.
    compositionLimit : S._isConvergent (S.SeriesOf m) →
      (L : ℝ) → S._ConvergesTo_ (S.SeriesOf l) L →
      S._ConvergesTo_ (S.SeriesOf (weighted q (H.compose c b))) L
    compositionLimit hm L hL =
      S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
        (λ n → P.≃-symm (EX.weightedCompositionPrefix q c b b0 n))
        (L , T.diagonalLimit signedRow l m mNN signedBound signedRowLimit hm (L , hL))
