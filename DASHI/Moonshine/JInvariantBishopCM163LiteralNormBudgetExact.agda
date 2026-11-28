module DASHI.Moonshine.JInvariantBishopCM163LiteralNormBudgetExact where

-- SOURCE-WRITTEN, UNCOMPILED. Actual l1 witnesses, not scalar-only
-- budgets. Reuse the same weighted product and original tail norms.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _*_; _+_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as S
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopWeightedCauchyEvaluationExact as W
import DASHI.Moonshine.JInvariantBishopWeightedPowerLimitExact as Power
import DASHI.Moonshine.JInvariantBishopCM163FormalEvaluationConsumerExact as V
import DASHI.Moonshine.JInvariantBishopCM163LiteralRealSliceEvaluationExact as Slice
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Guard
open G
open V using (q; Abs)

normCong : {f g : Series} → f ≈s g → Abs f → Abs g
normCong h (L , p) = L , S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
  (λ n {{_}} → Ext.seriesPartialSumsCongruent
    (λ k → P.∣-∣-cong (P.*-congˡ (h k))) n) (L , p)

record Bounded (f : Series) (b : ℝ) : Set where
  constructor bounded
  field
    witness : Abs f
    bound : proj₁ witness ≤ b
open Bounded public

boundNN : {f : Series} {b : ℝ} → Bounded f b → R.NonNegative b
boundNN {f} h = P.0≤x⇒nonNegx (P.≤-trans
  (P.nonNegx⇒0≤x (Power.absNormNN (W.weighted q f) (witness h))) (bound h))

transport : {f g : Series} {b c : ℝ} →
  f ≈s g → b ≃ c → Bounded f b → Bounded g c
transport h e p = bounded (normCong h (witness p)) (P.≤-respʳ-≃ e (bound p))

sumAdd : (a b : Series) (n : Nat) →
  S.SeriesOf (a ⊕s b) n ≃ S.SeriesOf a n + S.SeriesOf b n
sumAdd a b zero = P.≃-symm (P.+-identityʳ R.0ℝ)
sumAdd a b (suc n) =
  P.≃-trans (P.+-cong (sumAdd a b n) P.≃-refl)
    (let open P.ℝ-Solver in
      solve 4 (λ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ⊜ (a ⊕ c) ⊕ (b ⊕ d))
        P.≃-refl (S.SeriesOf a n) (S.SeriesOf b n) (a n) (b n))

sumConv : (a b : Series) → S._isConvergent (S.SeriesOf a) →
  S._isConvergent (S.SeriesOf b) → S._isConvergent (S.SeriesOf (a ⊕s b))
sumConv a b ha hb = proj₁ ha + proj₁ hb , S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
  (λ n {{_}} → P.≃-symm (sumAdd a b n))
  (proj₁ ha + proj₁ hb , S.xₙ+yₙ→x₀+y₀ ha hb)

addTermBound : (f g : Series) (n : Nat) →
  ∣ W.weighted q (f ⊕s g) n ∣ ≤ ∣ W.weighted q f n ∣ + ∣ W.weighted q g n ∣
addTermBound f g n =
  P.≤-respˡ-≃ (P.≃-symm (P.∣-∣-cong
    (P.*-distribˡ-+ (R.pow q n) (f n) (g n))))
    (P.∣x+y∣≤∣x∣+∣y∣ (W.weighted q f n) (W.weighted q g n))

addAbs : (f g : Series) → Abs f → Abs g → Abs (f ⊕s g)
addAbs f g hf hg = S.proposition-3-5
  (sumConv (λ n → ∣ W.weighted q f n ∣) (λ n → ∣ W.weighted q g n ∣) hf hg)
  (zero , λ n _ → P.≤-respˡ-≃
    (P.≃-symm (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ _))) (addTermBound f g n))

addBound : {f g : Series} {a b : ℝ} → Bounded f a → Bounded g b →
  Bounded (f ⊕s g) (a + b)
addBound {f} {g} p t =
  let h = addAbs f g (witness p) (witness t)
      m = sumConv (λ n → ∣ W.weighted q f n ∣) (λ n → ∣ W.weighted q g n ∣)
        (witness p) (witness t)
  in bounded h (P.≤-trans (S.xₙ≤yₙ⇒limxₙ≤limyₙ
    (S.∑₀-mono-≤ (addTermBound f g)) h m) (P.+-mono-≤ (bound p) (bound t)))

mulBound : {f g : Series} {a b : ℝ} → Bounded f a → Bounded g b →
  Bounded (f ⊗s g) (a * b)
mulBound {f} {g} p t = bounded
  (W.weightedProductAbsolute q f g (witness p) (witness t))
  (P.≤-trans (Power.weightedNormProduct q f g (witness p) (witness t))
    (P.≤-trans (P.*-monoʳ-≤-nonNeg (bound p) (Power.absNormNN (W.weighted q g) (witness t)))
      (P.*-monoˡ-≤-nonNeg (bound t) (boundNN p))))

negAbsTerm : (f : Series) (n : Nat) → ∣ W.weighted q (G.neg f) n ∣ ≃ ∣ W.weighted q f n ∣
negAbsTerm f n = P.≃-trans (P.∣-∣-cong
  (let open P.ℝ-Solver in solve 2 (λ a b → a ⊗ (⊝ b) ⊜ ⊝ (a ⊗ b))
    P.≃-refl (R.pow q n) (f n))) P.∣-x∣≃∣x∣

negBound : {f : Series} {a : ℝ} → Bounded f a → Bounded (G.neg f) a
negBound {f} h = bounded
  (proj₁ (witness h) , S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n {{_}} → Ext.seriesPartialSumsCongruent (λ k → P.≃-symm (negAbsTerm f k)) n)
    (witness h)) (bound h)

a b T discBudget : ℝ
a = (+ 1 / 25) ⋆
b = (+ 2 / 25) ⋆
T = (+ 1951 / 15625) ⋆
discBudget = (+ 4551 / 15625) ⋆

tx ty : Series
tx = U.X ⊖s H.unitSeries
ty = U.Y ⊖s H.unitSeries

txB : Bounded tx a
txB = bounded Slice.xTailNorm (P.<⇒≤ Guard.l1XSmall)
tyB : Bounded ty b
tyB = bounded Slice.yTailNorm (P.<⇒≤ Guard.l1YSmall)

triple : Series → Series
triple f = f ⊕s f ⊕s f

cubeTail : Series → Series
cubeTail f = triple f ⊕s triple (f ⊗s f) ⊕s ((f ⊗s f) ⊗s f)

squareTail : Series → Series
squareTail f = f ⊕s f ⊕s (f ⊗s f)

cubeTailBound : Bounded (cubeTail tx) T
cubeTailBound = transport reflS
  (let open P.ℝ-Solver in solve 0
    (Κ (+ 1 / 25) ⊕ Κ (+ 1 / 25) ⊕ Κ (+ 1 / 25) ⊕
      (Κ (+ 1 / 25) ⊗ Κ (+ 1 / 25) ⊕ Κ (+ 1 / 25) ⊗ Κ (+ 1 / 25) ⊕
       Κ (+ 1 / 25) ⊗ Κ (+ 1 / 25)) ⊕
      (Κ (+ 1 / 25) ⊗ Κ (+ 1 / 25)) ⊗ Κ (+ 1 / 25)
      ⊜ Κ (+ 1951 / 15625)) P.≃-refl)
  (addBound (addBound (addBound (addBound txB txB) txB)
    (addBound (addBound (mulBound txB txB) (mulBound txB txB)) (mulBound txB txB)))
    (mulBound (mulBound txB txB) txB))

cubeTailMeaning : cubeTail tx ≈s (U.X3 ⊖s H.unitSeries)
cubeTailMeaning = let open G.Solver in
  solve 1 (λ x →
    ((x ⊖ Κ 1ℚᵘ) ⊕ (x ⊖ Κ 1ℚᵘ) ⊕ (x ⊖ Κ 1ℚᵘ)) ⊕
    (((x ⊖ Κ 1ℚᵘ) ⊗ (x ⊖ Κ 1ℚᵘ)) ⊕ ((x ⊖ Κ 1ℚᵘ) ⊗ (x ⊖ Κ 1ℚᵘ)) ⊕
      ((x ⊖ Κ 1ℚᵘ) ⊗ (x ⊖ Κ 1ℚᵘ))) ⊕
    (((x ⊖ Κ 1ℚᵘ) ⊗ (x ⊖ Κ 1ℚᵘ)) ⊗ (x ⊖ Κ 1ℚᵘ))
    ⊜ (x ⊗ x) ⊗ x ⊖ Κ 1ℚᵘ) reflS U.X

squareTailMeaning : squareTail ty ≈s (U.Y2 ⊖s H.unitSeries)
squareTailMeaning = let open G.Solver in
  solve 1 (λ y → (y ⊖ Κ 1ℚᵘ) ⊕ (y ⊖ Κ 1ℚᵘ) ⊕
    ((y ⊖ Κ 1ℚᵘ) ⊗ (y ⊖ Κ 1ℚᵘ)) ⊜ y ⊗ y ⊖ Κ 1ℚᵘ) reflS U.Y

minusCubeMeaning : G.neg (cubeTail tx) ≈s H.minusX3Tail
minusCubeMeaning n = P.≃-trans (P.-‿cong (cubeTailMeaning n))
  (let open P.ℝ-Solver in solve 1 (λ a → (⊝ a) ⊜ (⊝ Κ 1ℚᵘ) ⊗ a)
    P.≃-refl ((U.X3 ⊖s H.unitSeries) n))

innerBound : Bounded H.minusX3Tail T
innerBound = transport minusCubeMeaning P.≃-refl (negBound cubeTailBound)

discMeaning : (cubeTail tx ⊕s G.neg (squareTail ty)) ≈s U.disc
discMeaning = transS (addCong cubeTailMeaning (negCong squareTailMeaning))
  (let open G.Solver in solve 2 (λ x y →
    (x ⊖ Κ 1ℚᵘ) ⊕ (⊝ (y ⊖ Κ 1ℚᵘ)) ⊜ x ⊖ y) reflS U.X3 U.Y2)

discBound : Bounded U.disc discBudget
discBound = transport discMeaning
  (let open P.ℝ-Solver in solve 0
    (Κ (+ 1951 / 15625) ⊕ (Κ (+ 2 / 25) ⊕ Κ (+ 2 / 25) ⊕
      Κ (+ 2 / 25) ⊗ Κ (+ 2 / 25)) ⊜ Κ (+ 4551 / 15625)) P.≃-refl)
  (addBound cubeTailBound (negBound (addBound (addBound tyB tyB) (mulBound tyB tyB))))
