module DASHI.Moonshine.JInvariantBishopFiniteCompositionExchangeExact where

-- SOURCE-WRITTEN, UNCOMPILED. Exact finite exchange on the literal
-- composition coefficients already owned by Paper 9. This is the
-- triangle k<=n embedded into a rectangle by zero-support; no
-- infinite Fubini theorem or additional series carrier.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (refl)
open import Data.Fin.Base using (toℕ)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
open import Relation.Nullary.Decidable.Core using (yes; no)
import Real as R
open R using (ℝ; _≃_; _+_; _*_)
import RealProperties as P
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as C
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FS
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H

Series : Set
Series = Nat → ℝ

sum : Series → Nat → ℝ
sum = R.∑₀

sumPrefix : (f g : Series) (n : Nat) →
  (∀ k → k N.< n → f k ≃ g k) → sum f n ≃ sum g n
sumPrefix f g zero h = P.≃-refl
sumPrefix f g (suc n) h =
  P.+-cong (sumPrefix f g n (λ k hk → h k (NP.<-trans hk (NP.n<1+n n))))
    (h n (NP.n<1+n n))

pad : (f : Series) (start end : Nat) → start N.≤ end →
  (∀ k → start N.≤ k → f k ≃ R.0ℝ) →
  sum f end ≃ sum f start
pad f zero zero h hz = P.≃-refl
pad f (suc s) zero () hz
pad f start (suc n) h hz with start NP.≟ suc n
... | yes refl = P.≃-refl
... | no neq =
  let smaller = NP.≤-pred (NP.≤∧≢⇒< h neq) in
  P.≃-trans (P.+-cong (pad f start n smaller hz) (hz n smaller))
    (P.+-identityʳ (sum f start))

scaleSum : (a : ℝ) (f : Series) (n : Nat) →
  a * sum f n ≃ sum (λ k → a * f k) n
scaleSum a f zero = P.*-zeroʳ a
scaleSum a f (suc n) =
  P.≃-trans (P.*-distribˡ-+ a (sum f n) (f n))
    (P.+-cong (scaleSum a f n) P.≃-refl)

-- Reuse stdlib rectangular Fin-sum exchange and the actual Bishop
-- finite-sum bridge; the two natural-index prefix counts are literal.
rectangleExchange : (f : Nat → Nat → ℝ) (m n : Nat) →
  sum (λ i → sum (f i) n) m ≃ sum (λ j → sum (λ i → f i j) m) n
rectangleExchange f m n =
  P.≃-trans (P.≃-symm (FS.finSumIsSeriesOf (λ i → sum (f i) n) m))
    (P.≃-trans (C.BishopSum.sum-cong-≋ (λ i →
      P.≃-symm (FS.finSumIsSeriesOf (f (toℕ i)) n)))
      (P.≃-trans (C.BishopSum.∑-comm (λ i j → f (toℕ i) (toℕ j)))
        (P.≃-trans (C.BishopSum.sum-cong-≋ (λ j →
          FS.finSumIsSeriesOf (λ i → f i (toℕ j)) m))
          (FS.finSumIsSeriesOf (λ j → sum (λ i → f i j) m) n))))

triangleExchange : (f : Nat → Nat → ℝ) (n : Nat) →
  (∀ i j → i N.< j → f i j ≃ R.0ℝ) →
  sum (λ i → sum (f i) (suc i)) n ≃ sum (λ j → sum (λ i → f i j) n) n
triangleExchange f n zeroAbove =
  P.≃-trans
    (sumPrefix (λ i → sum (f i) (suc i)) (λ i → sum (f i) n) n
      (λ i hi → P.≃-symm (pad (f i) (suc i) n hi (λ j hj → zeroAbove i j hj))))
    (rectangleExchange f n n)

weightedPower : ℝ → Series → Nat → Series
weightedPower q inner k n = R.pow q n * H.power inner k n

compositionSummand : ℝ → Series → Series → Nat → Nat → ℝ
compositionSummand q outer inner n k = outer k * weightedPower q inner k n

compositionSummandZero : (q : ℝ) (outer inner : Series) →
  inner zero ≃ R.0ℝ → (n k : Nat) → n N.< k →
  compositionSummand q outer inner n k ≃ R.0ℝ
compositionSummandZero q outer inner hz n k h =
  P.≃-trans (P.*-congˡ (P.≃-trans
    (P.*-congˡ (H.powerBelow inner hz k n h)) (P.*-zeroʳ (R.pow q n))))
    (P.*-zeroʳ (outer k))

weightedComposeRow : (q : ℝ) (outer inner : Series) (n : Nat) →
  R.pow q n * H.compose outer inner n ≃
    sum (compositionSummand q outer inner n) (suc n)
weightedComposeRow q outer inner n =
  P.≃-trans (scaleSum (R.pow q n) (λ k → outer k * H.power inner k n) (suc n))
    (Ext.finiteSumCongruent (λ k →
      let open P.ℝ-Solver in
      solve 3 (λ q a p → q ⊗ (a ⊗ p) ⊜ a ⊗ (q ⊗ p))
        P.≃-refl (R.pow q n) (outer k) (H.power inner k n)) (suc n))

-- The exact prefix of the ORIGINAL composition equals the sum of
-- truncated evaluated powers, including k=0 and the signed q phase.
weightedCompositionPrefix : (q : ℝ) (outer inner : Series) →
  inner zero ≃ R.0ℝ → (n : Nat) →
  sum (λ j → R.pow q j * H.compose outer inner j) n ≃
  sum (λ k → outer k * sum (weightedPower q inner k) n) n
weightedCompositionPrefix q outer inner hz n =
  P.≃-trans (Ext.finiteSumCongruent (weightedComposeRow q outer inner) n)
    (P.≃-trans (triangleExchange (compositionSummand q outer inner) n
      (compositionSummandZero q outer inner hz))
      (Ext.finiteSumCongruent (λ k → P.≃-symm
        (scaleSum (outer k) (weightedPower q inner k) n)) n))
