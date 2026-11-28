module DASHI.Foundations.BishopFiniteCauchyRingWeldExact where

-- SOURCE-WRITTEN, UNCOMPILED.
-- Original finite Cauchy row, no second polynomial/series carrier.
-- Reflection i ↦ n-i, and the disjoint simplex decomposition
-- i=0 versus i>0, give all-degree multiplication laws.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; toℕ; opposite)
import Data.Fin.Properties as FP
import Data.Fin.Permutation as Perm
import Data.Nat.Base as N
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Real as R
open R using (ℝ; _≃_; _+_; _*_)
import RealProperties as P
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as C
import DASHI.Foundations.BishopSignTwistedFiniteCauchyCoefficientExact as T

Series : Set
Series = Nat → ℝ

infixl 6 _⊕_
infixl 7 _⊗_
_⊕_ _⊗_ : Series → Series → Series
(f ⊕ g) n = f n + g n
_⊗_ = C.cauchyCoefficient

scale : ℝ → Series → Series
scale c f n = c * f n

zeroSeries unitSeries : Series
zeroSeries n = R.0ℝ
unitSeries zero = R.1ℝ
unitSeries (suc n) = R.0ℝ

rowCong : (f g u v : Series) →
  (∀ n → f n ≃ u n) → (∀ n → g n ≃ v n) →
  ∀ n → (f ⊗ g) n ≃ (u ⊗ v) n
rowCong = T.rowCauchyCoefficientRespectsTerms

commSummand : (f g : Series) (n : Nat) (i : Fin (suc n)) →
  (f (toℕ (opposite i)) * g (n N.∸ toℕ (opposite i))) ≃
    (g (toℕ i) * f (n N.∸ toℕ i))
commSummand f g n i =
  P.≃-trans
    (P.*-cong
      (P.≃-refl₂ (cong f (FP.opposite-prop i)))
      (P.≃-refl₂ (cong g
        (trans (cong (n N.∸_) (FP.opposite-prop i))
          (NP.m∸[m∸n]≡n (FP.toℕ≤pred[n] i))))))
    (P.*-comm (f (n N.∸ toℕ i)) (g (toℕ i)))

rowComm : (f g : Series) (n : Nat) → (f ⊗ g) n ≃ (g ⊗ f) n
rowComm f g n =
  P.≃-trans
    (C.BishopSum.sum-permute
      (λ i → f (toℕ i) * g (n N.∸ toℕ i)) Perm.reverse)
    (C.BishopSum.sum-cong-≋ (commSummand f g n))

rowAddLeft : (f g h : Series) (n : Nat) →
  ((f ⊕ g) ⊗ h) n ≃ ((f ⊗ h) ⊕ (g ⊗ h)) n
rowAddLeft f g h n =
  P.≃-trans
    (C.BishopSum.sum-cong-≋ (λ i →
      P.*-distribʳ-+ (h (n N.∸ toℕ i)) (f (toℕ i)) (g (toℕ i))))
    (C.BishopSum.∑-distrib-+
      (λ i → f (toℕ i) * h (n N.∸ toℕ i))
      (λ i → g (toℕ i) * h (n N.∸ toℕ i)))

rowAddRight : (f g h : Series) (n : Nat) →
  (f ⊗ (g ⊕ h)) n ≃ ((f ⊗ g) ⊕ (f ⊗ h)) n
rowAddRight f g h n =
  P.≃-trans (rowComm f (g ⊕ h) n)
    (P.≃-trans (rowAddLeft g h f n)
      (P.+-cong (rowComm g f n) (rowComm h f n)))

rowScaleLeft : (a : ℝ) (f g : Series) (n : Nat) →
  (scale a f ⊗ g) n ≃ scale a (f ⊗ g) n
rowScaleLeft a f g n =
  P.≃-trans
    (C.BishopSum.sum-cong-≋ (λ i →
      P.*-assoc a (f (toℕ i)) (g (n N.∸ toℕ i))))
    (P.≃-symm (C.BishopSum.*-distribˡ-sum a
      (λ i → f (toℕ i) * g (n N.∸ toℕ i))))

rowScaleRight : (a : ℝ) (f g : Series) (n : Nat) →
  (f ⊗ scale a g) n ≃ scale a (f ⊗ g) n
rowScaleRight a f g n = P.≃-trans (rowComm f (scale a g) n)
  (P.≃-trans (rowScaleLeft a g f n)
    (P.*-congˡ (rowComm g f n)))

rowZeroLeft : (f : Series) (n : Nat) → (zeroSeries ⊗ f) n ≃ R.0ℝ
rowZeroLeft f zero = P.≃-trans (C.cauchyCoefficientZero zeroSeries f)
  (P.*-zeroˡ (f zero))
rowZeroLeft f (suc n) =
  P.≃-trans (C.cauchyCoefficientSuccessor zeroSeries f n)
    (P.≃-trans (P.+-cong (P.*-zeroˡ (f (suc n))) (rowZeroLeft f n))
      (P.+-identityʳ R.0ℝ))

rowUnitLeft : (f : Series) (n : Nat) → (unitSeries ⊗ f) n ≃ f n
rowUnitLeft f zero = P.≃-trans (C.cauchyCoefficientZero unitSeries f)
  (P.*-identityˡ (f zero))
rowUnitLeft f (suc n) =
  P.≃-trans (C.cauchyCoefficientSuccessor unitSeries f n)
    (P.≃-trans (P.+-cong (P.*-identityˡ (f (suc n))) (rowZeroLeft f n))
      (P.+-identityʳ (f (suc n))))

rowUnitRight : (f : Series) (n : Nat) → (f ⊗ unitSeries) n ≃ f n
rowUnitRight f n = P.≃-trans (rowComm f unitSeries n) (rowUnitLeft f n)

-- Head split of the inner row; the degree-n tail reindexes the
-- i>0 simplex via i↦i-1, without any truncated subtraction outside
-- the finite row. Recursion below is solely on the degree.
shiftRow : (f g : Series) (n : Nat) →
  C.shift (f ⊗ g) n ≃ (scale (f zero) (C.shift g) ⊕ (C.shift f ⊗ g)) n
shiftRow = C.cauchyCoefficientSuccessor

rowAssoc : (f g h : Series) (n : Nat) →
  ((f ⊗ g) ⊗ h) n ≃ (f ⊗ (g ⊗ h)) n
rowAssoc f g h zero =
  P.≃-trans (C.cauchyCoefficientZero (f ⊗ g) h)
    (P.≃-trans (P.*-congʳ (C.cauchyCoefficientZero f g))
      (P.≃-trans (P.*-assoc (f zero) (g zero) (h zero))
        (P.≃-trans (P.*-congˡ (P.≃-symm (C.cauchyCoefficientZero g h)))
          (P.≃-symm (C.cauchyCoefficientZero f (g ⊗ h))))))
rowAssoc f g h (suc n) =
  let
    a = f zero
    b = g zero
    c = h (suc n)
    u = (C.shift g ⊗ h) n
    v = (C.shift f ⊗ (g ⊗ h)) n
    tail : (C.shift (f ⊗ g) ⊗ h) n ≃ (a * u + v)
    tail = P.≃-trans
      (rowCong (C.shift (f ⊗ g)) h
        (scale a (C.shift g) ⊕ (C.shift f ⊗ g)) h
        (shiftRow f g) (λ _ → P.≃-refl) n)
      (P.≃-trans (rowAddLeft (scale a (C.shift g)) (C.shift f ⊗ g) h n)
        (P.+-cong (rowScaleLeft a (C.shift g) h n) (rowAssoc (C.shift f) g h n)))
    regroup : (a * b) * c + (a * u + v) ≃ a * (b * c + u) + v
    regroup = P.ℝ-Solver.solve 5 (λ a b c u v →
      let open P.ℝ-Solver using (_⊜_) renaming (_⊗_ to _∙_; _⊕_ to _⊞_) in
      (a ∙ b) ∙ c ⊞ (a ∙ u ⊞ v) ⊜ a ∙ (b ∙ c ⊞ u) ⊞ v)
      P.≃-refl a b c u v
  in
  P.≃-trans (C.cauchyCoefficientSuccessor (f ⊗ g) h n)
    (P.≃-trans (P.+-cong (P.*-congʳ (C.cauchyCoefficientZero f g)) tail)
      (P.≃-trans regroup
        (P.≃-trans
          (P.+-cong (P.*-congˡ (P.≃-symm (C.cauchyCoefficientSuccessor g h n)))
            P.≃-refl)
          (P.≃-symm (C.cauchyCoefficientSuccessor f (g ⊗ h) n)))))
