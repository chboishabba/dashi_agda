module DASHI.Moonshine.JInvariantBishopLambertDegreeFibreExact where

-- SOURCE-WRITTEN, UNCOMPILED. Classical Lambert degree fibre m*d=r.
-- The actual positive factor-pair scanner, not an alternative divisor sum.
-- This pays finite Fourier regrouping only, not the horizontal row identity.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (sym; cong; trans)

import Data.Nat.Properties as NP
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as Q
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as F
import DASHI.Mathematics.NumberTheory.FiniteFactorPairPowerReadoutExact as Read
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Pow
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E

open C using (BishopComplex; _≈C_)
open A using (_+C_; scaleC; powC)

realEq : ∀ {x y : R.ℝ} → x ≡ y → R._≃_ x y
realEq refl = P.≃-refl

natAdd : ∀ a b → R._≃_ (N.natReal (a + b))
  (R._+_ (N.natReal a) (N.natReal b))
natAdd a b = P.≃-trans (P.⋆-cong (Q.natAsRationalAdd a b))
  (P.⋆-distrib-+ (Q.natAsRational a) (Q.natAsRational b))

foldR : ∀ {X : Set} → (X → R.ℝ) → List X → R.ℝ
foldR f [] = R.0ℝ
foldR f (x ∷ xs) = R._+_ (f x) (foldR f xs)

foldC : ∀ {X : Set} → (X → BishopComplex) → List X → BishopComplex
foldC f xs = C.complex (foldR (λ x → C.re (f x)) xs)
  (foldR (λ x → C.im (f x)) xs)

foldWeighted : ∀ {X : Set} (w : X → Nat) (v : R.ℝ) (xs : List X) →
  R._≃_ (foldR (λ x → R._*_ (N.natReal (w x)) v) xs)
    (R._*_ (N.natReal (W.foldNat w xs)) v)
foldWeighted w v [] =
  let open P.ℝ-Solver in solve 1 (λ x → Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊗ x) P.≃-refl v
foldWeighted w v (x ∷ xs) =
  P.≃-trans (P.+-cong P.≃-refl (foldWeighted w v xs))
    (P.≃-trans
      (let open P.ℝ-Solver in solve 3
        (λ a b z → (a ⊗ z) ⊕ (b ⊗ z) ⊜ (a ⊕ b) ⊗ z)
        P.≃-refl (N.natReal (w x)) (N.natReal (W.foldNat w xs)) v)
      (P.*-congʳ (P.≃-symm (natAdd (w x) (W.foldNat w xs)))))

foldPointwiseR : ∀ {X : Set} (f g : X → R.ℝ) (xs : List X) →
  (∀ x → R._≃_ (f x) (g x)) → R._≃_ (foldR f xs) (foldR g xs)
foldPointwiseR f g [] eq = P.≃-refl
foldPointwiseR f g (x ∷ xs) eq =
  P.+-cong (eq x) (foldPointwiseR f g xs eq)

-- Preserve the original product exponent before reading the degree fibre.
pairTerm : ∀ {r} → Nat → Nat → BishopComplex → F.PositiveFactorPair r → BishopComplex
pairTerm c k q p =
  scaleC (N.natReal (c * Pow.powNat (F.divisor p) k))
    (powC q (suc (F.predecessor p) * F.divisor p))

weightedFoldNat : ∀ {X : Set} c (w : X → Nat) (xs : List X) →
  W.foldNat (λ x → c * w x) xs ≡ c * W.foldNat w xs
weightedFoldNat c w [] = sym (NP.*-zeroʳ c)
weightedFoldNat c w (x ∷ xs) =
  trans
    (cong (c * w x +_) (weightedFoldNat c w xs))
    (sym (NP.*-distribˡ-+ c (w x) (W.foldNat w xs)))

coefficientReadout : ∀ c k r (pr : suc zero ≤ r) →
  W.foldNat (λ p → c * Pow.powNat (F.divisor p) k) (F.positiveFactorPairs r pr)
    ≡ c * Pow.sigmaPower k r
coefficientReadout c k r pr = trans
  (weightedFoldNat c (λ p → Pow.powNat (F.divisor p) k) (F.positiveFactorPairs r pr))
  (cong (c *_) (Read.positivePowerReadout k r pr))

degreeFibre : ∀ c k r (pr : suc zero ≤ r) q →
  foldC (pairTerm c k q) (F.positiveFactorPairs r pr) ≈C
  scaleC (N.natReal (c * Pow.sigmaPower k r)) (powC q r)
degreeFibre c k r pr q =
  let xs = F.positiveFactorPairs r pr
      w = λ p → c * Pow.powNat (F.divisor p) k
      read = coefficientReadout c k r pr
      realPoint : (p : F.PositiveFactorPair r) →
        R._≃_ (C.re (pairTerm c k q p))
          (R._*_ (N.natReal (w p)) (C.re (powC q r)))
      realPoint p = realEq (cong
        (λ j → C.re (scaleC (N.natReal (w p)) (powC q j)))
        (sym (F.productExact p)))
      imagPoint : (p : F.PositiveFactorPair r) →
        R._≃_ (C.im (pairTerm c k q p))
          (R._*_ (N.natReal (w p)) (C.im (powC q r)))
      imagPoint p = realEq (cong
        (λ j → C.im (scaleC (N.natReal (w p)) (powC q j)))
        (sym (F.productExact p)))
  in P.≃-trans (foldPointwiseR (λ p → C.re (pairTerm c k q p))
      (λ p → R._*_ (N.natReal (w p)) (C.re (powC q r))) xs realPoint)
      (P.≃-trans (foldWeighted w (C.re (powC q r)) xs)
        (realEq (cong (λ j → R._*_ (N.natReal j) (C.re (powC q r))) read)))
   , P.≃-trans (foldPointwiseR (λ p → C.im (pairTerm c k q p))
      (λ p → R._*_ (N.natReal (w p)) (C.im (powC q r))) xs imagPoint)
      (P.≃-trans (foldWeighted w (C.im (powC q r)) xs)
        (realEq (cong (λ j → R._*_ (N.natReal j) (C.im (powC q r))) read)))

-- Original normalized Fourier terms, including the unsigned E6 tail
-- (its subtraction from the constant term belongs to the existing owner).
e4Fibre : ∀ q n →
  foldC (pairTerm 240 3 q) (F.positiveFactorPairs (suc n) (s≤s z≤n))
    ≈C E.e4BishopTerm q n
e4Fibre q n = degreeFibre 240 3 (suc n) (s≤s z≤n) q

e6Fibre : ∀ q n →
  foldC (pairTerm 504 5 q) (F.positiveFactorPairs (suc n) (s≤s z≤n))
    ≈C E.e6BishopUnsignedTerm q n
e6Fibre q n = degreeFibre 504 5 (suc n) (s≤s z≤n) q
