module DASHI.Moonshine.JInvariantBishopRamanujanRowTransportExact where

-- Source-written. Transport the original signed integer divisor
-- convolution to the existing Bishop Cauchy rows, including both heads.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_∸_; s≤s; z≤n)
import Data.Nat.Properties as NP
open import Data.List.Base using (List; []; _∷_; _++_; map)
import Data.List.Properties as LP
open import Data.Integer.Base using (ℤ; +_)
import Data.Integer.Base as Z
import Data.Integer.Properties as ZP
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
import Real as R
open R using (ℝ; _≃_; _+_; _*_; _-_; _⋆)
import RealProperties as P
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as H
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSignedBoundaryExact as B
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionBoundaryRegroupExact as L
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSigmaFoldExact as V
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionInteriorFoldExact as I
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionFactorChartExact as C
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionClosedBoundaryExact as Closed

emb : ℤ → ℝ
emb z = (z / 1) ⋆

embEq : ∀ {a b : ℤ} → a ≡ b → emb a ≃ emb b
embEq refl = P.≃-refl

embAdd : (a b : ℤ) → emb (a Z.+ b) ≃ (emb a + emb b)
embAdd a b = P.≃-trans
  (P.⋆-cong (Q.*≡* (trans (ZP.*-identityʳ (a Z.+ b))
    (trans (cong₂ Z._+_ (sym (ZP.*-identityʳ a)) (sym (ZP.*-identityʳ b)))
      (sym (ZP.*-identityʳ ((a Z.* (+ 1)) Z.+ (b Z.* (+ 1)))))))))
  (P.⋆-distrib-+ (a / 1) (b / 1))

embMul : (a b : ℤ) → emb (a Z.* b) ≃ (emb a * emb b)
embMul a b = P.≃-trans
  (P.⋆-cong (Q.*≡* refl)) (P.⋆-distrib-* (a / 1) (b / 1))

embNeg : (a : ℤ) → emb (Z.- a) ≃ R.- (emb a)
embNeg a = P.⋆-distrib-neg (a / 1)

oneToHead : (n : Nat) → H.oneTo (suc n) ≡ 1 ∷ map suc (H.oneTo n)
oneToHead zero = refl
oneToHead (suc n) =
  trans (cong (_++ (suc (suc n) ∷ [])) (oneToHead n))
    (cong (1 ∷_) (sym (LP.map-++ suc (H.oneTo n) (suc n ∷ []))))

-- The positive part of the row, prior to splitting its last term.
tailInt : (f g : Nat → ℤ) → Nat → ℤ
tailInt f g n = B.foldZ (λ i → f i Z.* g (suc n ∸ i)) (H.oneTo (suc n))

tailStep : (f g : Nat → ℤ) (n : Nat) →
  tailInt f g (suc n) ≡ f 1 Z.* g (suc n) Z.+ tailInt (λ i → f (suc i)) g n
tailStep f g n =
  trans (cong (B.foldZ (λ i → f i Z.* g (suc (suc n) ∸ i))) (oneToHead (suc n)))
    (cong (f 1 Z.* g (suc n) Z.+_)
      (B.foldMap (λ i → f i Z.* g (suc (suc n) ∸ i)) suc (H.oneTo (suc n))))

tailReal : (f g : Nat → ℤ) (n : Nat) →
  Row.cauchyCoefficient (λ i → emb (f (suc i))) (λ i → emb (g i)) n ≃ emb (tailInt f g n)
tailReal f g zero =
  P.≃-trans (Row.cauchyCoefficientZero _ _)
    (P.≃-trans (P.≃-symm (embMul (f 1) (g 0)))
      (embEq (sym (ZP.+-identityʳ (f 1 Z.* g 0)))))
tailReal f g (suc n) =
  P.≃-trans (Row.cauchyCoefficientSuccessor _ _ n)
    (P.≃-trans (P.+-cong (P.≃-symm (embMul (f 1) (g (suc n))))
      (tailReal (λ i → f (suc i)) g n))
      (P.≃-trans (P.≃-symm (embAdd (f 1 Z.* g (suc n))
        (tailInt (λ i → f (suc i)) g n))) (embEq (sym (tailStep f g n)))))

stream : ℤ → Nat → Nat → ℤ
stream c k zero = + 1
stream c k (suc n) = c Z.* V.sigma k (suc n)

-- Remove the final positive-prefix term, which is precisely the second
-- normalized zero mode. No division at n=0.
tailSplit : (f g : Nat → ℤ) (n : Nat) →
  tailInt f g n ≡
  B.foldZ (λ i → f i Z.* g (suc n ∸ i)) (H.oneTo n) Z.+ f (suc n) Z.* g zero
tailSplit f g n =
  trans (L.foldAppend (λ i → f i Z.* g (suc n ∸ i)) (H.oneTo n) (suc n ∷ []))
    (cong (B.foldZ (λ i → f i Z.* g (suc n ∸ i)) (H.oneTo n) Z.+_)
      (trans (cong (λ v → f (suc n) Z.* g v Z.+ (+ 0)) (NP.n∸n≡0 (suc n)))
        (ZP.+-identityʳ (f (suc n) Z.* g zero))))

rowHead : (f g : Nat → ℤ) (n : Nat) →
  Row.cauchyCoefficient (λ i → emb (f i)) (λ i → emb (g i)) (suc n) ≃
  emb (f zero Z.* g (suc n) Z.+ (B.foldZ (λ i → f i Z.* g (suc n ∸ i)) (H.oneTo n)
    Z.+ f (suc n) Z.* g zero))
rowHead f g n = P.≃-trans (Row.cauchyCoefficientSuccessor _ _ n)
  (P.≃-trans (P.+-cong (P.≃-symm (embMul (f zero) (g (suc n))))
    (P.≃-trans (tailReal f g n) (embEq (tailSplit f g n))))
    (P.≃-symm (embAdd _ _)))

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥-elim)
import DASHI.Mathematics.NumberTheory.FiniteOneToEnumerationExact as One
open import Data.Nat.Base using (_<_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver

positiveStream : (c : ℤ) (k i : Nat) → zero < i → stream c k i ≡ c Z.* V.sigma k i
positiveStream c k zero ()
positiveStream c k (suc i) h = refl

complementPositive : (n i : Nat) → i ∈ H.oneTo n → zero < suc n ∸ i
complementPositive n i m =
  C.splitPositive (suc n) i
    (s≤s (One.oneToUpperBound m))

convFold : (a b : ℤ) (k l n : Nat) →
  B.foldZ (λ i → stream a k i Z.* stream b l (suc n ∸ i)) (H.oneTo n) ≡
  (a Z.* b) Z.* V.conv k l (suc n)
convFold a b k l n =
  let f = λ i → V.sigma k i Z.* V.sigma l (suc n ∸ i)
      g = λ i → (a Z.* b) Z.* f i
  in trans (B.foldCongOn (λ i → stream a k i Z.* stream b l (suc n ∸ i)) g (H.oneTo n)
    (λ {i} m → trans (cong₂ Z._*_ (positiveStream a k i (One.oneToPositive m))
      (positiveStream b l (suc n ∸ i) (complementPositive n i m)))
      (solve 4 (λ a b x y → (a :* x) :* (b :* y) := (a :* b) :* (x :* y))
        refl a b (V.sigma k i) (V.sigma l (suc n ∸ i)))))
    (trans (sym (Closed.scaleFold
      (a Z.* b) f (H.oneTo n)))
      (cong (λ x → (a Z.* b) Z.* B.foldZ f x) (sym (L.strictPrefix (suc n) n NP.≤-refl))))

-- Final real readout in original coefficient order.
rowProduct : (a b : ℤ) (k l n : Nat) →
  Row.cauchyCoefficient (λ i → emb (stream a k i)) (λ i → emb (stream b l i)) (suc n) ≃
  (emb a * emb (V.sigma k (suc n))) + (emb b * emb (V.sigma l (suc n))) +
    ((emb a * emb b) * emb (V.conv k l (suc n)))
rowProduct a b k l n =
  let x = V.sigma k (suc n)
      y = V.sigma l (suc n)
      z = V.conv k l (suc n)
      eq : (+ 1) Z.* (b Z.* y) Z.+ ((a Z.* b) Z.* z Z.+ (a Z.* x) Z.* (+ 1)) ≡
        (a Z.* x Z.+ b Z.* y) Z.+ (a Z.* b) Z.* z
      eq = solve 5 (λ a b x y z → con (+ 1) :* (b :* y) :+
        ((a :* b) :* z :+ (a :* x) :* con (+ 1)) :=
        (a :* x :+ b :* y) :+ (a :* b) :* z) refl a b x y z
  in P.≃-trans (rowHead (stream a k) (stream b l) n)
    (P.≃-trans (embEq (cong (λ v → (+ 1) Z.* (b Z.* y) Z.+ (v Z.+ (a Z.* x) Z.* (+ 1)))
      (convFold a b k l n)))
      (P.≃-trans (embEq eq)
        (P.≃-trans (embAdd _ _) (P.+-cong
          (P.≃-trans (embAdd _ _) (P.+-cong (embMul a x) (embMul b y)))
          (P.≃-trans (embMul _ z) (P.*-congʳ (embMul a b)))))))
