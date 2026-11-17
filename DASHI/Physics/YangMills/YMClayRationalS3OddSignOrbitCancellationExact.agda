{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRationalS3OddSignOrbitCancellationExact where

------------------------------------------------------------------------
-- Source-written universal signed-orbit cancellation for Q^4.
-- One odd coordinate exponent is sufficient to cancel the complete
-- sixteen-element sign orbit. No fixed polynomial-degree bound,
-- no finite cubature assumption, no Haar input, and no sqrt/pi.
--
-- This proves the ODD-parity part of B4 Reynolds averaging.
-- Coordinate-permutation normal forms and full even-invariant
-- decomposition are separate Agda obligations.
--
-- Sources: original DASHI rational SU2 / hyperoctahedral owners;
-- elementary finite-group Reynolds averaging (Weyl).
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

evenPower : ℚ → Nat → ℚ
evenPower x zero = 1ℚ
evenPower x (suc n) = (x * x) * evenPower x n

oddPower : ℚ → Nat → ℚ
oddPower x n = x * evenPower x n

squareSign : ∀ x v →
  ((- x) * (- x)) * v ≡ (x * x) * v
squareSign = ℚRing.solve-∀

oddFactor : ∀ x v →
  (- x) * v ≡ - (x * v)
oddFactor = ℚRing.solve-∀

oppositeSum : ∀ x → x + (- x) ≡ 0ℚ
oppositeSum = ℚRing.solve-∀

evenPowerSign : ∀ x n →
  evenPower (- x) n ≡ evenPower x n
evenPowerSign x zero = refl
evenPowerSign x (suc n) =
  trans
    (cong (λ v → ((- x) * (- x)) * v)
      (evenPowerSign x n))
    (squareSign x (evenPower x n))

oddPowerSign : ∀ x n →
  oddPower (- x) n ≡ - (oddPower x n)
oddPowerSign x n =
  trans
    (cong (λ v → (- x) * v) (evenPowerSign x n))
    (oddFactor x (evenPower x n))

signedPair : (ℚ → ℚ) → ℚ → ℚ
signedPair f x = f x + f (- x)

signedPairOddZero :
  ∀ (f : ℚ → ℚ) x →
  (∀ y → f (- y) ≡ - (f y)) →
  signedPair f x ≡ 0ℚ
signedPairOddZero f x parity =
  trans
    (cong (λ v → f x + v) (parity x))
    (oppositeSum (f x))

-- The 2^3 residual sign choices on the other coordinates.
sumOtherThreeSigns : (ℚ → ℚ → ℚ → ℚ) → ℚ → ℚ → ℚ → ℚ
sumOtherThreeSigns f b c d =
    f b c d
  + f (- b) c d
  + f b (- c) d
  + f b c (- d)
  + f (- b) (- c) d
  + f (- b) c (- d)
  + f b (- c) (- d)
  + f (- b) (- c) (- d)

sumOtherThreeZero :
  ∀ (f : ℚ → ℚ → ℚ → ℚ) b c d →
  (∀ x y z → f x y z ≡ 0ℚ) →
  sumOtherThreeSigns f b c d ≡ 0ℚ
sumOtherThreeZero f b c d zeroF
  rewrite zeroF b c d
        | zeroF (- b) c d
        | zeroF b (- c) d
        | zeroF b c (- d)
        | zeroF (- b) (- c) d
        | zeroF (- b) c (- d)
        | zeroF b (- c) (- d)
        | zeroF (- b) (- c) (- d)
  = ℚRing.solve []

-- The actual full signed coordinate orbit, duplicates included at
-- zero coordinates: a 16-term *multiset*. Uniform averaging of that
-- multiset is the correct Reynolds operator, including stabilizers.
signedOrbitSixteen :
  (ℚ → ℚ → ℚ → ℚ → ℚ) → ℚ → ℚ → ℚ → ℚ → ℚ
signedOrbitSixteen f a b c d =
  sumOtherThreeSigns
    (λ b' c' d' → signedPair (λ a' → f a' b' c' d') a)
    b c d

signedOrbitOddInFirst :
  ∀ (f : ℚ → ℚ → ℚ → ℚ → ℚ) a b c d →
  (∀ x y z w → f (- x) y z w ≡ - (f x y z w)) →
  signedOrbitSixteen f a b c d ≡ 0ℚ
signedOrbitOddInFirst f a b c d parity =
  sumOtherThreeZero
    (λ b' c' d' → signedPair (λ a' → f a' b' c' d') a)
    b c d
    (λ b' c' d' →
      signedPairOddZero (λ a' → f a' b' c' d') a
        (λ x → parity x b' c' d'))

-- Any odd exponent in q0 is enough, at ARBITRARY degree. Other
-- coordinates may have arbitrary signed-parity monomial factors.
oddFirstMonomial :
  Nat → (ℚ → ℚ → ℚ → ℚ) → ℚ → ℚ → ℚ → ℚ → ℚ
oddFirstMonomial n g a b c d =
  oddPower a n * g b c d

oddFirstMonomialParity :
  ∀ n g a b c d →
  oddFirstMonomial n g (- a) b c d
  ≡ - (oddFirstMonomial n g a b c d)
oddFirstMonomialParity n g a b c d =
  trans
    (cong (λ v → v * g b c d) (oddPowerSign a n))
    (oddFactor (oddPower a n) (g b c d))

oddFirstMonomialOrbitZero :
  ∀ n g a b c d →
  signedOrbitSixteen (oddFirstMonomial n g) a b c d ≡ 0ℚ
oddFirstMonomialOrbitZero n g a b c d =
  signedOrbitOddInFirst
    (oddFirstMonomial n g) a b c d
    (oddFirstMonomialParity n g)
