module DASHI.Foundations.PolynomialVandermondeDiscriminantExact where

------------------------------------------------------------------------
-- VIETE / VANDERMONDE / DISCRIMINANT: THE ACTUAL S3 ROOT BRANCH CUT.
--
-- Classical roots: Vandermonde (1770), Lagrange (1770-71), Galois
-- (1830-32), and the standard discriminant. This exact rational
-- three-root polynomial is an algebraic finite foundation for the
-- video's branch-point discussion, NOT a complex covering theorem.
--
-- V=(a-b)(a-c)(b-c) has a sign representation of S3:
-- EVEN C3 preserves V; ODD swaps negate V.
-- Δ=V² is invariant under ALL six root permutations.
-- Δ vanishes whenever any two of the three roots coincide.
-- This is a genuine equivariant map separating A3 from odd S3,
-- unlike the numeric 3^5/5^3/wave-operator analogies.
--
-- Proof uses the original rational-ring tactic and original Vieta/S3
-- roots, never duplicates permutation or polynomial coefficients.
-- All claims SOURCE-WRITTEN / AGDA KERNEL PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; -_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Foundations.PolynomialVietaRootSymmetryExact as Vieta
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as S3

vandermonde : Vieta.ThreeRoots → ℚ
vandermonde (Vieta.roots a b c) =
  (a - b) * (a - c) * (b - c)

discriminant : Vieta.ThreeRoots → ℚ
discriminant r = vandermonde r * vandermonde r

isOdd : S3.TriPermutation → ℚ → ℚ
isOdd S3.permIdentity x = x
isOdd S3.permRotate x = x
isOdd S3.permRotate2 x = x
isOdd S3.permSwapLowMid x = - x
isOdd S3.permSwapLowHigh x = - x
isOdd S3.permSwapMidHigh x = - x

-- This is the six-permutation sign character on the alternating
-- root product. Odd swaps cannot preserve V generically.
vandermondeTransformsByParity :
  (p : S3.TriPermutation) (r : Vieta.ThreeRoots) →
  vandermonde (Vieta.permuteRoots p r)
  ≡ isOdd p (vandermonde r)
vandermondeTransformsByParity S3.permIdentity r = refl
vandermondeTransformsByParity S3.permRotate (Vieta.roots a b c) = Ring.solve-∀ a b c
vandermondeTransformsByParity S3.permRotate2 (Vieta.roots a b c) = Ring.solve-∀ a b c
vandermondeTransformsByParity S3.permSwapLowMid (Vieta.roots a b c) = Ring.solve-∀ a b c
vandermondeTransformsByParity S3.permSwapLowHigh (Vieta.roots a b c) = Ring.solve-∀ a b c
vandermondeTransformsByParity S3.permSwapMidHigh (Vieta.roots a b c) = Ring.solve-∀ a b c

discriminantInvariant :
  (p : S3.TriPermutation) (r : Vieta.ThreeRoots) →
  discriminant (Vieta.permuteRoots p r)
  ≡ discriminant r
discriminantInvariant S3.permIdentity r = refl
discriminantInvariant S3.permRotate (Vieta.roots a b c) = Ring.solve-∀ a b c
discriminantInvariant S3.permRotate2 (Vieta.roots a b c) = Ring.solve-∀ a b c
discriminantInvariant S3.permSwapLowMid (Vieta.roots a b c) = Ring.solve-∀ a b c
discriminantInvariant S3.permSwapLowHigh (Vieta.roots a b c) = Ring.solve-∀ a b c
discriminantInvariant S3.permSwapMidHigh (Vieta.roots a b c) = Ring.solve-∀ a b c

firstSecondCollisionGivesZero :
  (a c : ℚ) →
  discriminant (Vieta.roots a a c) ≡ 0ℚ
firstSecondCollisionGivesZero a c = Ring.solve-∀ a c

firstThirdCollisionGivesZero :
  (a b : ℚ) →
  discriminant (Vieta.roots a b a) ≡ 0ℚ
firstThirdCollisionGivesZero a b = Ring.solve-∀ a b

secondThirdCollisionGivesZero :
  (a b : ℚ) →
  discriminant (Vieta.roots a b b) ≡ 0ℚ
secondThirdCollisionGivesZero a b = Ring.solve-∀ a b

-- This is a concrete discriminant vanishing implication. The
-- converse (Δ=0 -> collision) and a nonzero complex coefficient
-- covering/path-lift require field integral-domain and topology
-- proofs, not finite root permutation tables alone.

------------------------------------------------------------------------
-- COEFFICIENT-ONLY CUBIC DISCRIMINANT.
-- For monic x³ - s₁x² + s₂x - s₃, this is the classical formula.
-- It makes explicit that Δ is a FUNCTION OF THE COEFFICIENTS,
-- not simply a numerically equal root-oriented expression.
------------------------------------------------------------------------

four : ℚ
four = 1ℚ + 1ℚ + 1ℚ + 1ℚ

eighteen : ℚ
eighteen = (four * four) + 1ℚ + 1ℚ

twentySeven : ℚ
twentySeven = (four * four) + (four * four) - four - 1ℚ

coefficientDiscriminant : ℚ → ℚ → ℚ → ℚ
coefficientDiscriminant s₁ s₂ s₃ =
  s₁ * s₁ * (s₂ * s₂)
  - ((s₂ * s₂ * s₂) * four)
  - ((s₁ * s₁ * s₁) * (s₃ * four))
  - ((s₃ * s₃) * twentySeven)
  + ((s₁ * s₂ * s₃) * eighteen)

discriminantDependsOnlyOnVietaCoefficients :
  (r : Vieta.ThreeRoots) →
  discriminant r ≡
  coefficientDiscriminant
    (Vieta.rootSum r) (Vieta.rootPairSum r) (Vieta.rootProduct r)
discriminantDependsOnlyOnVietaCoefficients
  (Vieta.roots a b c) = Ring.solve-∀ a b c


------------------------------------------------------------------------
-- CONVERSE: ZERO CUBIC DISCRIMINANT IMPLIES A ROOT COLLISION.
-- Supply the two exact rational field properties. The underlying
-- algebra is classical and already belongs to rational stdlib:
--    xy=0 -> x=0 or y=0, and a-b=0 -> a=b.
-- We do not misreport this as an unconditional proof until the two
-- rational laws are instantiated with the installed stdlib version.
------------------------------------------------------------------------

record RationalDomainLawWitness : Set where
  field
    zeroProduct :
      (x y : ℚ) → x * y ≡ 0ℚ → (x ≡ 0ℚ) ⊎ (y ≡ 0ℚ)
    zeroDifference :
      (x y : ℚ) → x - y ≡ 0ℚ → x ≡ y

open RationalDomainLawWitness public

splitVandermondeZero :
  (laws : RationalDomainLawWitness) →
  (a b c : ℚ) →
  vandermonde (Vieta.roots a b c) ≡ 0ℚ →
  (a ≡ b) ⊎ ((a ≡ c) ⊎ (b ≡ c))
splitVandermondeZero laws a b c vZero
  with zeroProduct laws ((a - b) * (a - c)) (b - c) vZero
... | inj₂ bcZero =
  inj₂ (inj₂ (zeroDifference laws b c bcZero))
... | inj₁ firstZero
  with zeroProduct laws (a - b) (a - c) firstZero
...   | inj₁ abZero = inj₁ (zeroDifference laws a b abZero)
...   | inj₂ acZero = inj₂ (inj₁ (zeroDifference laws a c acZero))

zeroDiscriminantImpliesCollision :
  (laws : RationalDomainLawWitness) →
  (a b c : ℚ) →
  discriminant (Vieta.roots a b c) ≡ 0ℚ →
  (a ≡ b) ⊎ ((a ≡ c) ⊎ (b ≡ c))
zeroDiscriminantImpliesCollision laws a b c discZero
  with zeroProduct laws
    (vandermonde (Vieta.roots a b c))
    (vandermonde (Vieta.roots a b c)) discZero
... | inj₁ vZero = splitVandermondeZero laws a b c vZero
... | inj₂ vZero = splitVandermondeZero laws a b c vZero

-- The converse is now a short genuine constructive proof with two
-- explicitly named missing field-property instances. It is not a
-- claimed topological discriminant-complement construction.
