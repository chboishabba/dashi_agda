module DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore where

------------------------------------------------------------------------
-- Lightweight ordered-rational facts used by the finite Hölder and kernel
-- proofs.
--
-- This deliberately does not import the Galerkin/L2 carrier.  Keeping these
-- elementary facts behind a small boundary prevents local finite inequalities
-- from importing the full finite Cauchy--Schwarz / Gram-defect development.
-- Round 61 profiling confirmed that distinction is material: the legacy
-- recursive Gram path spent roughly 263.5 seconds in finiteGramStep before the
-- constant-one Hölder proof itself was reached.  The compiled constant-one
-- Hölder route therefore depends only on this core.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative; nonPositive)
import Data.Rational.Properties as ℚₚ
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)

square : ℚ → ℚ
square value = value * value

addNonnegative :
  ∀ {left right} →
  0ℚ ≤ left →
  0ℚ ≤ right →
  0ℚ ≤ left + right
addNonnegative {left} {right} leftNonnegative rightNonnegative =
  subst
    (λ lower → lower ≤ left + right)
    (ℚₚ.+-identityˡ 0ℚ)
    (ℚₚ.+-mono-≤ leftNonnegative rightNonnegative)

squareNonnegative : ∀ value → 0ℚ ≤ square value
squareNonnegative value with ℚₚ.≤-total 0ℚ value
... | inj₁ nonnegative =
  let
    instance
      valueNonnegative = ℚ.nonNegative nonnegative
      productNonnegative = ℚₚ.nonNeg*nonNeg⇒nonNeg value value
  in
  ℚₚ.nonNegative⁻¹ (value * value)
... | inj₂ nonpositive =
  let
    instance
      valueNonpositive = ℚ.nonPositive nonpositive
      productNonnegative = ℚₚ.nonPos*nonPos⇒nonNeg value value
  in
  ℚₚ.nonNegative⁻¹ (value * value)

-- This is the only multiplicative monotonicity fact required by the legacy
-- six-three kernel consumer.  It used to be imported through
-- NSTriadKNRationalOrderedFiniteL2, thereby pulling the complete recursive
-- finite Gram/Cauchy--Schwarz proof graph into a theorem that only needs
-- ordered-field arithmetic.
nonnegativeProductMonotone :
  ∀ {a b c d : ℚ} →
  0ℚ ≤ a →
  0ℚ ≤ b →
  0ℚ ≤ c →
  0ℚ ≤ d →
  a ≤ c →
  b ≤ d →
  a * b ≤ c * d
nonnegativeProductMonotone {a} {b} {c} {d}
    aNonnegative bNonnegative cNonnegative dNonnegative a≤c b≤d =
  let
    instance
      aNN = ℚ.nonNegative aNonnegative
      bNN = ℚ.nonNegative bNonnegative
      cNN = ℚ.nonNegative cNonnegative
      dNN = ℚ.nonNegative dNonnegative

    first : a * b ≤ c * b
    first = ℚₚ.*-monoʳ-≤-nonNeg b a≤c

    second : c * b ≤ c * d
    second = ℚₚ.*-monoˡ-≤-nonNeg c b≤d
  in
  ℚₚ.≤-trans first second
