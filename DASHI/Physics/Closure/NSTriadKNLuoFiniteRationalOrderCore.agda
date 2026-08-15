module DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore where

------------------------------------------------------------------------
-- Lightweight ordered-rational facts used by the finite Hölder proofs.
--
-- This deliberately does not import the Galerkin/L2 carrier.  Keeping these
-- elementary facts behind a small boundary prevents the Hölder theorem from
-- importing the full finite Cauchy--Schwarz development.
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
