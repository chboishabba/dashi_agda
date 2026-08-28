module DASHI.Foundations.BishopBaselFiniteSineProductCoefficientExact where

------------------------------------------------------------------------
-- FINITE EULER SINE-PRODUCT COEFFICIENT OWNER
--
-- Track only the constant and t-linear coefficients of
--
--   P_N(t) = product_{m=1}^N (1 - t / m^2).
--
-- No infinite product, sine-product identity, or Basel evaluation is asserted
-- here.  The finite algebra records exactly that the t coefficient accumulates
-- one negative reciprocal square at each factor.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 0ℚᵘ; 1ℚᵘ; _/_; _-_; _+_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

reciprocalSquare : Nat → ℚᵘ
reciprocalSquare index =
  let denominator = suc index * suc index
  in + 1 / denominator

------------------------------------------------------------------------
-- Degree-one jet.  This is intentionally smaller than a general polynomial
-- carrier: Basel only needs the coefficient of t=x^2.

record LinearJet : Set where
  constructor jet
  field
    constant : ℚᵘ
    linear : ℚᵘ

open LinearJet public

oneJet : LinearJet
oneJet = jet 1ℚᵘ 0ℚᵘ

multiplyByEulerFactor : LinearJet → Nat → LinearJet
multiplyByEulerFactor old index =
  jet
    (constant old)
    (linear old ℚ.- (constant old ℚ.* reciprocalSquare index))

finiteSineProductJet : Nat → LinearJet
finiteSineProductJet zero = oneJet
finiteSineProductJet (suc count) =
  multiplyByEulerFactor (finiteSineProductJet count) count

------------------------------------------------------------------------
-- The constant coefficient remains one, so the linear recurrence simplifies
-- to subtraction of the next reciprocal square.

finiteSineProductConstant :
  ∀ count → constant (finiteSineProductJet count) ≡ 1ℚᵘ
finiteSineProductConstant zero = refl
finiteSineProductConstant (suc count) = finiteSineProductConstant count

negativeBaselPrefix : Nat → ℚᵘ
negativeBaselPrefix zero = 0ℚᵘ
negativeBaselPrefix (suc count) =
  negativeBaselPrefix count ℚ.- reciprocalSquare count

finiteSineProductLinearIsNegativeBaselPrefix :
  ∀ count →
  linear (finiteSineProductJet count) ≡ negativeBaselPrefix count
finiteSineProductLinearIsNegativeBaselPrefix zero = refl
finiteSineProductLinearIsNegativeBaselPrefix (suc count)
  rewrite finiteSineProductConstant count
        | finiteSineProductLinearIsNegativeBaselPrefix count
  = refl

------------------------------------------------------------------------
-- Analytic seam kept explicit.  A future owner must identify the limit of the
-- finite products with sin(pi*x)/(pi*x) strongly enough to transport the
-- t=x^2 coefficient.  This module does not assume that theorem.

record EulerSineProductBaselBoundary : Set₁ where
  field
    InfiniteProductCarrier : Set
    FiniteProductsConverge : Set
    SineProductIdentification : Set
    QuadraticCoefficientPassesToLimit : Set

open EulerSineProductBaselBoundary public

bishopBaselFiniteSineProductCoefficientLevel : ProofLevel
bishopBaselFiniteSineProductCoefficientLevel = machineChecked
