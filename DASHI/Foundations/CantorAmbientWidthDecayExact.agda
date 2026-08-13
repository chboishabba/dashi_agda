module DASHI.Foundations.CantorAmbientWidthDecayExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.List.Base using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; ½; _/_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Analysis.CanonicalRationalMetric as Metric

------------------------------------------------------------------------
-- CONSTRUCTIVE AMBIENT-WIDTH DECAY FOR THE TERNARY CANTOR SURVIVOR
--
-- The total ordinary interval width at depth n is (2/3)^n.  Instead of merely
-- asserting a limit, we give an explicit dyadic modulus: at depth 2k the width
-- is at most 2^-k because (2/3)^2 = 4/9 <= 1/2.
------------------------------------------------------------------------

twoThird : ℚ
twoThird = Int.+ 2 / 3

twoThirdNonnegative : 0ℚ ≤ twoThird
twoThirdNonnegative = toWitness {a? = 0ℚ ≤? twoThird} _

twoThirdSquareBelowHalf : twoThird * twoThird ≤ ½
twoThirdSquareBelowHalf =
  toWitness {a? = (twoThird * twoThird) ≤? ½} _

pow : ℚ → Nat → ℚ
pow ratio zero = 1ℚ
pow ratio (suc exponent) = ratio * pow ratio exponent

powNonnegative :
  (ratio : ℚ) → (exponent : Nat) →
  0ℚ ≤ ratio → 0ℚ ≤ pow ratio exponent
powNonnegative ratio zero ratioNonnegative =
  toWitness {a? = 0ℚ ≤? 1ℚ} _
powNonnegative ratio (suc exponent) ratioNonnegative =
  let
    instance
      ratioNN = nonNegative ratioNonnegative
      powerNN = nonNegative (powNonnegative ratio exponent ratioNonnegative)
      productNN = ℚₚ.nonNeg*nonNeg⇒nonNeg ratio (pow ratio exponent)
  in
  ℚₚ.nonNegative⁻¹ (ratio * pow ratio exponent)

ambientWidth : Nat → ℚ
ambientWidth depth = pow twoThird depth

evenDepth : Nat → Nat
evenDepth zero = zero
evenDepth (suc k) = suc (suc (evenDepth k))

private
  pairStep : (x : ℚ) →
    twoThird * (twoThird * x) ≡ (twoThird * twoThird) * x
  pairStep x = solve (twoThird ∷ x ∷ [])

ambientWidthAtEvenDepthBelowDyadic :
  (k : Nat) →
  ambientWidth (evenDepth k) ≤ Metric.dyadicQ k
ambientWidthAtEvenDepthBelowDyadic zero = ℚₚ.≤-refl
ambientWidthAtEvenDepthBelowDyadic (suc k) =
  begin
    ambientWidth (evenDepth (suc k))
      ≡⟨ pairStep (ambientWidth (evenDepth k)) ⟩
    (twoThird * twoThird) * ambientWidth (evenDepth k)
      ≤⟨ squareScaled ⟩
    ½ * ambientWidth (evenDepth k)
      ≤⟨ halfScaled ⟩
    ½ * Metric.dyadicQ k
      ≡⟨ sym (Metric.dyadicStepℚ k) ⟩
    Metric.dyadicQ (suc k)
    ∎
  where
    open ℚₚ.≤-Reasoning

    widthNonnegative : 0ℚ ≤ ambientWidth (evenDepth k)
    widthNonnegative =
      powNonnegative twoThird (evenDepth k) twoThirdNonnegative

    squareScaled :
      (twoThird * twoThird) * ambientWidth (evenDepth k)
      ≤ ½ * ambientWidth (evenDepth k)
    squareScaled =
      let
        instance widthNN = nonNegative widthNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (ambientWidth (evenDepth k))
        twoThirdSquareBelowHalf

    halfScaled :
      ½ * ambientWidth (evenDepth k)
      ≤ ½ * Metric.dyadicQ k
    halfScaled =
      let
        instance halfNN = nonNegative Metric.halfNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        ½
        (ambientWidthAtEvenDepthBelowDyadic k)

------------------------------------------------------------------------
-- Explicit limiting certificate: every dyadic precision 2^-k is reached by
-- the concrete depth N = 2k.  This is the constructive content needed for
-- ambientWidth(n) -> 0 without importing a separate epsilon-real-limit API.
------------------------------------------------------------------------

record AmbientWidthConvergesToZero : Set where
  constructor ambientWidthConvergesToZero
  field
    witnessDepth : Nat → Nat
    widthBelowDyadicTolerance :
      (k : Nat) → ambientWidth (witnessDepth k) ≤ Metric.dyadicQ k

open AmbientWidthConvergesToZero public

canonicalAmbientWidthConvergence : AmbientWidthConvergesToZero
canonicalAmbientWidthConvergence =
  ambientWidthConvergesToZero evenDepth ambientWidthAtEvenDepthBelowDyadic
