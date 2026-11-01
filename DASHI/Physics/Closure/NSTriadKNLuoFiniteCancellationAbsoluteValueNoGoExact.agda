module DASHI.Physics.Closure.NSTriadKNLuoFiniteCancellationAbsoluteValueNoGoExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Mathematical ingredient: elementary ordered-field arithmetic.
-- Title: "Finite signed-cancellation versus absolute-majorant no-go".
-- Author: DASHI repository contributors.
-- DOI: not applicable; this is a repository-original finite audit lemma.
--
-- PURPOSE
-- Make one recurring proof-failure mode executable.  The signed pair
--
--   a + (-a)
--
-- cancels exactly, while the corresponding two-term magnitude majorant is
--
--   a + a.
--
-- At a=1 the signed sum is zero and the magnitude sum is exactly two.  Thus a
-- cancellation proved before taking absolute values cannot silently be used
-- after a Schur, supremum, or triangle-inequality majorisation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; -_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

signedPair : ℚ → ℚ
signedPair amplitude = amplitude + (- amplitude)

magnitudePair : ℚ → ℚ
magnitudePair amplitude = amplitude + amplitude

signedPairCancels :
  (amplitude : ℚ) → signedPair amplitude ≡ 0ℚ
signedPairCancels amplitude = solve (amplitude ∷ [])

two : ℚ
two = Int.+ 2 / 1

unitMagnitudePairIsTwo : magnitudePair 1ℚ ≡ two
unitMagnitudePairIsTwo = refl

zeroBelowTwo : 0ℚ ≤ two
zeroBelowTwo = toWitness {a? = 0ℚ ≤? two} _
