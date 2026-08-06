module DASHI.Physics.Closure.NSTriadKNLuoFiniteTraceFreeStretchCompressionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Evan Miller.
-- Title: "On the Interaction of Strain and Vorticity for Solutions of the
-- Navier--Stokes Equation".
-- arXiv:2407.02691.
-- DOI: none assigned in the cited preprint version.
--
-- PURPOSE
-- Formalise one exact piece of the geometric feedback suggested by
-- incompressibility.  A trace-free eigenvalue triple is represented by two
-- freely chosen entries and the derived third entry
--
--   lambda3 = -lambda1-lambda2.
--
-- For any stretching value lambda1, at least one transverse eigenvalue is at
-- most -lambda1/2.  This is a quantitative compression statement, not a
-- regularity theorem and not an assertion about which eigendirection the
-- vorticity follows.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _-_; -_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst₂)

half : ℚ
half = Int.+ 1 / 2

record TraceFreeStretchPair : Set where
  constructor trace-free-stretch-pair
  field
    stretching firstTransverse : ℚ

open TraceFreeStretchPair public

secondTransverse : TraceFreeStretchPair → ℚ
secondTransverse pair = - stretching pair - firstTransverse pair

traceFreeIdentity :
  (pair : TraceFreeStretchPair) →
  stretching pair + firstTransverse pair + secondTransverse pair ≡ 0ℚ
traceFreeIdentity pair =
  solve (stretching pair ∷ firstTransverse pair ∷ [])

negativeHalfStretch : TraceFreeStretchPair → ℚ
negativeHalfStretch pair = - (half * stretching pair)

secondTransverseBelowHalfFromFirstAbove :
  (pair : TraceFreeStretchPair) →
  negativeHalfStretch pair ≤ firstTransverse pair →
  secondTransverse pair ≤ negativeHalfStretch pair
secondTransverseBelowHalfFromFirstAbove pair firstAbove =
  let
    negated :
      - firstTransverse pair ≤ - negativeHalfStretch pair
    negated = ℚₚ.neg-antimono-≤ firstAbove

    shifted :
      - stretching pair + (- firstTransverse pair)
      ≤ - stretching pair + (- negativeHalfStretch pair)
    shifted = ℚₚ.+-monoʳ-≤ (- stretching pair) negated

    leftMeaning :
      - stretching pair + (- firstTransverse pair)
      ≡ secondTransverse pair
    leftMeaning =
      solve (stretching pair ∷ firstTransverse pair ∷ [])

    rightMeaning :
      - stretching pair + (- negativeHalfStretch pair)
      ≡ negativeHalfStretch pair
    rightMeaning =
      solve (stretching pair ∷ half ∷ [])
  in
  subst₂ _≤_ leftMeaning rightMeaning shifted

oneTransverseDirectionCompresses :
  (pair : TraceFreeStretchPair) →
  firstTransverse pair ≤ negativeHalfStretch pair
  ⊎ secondTransverse pair ≤ negativeHalfStretch pair
oneTransverseDirectionCompresses pair
  with ℚₚ.≤-total (firstTransverse pair) (negativeHalfStretch pair)
... | inj₁ firstBelow = inj₁ firstBelow
... | inj₂ firstAbove =
  inj₂ (secondTransverseBelowHalfFromFirstAbove pair firstAbove)
