module DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHalfSplitExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Formalize the source-faithful lower/upper dyadic-range combination used in
-- Luo Section 4.  The two halves are not replaced by one pointwise multiplier
-- estimate.  Instead the module proves
--
--   (L+U)^2 <= 2 (L^2+U^2)
--
-- from the nonnegativity of (L-U)^2, and then transports separately proved
-- lower- and upper-half estimates into one complete J11 estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; subst₂)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

two : ℚ
two = Int.+ 2 / 1

twoNonnegative : 0ℚ ≤ two
twoNonnegative = toWitness {a? = 0ℚ ≤? two} _

squareOfSumBelowTwiceSquares :
  (lower upper : ℚ) →
  L2.square (lower + upper)
  ≤ two * (L2.square lower + L2.square upper)
squareOfSumBelowTwiceSquares lower upper =
  let
    differenceSquareNonnegative :
      0ℚ ≤ L2.square (lower - upper)
    differenceSquareNonnegative =
      L2.squareNonnegative (lower - upper)

    shifted :
      L2.square (lower + upper) + 0ℚ
      ≤ L2.square (lower + upper) + L2.square (lower - upper)
    shifted =
      ℚₚ.+-monoʳ-≤
        (L2.square (lower + upper))
        differenceSquareNonnegative

    leftMeaning :
      L2.square (lower + upper) + 0ℚ
      ≡ L2.square (lower + upper)
    leftMeaning = solve (lower ∷ upper ∷ [])

    rightMeaning :
      L2.square (lower + upper) + L2.square (lower - upper)
      ≡ two * (L2.square lower + L2.square upper)
    rightMeaning = solve (lower ∷ upper ∷ [])
  in
  subst₂ _≤_ leftMeaning rightMeaning shifted

record FiniteDyadicHalfSplitData : Set where
  constructor finite-dyadic-half-split
  field
    lowerHalf upperHalf delta lowerBudget upperBudget : ℚ

    lowerHalfSquaredBound :
      L2.square lowerHalf ≤ delta * lowerBudget

    upperHalfSquaredBound :
      L2.square upperHalf ≤ delta * upperBudget

open FiniteDyadicHalfSplitData public

halfSquaresBound :
  (data : FiniteDyadicHalfSplitData) →
  L2.square (lowerHalf data) + L2.square (upperHalf data)
  ≤ delta data * lowerBudget data + delta data * upperBudget data
halfSquaresBound data =
  ℚₚ.+-mono-≤
    (lowerHalfSquaredBound data)
    (upperHalfSquaredBound data)

twiceHalfSquaresBound :
  (data : FiniteDyadicHalfSplitData) →
  two * (L2.square (lowerHalf data) + L2.square (upperHalf data))
  ≤ two * (delta data * lowerBudget data + delta data * upperBudget data)
twiceHalfSquaresBound data =
  let instance twoIsNonnegative = nonNegative twoNonnegative
  in
  ℚₚ.*-monoˡ-≤-nonNeg two (halfSquaresBound data)

combinedHalfBound :
  (data : FiniteDyadicHalfSplitData) →
  L2.square (lowerHalf data + upperHalf data)
  ≤ two * delta data * (lowerBudget data + upperBudget data)
combinedHalfBound data =
  let
    first =
      ℚₚ.≤-trans
        (squareOfSumBelowTwiceSquares
          (lowerHalf data) (upperHalf data))
        (twiceHalfSquaresBound data)

    targetMeaning :
      two * (delta data * lowerBudget data + delta data * upperBudget data)
      ≡ two * delta data * (lowerBudget data + upperBudget data)
    targetMeaning =
      solve
        ( two
        ∷ delta data
        ∷ lowerBudget data
        ∷ upperBudget data
        ∷ []
        )
  in
  subst
    (λ upper →
      L2.square (lowerHalf data + upperHalf data) ≤ upper)
    targetMeaning
    first

finiteDyadicHalfSplitClosed : Bool
finiteDyadicHalfSplitClosed = true

finiteDyadicHalfSplitClosedIsTrue :
  finiteDyadicHalfSplitClosed ≡ true
finiteDyadicHalfSplitClosedIsTrue = refl
