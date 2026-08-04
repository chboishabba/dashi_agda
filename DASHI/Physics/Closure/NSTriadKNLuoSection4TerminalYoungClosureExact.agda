module DASHI.Physics.Closure.NSTriadKNLuoSection4TerminalYoungClosureExact where

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
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- PURPOSE
-- Prove the exact ordered-field calculation closing Luo's final Section-4
-- estimate.  In rational form, if
--
--   X^2 <= delta (a X + lambda),
--   a^2 <= lambda,
--   0 <= delta <= 1,
--
-- then Young's inequality gives
--
--   X^2 <= 3 delta lambda.
--
-- This is the algebra behind the passage from equation (4.10) to (4.11).
-- The theorem proves the Young step, absorption, and exact constant; it does
-- not assume the final energy bound as an input.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; -_; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

two three : ℚ
two = Int.+ 2 / 1
three = Int.+ 3 / 1

twoNonnegative : 0ℚ ≤ two
twoNonnegative = toWitness {a? = 0ℚ ≤? two} _

square : ℚ → ℚ
square value = value * value

youngTwice :
  (left right : ℚ) →
  two * (left * right)
  ≤ square left + square right
youngTwice left right =
  let
    differenceSquareNonnegative :
      0ℚ ≤ square (left - right)
    differenceSquareNonnegative =
      L2.squareNonnegative (left - right)

    shifted :
      two * (left * right) + 0ℚ
      ≤ two * (left * right) + square (left - right)
    shifted =
      ℚₚ.+-monoʳ-≤
        (two * (left * right))
        differenceSquareNonnegative

    leftMeaning :
      two * (left * right) + 0ℚ
      ≡ two * (left * right)
    leftMeaning = solve (left ∷ right ∷ [])

    rightMeaning :
      two * (left * right) + square (left - right)
      ≡ square left + square right
    rightMeaning = solve (left ∷ right ∷ [])
  in
  subst₂ _≤_ leftMeaning rightMeaning shifted

addNegativeCommon :
  ∀ left right common →
  left ≤ right →
  left - common ≤ right - common
addNegativeCommon left right common inequality =
  subst₂ _≤_
    (solve (left ∷ common ∷ []))
    (solve (right ∷ common ∷ []))
    (ℚₚ.+-monoʳ-≤ (- common) inequality)

record Section4TerminalYoungData : Set where
  constructor section4-terminal-young
  field
    X delta halfScale lambda : ℚ

    XNonnegative : 0ℚ ≤ X
    deltaNonnegative : 0ℚ ≤ delta
    halfScaleNonnegative : 0ℚ ≤ halfScale
    lambdaNonnegative : 0ℚ ≤ lambda

    deltaAtMostOne : delta ≤ 1ℚ
    halfScaleSquaredBelowLambda :
      square halfScale ≤ lambda

    section4PreYoungInequality :
      square X
      ≤ delta * (halfScale * X + lambda)

open Section4TerminalYoungData public

deltaSquaredNonnegative :
  (data : Section4TerminalYoungData) →
  0ℚ ≤ square (delta data)
deltaSquaredNonnegative data =
  L2.squareNonnegative (delta data)

deltaSquaredBelowDelta :
  (data : Section4TerminalYoungData) →
  square (delta data) ≤ delta data
deltaSquaredBelowDelta data =
  let
    instance
      deltaIsNonnegative = nonNegative (deltaNonnegative data)
  in
  subst
    (λ upper → square (delta data) ≤ upper)
    (solve (delta data ∷ []))
    (ℚₚ.*-monoˡ-≤-nonNeg
      (delta data)
      (deltaAtMostOne data))

doubledPreYoungInequality :
  (data : Section4TerminalYoungData) →
  two * square (X data)
  ≤ two * (delta data * (halfScale data * X data + lambda data))
doubledPreYoungInequality data =
  let instance twoIsNonnegative = nonNegative twoNonnegative
  in
  ℚₚ.*-monoˡ-≤-nonNeg
    two
    (section4PreYoungInequality data)

scaledYoungProduct :
  (data : Section4TerminalYoungData) →
  two * (delta data * halfScale data * X data)
  ≤ square (delta data * halfScale data) + square (X data)
scaledYoungProduct data =
  subst
    (λ lower → lower ≤
      square (delta data * halfScale data) + square (X data))
    (solve (delta data ∷ halfScale data ∷ X data ∷ []))
    (youngTwice (delta data * halfScale data) (X data))

preAbsorptionBound :
  (data : Section4TerminalYoungData) →
  two * square (X data)
  ≤ square (X data)
      + ( square (delta data) * square (halfScale data)
        + two * (delta data * lambda data)
        )
preAbsorptionBound data =
  let
    addedLambda :
      two * (delta data * halfScale data * X data)
        + two * (delta data * lambda data)
      ≤ (square (delta data * halfScale data) + square (X data))
        + two * (delta data * lambda data)
    addedLambda =
      ℚₚ.+-mono-≤
        (scaledYoungProduct data)
        ℚₚ.≤-refl

    doubledExpanded :
      two * (delta data * (halfScale data * X data + lambda data))
      ≡ two * (delta data * halfScale data * X data)
        + two * (delta data * lambda data)
    doubledExpanded =
      solve
        ( two
        ∷ delta data
        ∷ halfScale data
        ∷ X data
        ∷ lambda data
        ∷ []
        )

    youngExpanded :
      (square (delta data * halfScale data) + square (X data))
        + two * (delta data * lambda data)
      ≡ square (X data)
        + ( square (delta data) * square (halfScale data)
          + two * (delta data * lambda data)
          )
    youngExpanded =
      solve
        ( delta data
        ∷ halfScale data
        ∷ X data
        ∷ lambda data
        ∷ []
        )
  in
  ℚₚ.≤-trans
    (doubledPreYoungInequality data)
    (subst₂ _≤_
      (sym doubledExpanded)
      youngExpanded
      addedLambda)

absorbedSquareBound :
  (data : Section4TerminalYoungData) →
  square (X data)
  ≤ square (delta data) * square (halfScale data)
    + two * (delta data * lambda data)
absorbedSquareBound data =
  let
    translated =
      addNegativeCommon
        (two * square (X data))
        ( square (X data)
          + ( square (delta data) * square (halfScale data)
            + two * (delta data * lambda data)))
        (square (X data))
        (preAbsorptionBound data)

    leftMeaning :
      two * square (X data) - square (X data)
      ≡ square (X data)
    leftMeaning = solve (X data ∷ [])

    rightMeaning :
      ( square (X data)
        + ( square (delta data) * square (halfScale data)
          + two * (delta data * lambda data)))
      - square (X data)
      ≡ square (delta data) * square (halfScale data)
        + two * (delta data * lambda data)
    rightMeaning =
      solve
        ( X data
        ∷ delta data
        ∷ halfScale data
        ∷ lambda data
        ∷ []
        )
  in
  subst₂ _≤_ leftMeaning rightMeaning translated

deltaSquaredScaleBelowDeltaLambda :
  (data : Section4TerminalYoungData) →
  square (delta data) * square (halfScale data)
  ≤ delta data * lambda data
deltaSquaredScaleBelowDeltaLambda data =
  let
    firstStep :
      square (delta data) * square (halfScale data)
      ≤ square (delta data) * lambda data
    firstStep =
      let instance deltaSquaredIsNonnegative =
        nonNegative (deltaSquaredNonnegative data)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (square (delta data))
        (halfScaleSquaredBelowLambda data)

    secondStep :
      square (delta data) * lambda data
      ≤ delta data * lambda data
    secondStep =
      let instance lambdaIsNonnegative =
        nonNegative (lambdaNonnegative data)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (lambda data)
        (deltaSquaredBelowDelta data)
  in
  ℚₚ.≤-trans firstStep secondStep

section4TerminalYoungClosure :
  (data : Section4TerminalYoungData) →
  square (X data)
  ≤ three * (delta data * lambda data)
section4TerminalYoungClosure data =
  let
    combined :
      square (delta data) * square (halfScale data)
        + two * (delta data * lambda data)
      ≤ delta data * lambda data
        + two * (delta data * lambda data)
    combined =
      ℚₚ.+-mono-≤
        (deltaSquaredScaleBelowDeltaLambda data)
        ℚₚ.≤-refl

    targetMeaning :
      delta data * lambda data
        + two * (delta data * lambda data)
      ≡ three * (delta data * lambda data)
    targetMeaning =
      solve (delta data ∷ lambda data ∷ [])
  in
  ℚₚ.≤-trans
    (absorbedSquareBound data)
    (subst
      (λ upper →
        square (delta data) * square (halfScale data)
          + two * (delta data * lambda data)
        ≤ upper)
      targetMeaning
      combined)

section4TerminalYoungAlgebraClosed : Bool
section4TerminalYoungAlgebraClosed = true

section4ExactThreeDeltaLambdaClosed : Bool
section4ExactThreeDeltaLambdaClosed = true

section4TerminalYoungAlgebraClosedIsTrue :
  section4TerminalYoungAlgebraClosed ≡ true
section4TerminalYoungAlgebraClosedIsTrue = refl

section4ExactThreeDeltaLambdaClosedIsTrue :
  section4ExactThreeDeltaLambdaClosed ≡ true
section4ExactThreeDeltaLambdaClosedIsTrue = refl
