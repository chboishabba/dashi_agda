module DASHI.Physics.Closure.NSTriadKNLuoSection4ProductClosureExact where

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
-- Prove the exact ordered-field product step combining the two Section-4
-- estimates for J11 and J12.  From
--
--   J11^2 <= delta U,
--   J12^2 <= delta L,
--
-- the theorem derives
--
--   (J11 J12)^2 <= delta^2 (U L).
--
-- If U L <= W and 0 <= delta <= 1, it further derives
--
--   (J11 J12)^2 <= delta W.
--
-- These are the algebraic steps used to turn the separate frequency bounds
-- into Luo's J1 estimate.  Neither product estimate is accepted as an input.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; subst₂)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

square : ℚ → ℚ
square value = value * value

record Section4ProductData : Set where
  constructor section4-product
  field
    J11 J12 delta upperWeight lowerWeight targetWeight : ℚ

    deltaNonnegative : 0ℚ ≤ delta
    deltaAtMostOne : delta ≤ 1ℚ
    upperWeightNonnegative : 0ℚ ≤ upperWeight
    lowerWeightNonnegative : 0ℚ ≤ lowerWeight
    targetWeightNonnegative : 0ℚ ≤ targetWeight

    J11SquaredBound :
      square J11 ≤ delta * upperWeight
    J12SquaredBound :
      square J12 ≤ delta * lowerWeight

    weightProductBound :
      upperWeight * lowerWeight ≤ targetWeight

open Section4ProductData public

deltaUpperNonnegative :
  (data : Section4ProductData) →
  0ℚ ≤ delta data * upperWeight data
deltaUpperNonnegative data =
  let
    instance
      deltaIsNonnegative = nonNegative (deltaNonnegative data)
      upperIsNonnegative = nonNegative (upperWeightNonnegative data)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg (delta data) (upperWeight data)
  in
  ℚₚ.nonNegative⁻¹ (delta data * upperWeight data)

deltaSquaredNonnegative :
  (data : Section4ProductData) →
  0ℚ ≤ square (delta data)
deltaSquaredNonnegative data = L2.squareNonnegative (delta data)

section4ProductSquaredBound :
  (data : Section4ProductData) →
  square (J11 data * J12 data)
  ≤ square (delta data)
      * (upperWeight data * lowerWeight data)
section4ProductSquaredBound data =
  let
    firstStep :
      square (J11 data) * square (J12 data)
      ≤ (delta data * upperWeight data) * square (J12 data)
    firstStep =
      let instance rightSquareIsNonnegative =
        nonNegative (L2.squareNonnegative (J12 data))
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (square (J12 data))
        (J11SquaredBound data)

    secondStep :
      (delta data * upperWeight data) * square (J12 data)
      ≤ (delta data * upperWeight data)
          * (delta data * lowerWeight data)
    secondStep =
      let instance leftFactorIsNonnegative =
        nonNegative (deltaUpperNonnegative data)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (delta data * upperWeight data)
        (J12SquaredBound data)

    leftMeaning :
      square (J11 data * J12 data)
      ≡ square (J11 data) * square (J12 data)
    leftMeaning = solve (J11 data ∷ J12 data ∷ [])

    rightMeaning :
      (delta data * upperWeight data)
        * (delta data * lowerWeight data)
      ≡ square (delta data)
          * (upperWeight data * lowerWeight data)
    rightMeaning =
      solve
        ( delta data
        ∷ upperWeight data
        ∷ lowerWeight data
        ∷ []
        )
  in
  subst₂ _≤_
    (symmetry leftMeaning)
    rightMeaning
    (ℚₚ.≤-trans firstStep secondStep)
  where
    symmetry : ∀ {left right : ℚ} → left ≡ right → right ≡ left
    symmetry refl = refl

section4ProductTargetSquaredBound :
  (data : Section4ProductData) →
  square (J11 data * J12 data)
  ≤ square (delta data) * targetWeight data
section4ProductTargetSquaredBound data =
  ℚₚ.≤-trans
    (section4ProductSquaredBound data)
    (let instance deltaSquaredIsNonnegative =
       nonNegative (deltaSquaredNonnegative data)
     in
     ℚₚ.*-monoˡ-≤-nonNeg
       (square (delta data))
       (weightProductBound data))

deltaSquaredBelowDelta :
  (data : Section4ProductData) →
  square (delta data) ≤ delta data
deltaSquaredBelowDelta data =
  let instance deltaIsNonnegative = nonNegative (deltaNonnegative data)
  in
  subst
    (λ upper → square (delta data) ≤ upper)
    (solve (delta data ∷ []))
    (ℚₚ.*-monoˡ-≤-nonNeg
      (delta data)
      (deltaAtMostOne data))

section4J1SquaredBound :
  (data : Section4ProductData) →
  square (J11 data * J12 data)
  ≤ delta data * targetWeight data
section4J1SquaredBound data =
  ℚₚ.≤-trans
    (section4ProductTargetSquaredBound data)
    (let instance targetIsNonnegative =
       nonNegative (targetWeightNonnegative data)
     in
     ℚₚ.*-monoʳ-≤-nonNeg
       (targetWeight data)
       (deltaSquaredBelowDelta data))

section4ProductClosureClosed : Bool
section4ProductClosureClosed = true

section4J1SquaredClosureClosed : Bool
section4J1SquaredClosureClosed = true

section4ProductClosureClosedIsTrue :
  section4ProductClosureClosed ≡ true
section4ProductClosureClosedIsTrue = refl

section4J1SquaredClosureClosedIsTrue :
  section4J1SquaredClosureClosed ≡ true
section4J1SquaredClosureClosedIsTrue = refl
