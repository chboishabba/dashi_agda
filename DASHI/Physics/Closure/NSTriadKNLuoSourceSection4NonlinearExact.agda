module DASHI.Physics.Closure.NSTriadKNLuoSourceSection4NonlinearExact where

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
-- Combine the separately derived source estimates for J1 and J2.  After
-- identifying one common shell scale Q and one common smallness delta, the
-- existing square inequality gives
--
--   (J1+J2)^2 <= 20992 delta^2 Q.
--
-- The constant is explicit: 2*(6400+4096)=20992.  This is the complete
-- square-safe nonlinear estimate behind Luo's (4.3)--(4.10), obtained from
-- the literal weighted J11/J12 split and the high-tail J2 criterion.  No
-- total nonlinear budget is a field.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (subst; subst₂; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHalfSplitExact as SquareSum
import DASHI.Physics.Closure.NSTriadKNLuoSourceJ11HalfRangeDerivedExact as J11
import DASHI.Physics.Closure.NSTriadKNLuoSourceJ1CriterionExact as J1
import DASHI.Physics.Closure.NSTriadKNLuoSourceJ2CriterionExact as J2

nonnegativeProduct :
  ∀ {left right : ℚ} →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
nonnegativeProduct {left} {right} leftNonnegative rightNonnegative =
  let
    instance
      leftIsNonnegative = nonNegative leftNonnegative
      rightIsNonnegative = nonNegative rightNonnegative
      productIsNonnegative = ℚₚ.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚₚ.nonNegative⁻¹ (left * right)

record SourceSection4NonlinearData (Time : Set) : Set₁ where
  field
    j1Data : J1.SourceJ1CriterionData Time
    j2Data : J2.SourceJ2CriterionData
    j2Value : ℚ

    j2ValueMeaning :
      L2.square j2Value ≡ J2.sourceJ2Square j2Data

    commonOutputScale :
      J2.outputScale j2Data ≡ J1.outputScale j1Data

    commonDelta :
      J2.delta j2Data
      ≡ J11.delta (J1.j11Data j1Data)

open SourceSection4NonlinearData public

sourceJ1 : ∀ {Time} → SourceSection4NonlinearData Time → ℚ
sourceJ1 data = J1.sourceJ1 (j1Data data)

sourceJ2 : ∀ {Time} → SourceSection4NonlinearData Time → ℚ
sourceJ2 = j2Value

commonScale : ∀ {Time} → SourceSection4NonlinearData Time → ℚ
commonScale data = J1.outputScale (j1Data data)

commonSmallness : ∀ {Time} → SourceSection4NonlinearData Time → ℚ
commonSmallness data = J11.delta (J1.j11Data (j1Data data))

sourceJ1SquareBelowScale :
  ∀ {Time} (data : SourceSection4NonlinearData Time) →
  L2.square (sourceJ1 data)
  ≤ (Int.+ 6400 / 1)
      * L2.square (commonSmallness data)
      * commonScale data
sourceJ1SquareBelowScale data =
  let
    coefficient =
      (Int.+ 6400 / 1) * L2.square (commonSmallness data)

    base = J1.sourceJ1CriterionBound (j1Data data)

    coefficientNonnegative : 0ℚ ≤ coefficient
    coefficientNonnegative =
      nonnegativeProduct
        (toWitness {a? = 0ℚ ≤? (Int.+ 6400 / 1)} _)
        (L2.squareNonnegative (commonSmallness data))

    rawScale : coefficient * 1ℚ ≤ coefficient * commonScale data
    rawScale =
      let instance coefficientIsNonnegative =
        nonNegative coefficientNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        coefficient
        (J1.outputScaleAtLeastOne (j1Data data))

    leftMeaning : coefficient * 1ℚ ≡ coefficient
    leftMeaning = solve (coefficient ∷ [])

    scaleByShell : coefficient ≤ coefficient * commonScale data
    scaleByShell =
      subst
        (λ left → left ≤ coefficient * commonScale data)
        leftMeaning
        rawScale
  in
  ℚₚ.≤-trans base scaleByShell

sourceJ2SquareBelowScale :
  ∀ {Time} (data : SourceSection4NonlinearData Time) →
  L2.square (sourceJ2 data)
  ≤ (Int.+ 4096 / 1)
      * L2.square (commonSmallness data)
      * commonScale data
sourceJ2SquareBelowScale data =
  let
    raw = J2.sourceJ2CriterionSquareBound (j2Data data)

    leftMeaning :
      J2.sourceJ2Square (j2Data data)
      ≡ L2.square (sourceJ2 data)
    leftMeaning = sym (j2ValueMeaning data)

    rightMeaning :
      J2.fourThousandNinetySix
        * L2.square (J2.delta (j2Data data))
        * J2.outputScale (j2Data data)
      ≡ (Int.+ 4096 / 1)
        * L2.square (commonSmallness data)
        * commonScale data
    rightMeaning
      rewrite commonDelta data
            | commonOutputScale data = refl
  in
  subst₂ _≤_ leftMeaning rightMeaning raw

sourceSection4NonlinearSquareBound :
  ∀ {Time} (data : SourceSection4NonlinearData Time) →
  L2.square (sourceJ1 data + sourceJ2 data)
  ≤ (Int.+ 20992 / 1)
      * L2.square (commonSmallness data)
      * commonScale data
sourceSection4NonlinearSquareBound data =
  let
    algebra =
      SquareSum.squareOfSumBelowTwiceSquares
        (sourceJ1 data)
        (sourceJ2 data)

    component :
      L2.square (sourceJ1 data) + L2.square (sourceJ2 data)
      ≤ (Int.+ 6400 / 1)
          * L2.square (commonSmallness data)
          * commonScale data
        + (Int.+ 4096 / 1)
          * L2.square (commonSmallness data)
          * commonScale data
    component =
      ℚₚ.+-mono-≤
        (sourceJ1SquareBelowScale data)
        (sourceJ2SquareBelowScale data)

    scaled :
      SquareSum.two
        * (L2.square (sourceJ1 data) + L2.square (sourceJ2 data))
      ≤ SquareSum.two
        * ( (Int.+ 6400 / 1)
              * L2.square (commonSmallness data)
              * commonScale data
          + (Int.+ 4096 / 1)
              * L2.square (commonSmallness data)
              * commonScale data)
    scaled =
      let instance twoIsNonnegative =
        nonNegative SquareSum.twoNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg SquareSum.two component

    targetMeaning :
      SquareSum.two
        * ( (Int.+ 6400 / 1)
              * L2.square (commonSmallness data)
              * commonScale data
          + (Int.+ 4096 / 1)
              * L2.square (commonSmallness data)
              * commonScale data)
      ≡ (Int.+ 20992 / 1)
          * L2.square (commonSmallness data)
          * commonScale data
    targetMeaning =
      solve
        ( L2.square (commonSmallness data)
        ∷ commonScale data
        ∷ []
        )
  in
  ℚₚ.≤-trans algebra
    (subst
      (λ upper →
        SquareSum.two
          * (L2.square (sourceJ1 data) + L2.square (sourceJ2 data))
        ≤ upper)
      targetMeaning
      scaled)
