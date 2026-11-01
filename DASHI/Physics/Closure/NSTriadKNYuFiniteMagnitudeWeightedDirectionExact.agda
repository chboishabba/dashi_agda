module DASHI.Physics.Closure.NSTriadKNYuFiniteMagnitudeWeightedDirectionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- PURPOSE
-- Formalise the ordered-algebra step from the source's Lemma 4.1,
--
--   min(a,b) directionGap <= 2 increment,
--
-- to its magnitude-weighted consequence
--
--   a^2 b directionGap <= 2 upper a increment,
--
-- under a,b <= upper.  The two possible minimum branches are proved
-- separately so no hidden min/max rewriting is required.
--
-- The continuum Euclidean triangle inequality is the producer of the branch
-- hypothesis.  Everything after that point is exact rational order algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

two : ℚ
two = Int.+ 2 / 1

weightedDirectionDefect : ℚ → ℚ → ℚ → ℚ
weightedDirectionDefect anchor other directionGap =
  anchor * anchor * other * directionGap

weightedIncrementEnvelope : ℚ → ℚ → ℚ → ℚ
weightedIncrementEnvelope upper anchor increment =
  two * upper * anchor * increment

record AnchorMinimumData : Set where
  constructor anchor-minimum-data
  field
    anchor other directionGap increment upper : ℚ
    branchMultiplierNonnegative : 0ℚ ≤ anchor * other
    upperMultiplierNonnegative : 0ℚ ≤ two * anchor * increment
    anchorDirectionBound :
      anchor * directionGap ≤ two * increment
    otherMagnitudeBound : other ≤ upper

open AnchorMinimumData public

anchorMinimumWeightedDirectionBound :
  (dataSet : AnchorMinimumData) →
  weightedDirectionDefect
    (anchor dataSet) (other dataSet) (directionGap dataSet)
  ≤ weightedIncrementEnvelope
      (upper dataSet) (anchor dataSet) (increment dataSet)
anchorMinimumWeightedDirectionBound dataSet =
  let
    firstRaw :
      (anchor dataSet * other dataSet)
        * (anchor dataSet * directionGap dataSet)
      ≤ (anchor dataSet * other dataSet)
        * (two * increment dataSet)
    firstRaw =
      let
        instance
          branchMultiplierIsNonnegative =
            nonNegative (branchMultiplierNonnegative dataSet)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (anchor dataSet * other dataSet)
        (anchorDirectionBound dataSet)

    first :
      weightedDirectionDefect
        (anchor dataSet) (other dataSet) (directionGap dataSet)
      ≤ two * anchor dataSet * other dataSet * increment dataSet
    first =
      subst
        (λ lower →
          lower ≤ two * anchor dataSet * other dataSet * increment dataSet)
        (solve
          ( anchor dataSet
          ∷ other dataSet
          ∷ directionGap dataSet
          ∷ []))
        (subst
          (λ upperValue →
            (anchor dataSet * other dataSet)
              * (anchor dataSet * directionGap dataSet)
            ≤ upperValue)
          (solve
            ( anchor dataSet
            ∷ other dataSet
            ∷ increment dataSet
            ∷ []))
          firstRaw)

    secondRaw :
      (two * anchor dataSet * increment dataSet) * other dataSet
      ≤ (two * anchor dataSet * increment dataSet) * upper dataSet
    secondRaw =
      let
        instance
          upperMultiplierIsNonnegative =
            nonNegative (upperMultiplierNonnegative dataSet)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (two * anchor dataSet * increment dataSet)
        (otherMagnitudeBound dataSet)

    second :
      two * anchor dataSet * other dataSet * increment dataSet
      ≤ weightedIncrementEnvelope
          (upper dataSet) (anchor dataSet) (increment dataSet)
    second =
      subst
        (λ lower →
          lower
          ≤ weightedIncrementEnvelope
              (upper dataSet) (anchor dataSet) (increment dataSet))
        (solve
          ( anchor dataSet
          ∷ other dataSet
          ∷ increment dataSet
          ∷ []))
        (subst
          (λ upperValue →
            (two * anchor dataSet * increment dataSet) * other dataSet
            ≤ upperValue)
          (solve
            ( upper dataSet
            ∷ anchor dataSet
            ∷ increment dataSet
            ∷ []))
          secondRaw)
  in
  ℚₚ.≤-trans first second

record OtherMinimumData : Set where
  constructor other-minimum-data
  field
    otherBranchAnchor otherBranchOther : ℚ
    otherBranchDirectionGap otherBranchIncrement otherBranchUpper : ℚ
    otherSquareAnchorNonnegative :
      0ℚ ≤ otherBranchAnchor * otherBranchAnchor
    otherUpperMultiplierNonnegative :
      0ℚ ≤ two * otherBranchAnchor * otherBranchIncrement
    otherDirectionBound :
      otherBranchOther * otherBranchDirectionGap
      ≤ two * otherBranchIncrement
    otherAnchorMagnitudeBound :
      otherBranchAnchor ≤ otherBranchUpper

open OtherMinimumData public

otherMinimumWeightedDirectionBound :
  (dataSet : OtherMinimumData) →
  weightedDirectionDefect
    (otherBranchAnchor dataSet)
    (otherBranchOther dataSet)
    (otherBranchDirectionGap dataSet)
  ≤ weightedIncrementEnvelope
      (otherBranchUpper dataSet)
      (otherBranchAnchor dataSet)
      (otherBranchIncrement dataSet)
otherMinimumWeightedDirectionBound dataSet =
  let
    firstRaw :
      (otherBranchAnchor dataSet * otherBranchAnchor dataSet)
        * (otherBranchOther dataSet * otherBranchDirectionGap dataSet)
      ≤ (otherBranchAnchor dataSet * otherBranchAnchor dataSet)
        * (two * otherBranchIncrement dataSet)
    firstRaw =
      let
        instance
          otherSquareAnchorIsNonnegative =
            nonNegative (otherSquareAnchorNonnegative dataSet)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (otherBranchAnchor dataSet * otherBranchAnchor dataSet)
        (otherDirectionBound dataSet)

    first :
      weightedDirectionDefect
        (otherBranchAnchor dataSet)
        (otherBranchOther dataSet)
        (otherBranchDirectionGap dataSet)
      ≤ two
        * otherBranchAnchor dataSet
        * otherBranchAnchor dataSet
        * otherBranchIncrement dataSet
    first =
      subst
        (λ lower →
          lower
          ≤ two
            * otherBranchAnchor dataSet
            * otherBranchAnchor dataSet
            * otherBranchIncrement dataSet)
        (solve
          ( otherBranchAnchor dataSet
          ∷ otherBranchOther dataSet
          ∷ otherBranchDirectionGap dataSet
          ∷ []))
        (subst
          (λ upperValue →
            (otherBranchAnchor dataSet * otherBranchAnchor dataSet)
              * (otherBranchOther dataSet * otherBranchDirectionGap dataSet)
            ≤ upperValue)
          (solve
            ( otherBranchAnchor dataSet
            ∷ otherBranchIncrement dataSet
            ∷ []))
          firstRaw)

    secondRaw :
      (two * otherBranchAnchor dataSet * otherBranchIncrement dataSet)
        * otherBranchAnchor dataSet
      ≤ (two * otherBranchAnchor dataSet * otherBranchIncrement dataSet)
        * otherBranchUpper dataSet
    secondRaw =
      let
        instance
          otherUpperMultiplierIsNonnegative =
            nonNegative (otherUpperMultiplierNonnegative dataSet)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (two * otherBranchAnchor dataSet * otherBranchIncrement dataSet)
        (otherAnchorMagnitudeBound dataSet)

    second :
      two
        * otherBranchAnchor dataSet
        * otherBranchAnchor dataSet
        * otherBranchIncrement dataSet
      ≤ weightedIncrementEnvelope
          (otherBranchUpper dataSet)
          (otherBranchAnchor dataSet)
          (otherBranchIncrement dataSet)
    second =
      subst
        (λ lower →
          lower
          ≤ weightedIncrementEnvelope
              (otherBranchUpper dataSet)
              (otherBranchAnchor dataSet)
              (otherBranchIncrement dataSet))
        (solve
          ( otherBranchAnchor dataSet
          ∷ otherBranchIncrement dataSet
          ∷ []))
        (subst
          (λ upperValue →
            (two * otherBranchAnchor dataSet * otherBranchIncrement dataSet)
              * otherBranchAnchor dataSet
            ≤ upperValue)
          (solve
            ( otherBranchUpper dataSet
            ∷ otherBranchAnchor dataSet
            ∷ otherBranchIncrement dataSet
            ∷ []))
          secondRaw)
  in
  ℚₚ.≤-trans first second
