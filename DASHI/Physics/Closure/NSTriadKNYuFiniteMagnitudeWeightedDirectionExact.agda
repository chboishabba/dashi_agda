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
    anchor other directionGap increment upper : ℚ
    squareAnchorNonnegative : 0ℚ ≤ anchor * anchor
    upperMultiplierNonnegative : 0ℚ ≤ two * anchor * increment
    otherDirectionBound :
      other * directionGap ≤ two * increment
    anchorMagnitudeBound : anchor ≤ upper

open OtherMinimumData public

otherMinimumWeightedDirectionBound :
  (dataSet : OtherMinimumData) →
  weightedDirectionDefect
    (anchor dataSet) (other dataSet) (directionGap dataSet)
  ≤ weightedIncrementEnvelope
      (upper dataSet) (anchor dataSet) (increment dataSet)
otherMinimumWeightedDirectionBound dataSet =
  let
    firstRaw :
      (anchor dataSet * anchor dataSet)
        * (other dataSet * directionGap dataSet)
      ≤ (anchor dataSet * anchor dataSet)
        * (two * increment dataSet)
    firstRaw =
      let
        instance
          squareAnchorIsNonnegative =
            nonNegative (squareAnchorNonnegative dataSet)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (anchor dataSet * anchor dataSet)
        (otherDirectionBound dataSet)

    first :
      weightedDirectionDefect
        (anchor dataSet) (other dataSet) (directionGap dataSet)
      ≤ two * anchor dataSet * anchor dataSet * increment dataSet
    first =
      subst
        (λ lower →
          lower ≤ two * anchor dataSet * anchor dataSet * increment dataSet)
        (solve
          ( anchor dataSet
          ∷ other dataSet
          ∷ directionGap dataSet
          ∷ []))
        (subst
          (λ upperValue →
            (anchor dataSet * anchor dataSet)
              * (other dataSet * directionGap dataSet)
            ≤ upperValue)
          (solve
            ( anchor dataSet
            ∷ increment dataSet
            ∷ []))
          firstRaw)

    secondRaw :
      (two * anchor dataSet * increment dataSet) * anchor dataSet
      ≤ (two * anchor dataSet * increment dataSet) * upper dataSet
    secondRaw =
      let
        instance
          upperMultiplierIsNonnegative =
            nonNegative (upperMultiplierNonnegative dataSet)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (two * anchor dataSet * increment dataSet)
        (anchorMagnitudeBound dataSet)

    second :
      two * anchor dataSet * anchor dataSet * increment dataSet
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
          ∷ increment dataSet
          ∷ []))
        (subst
          (λ upperValue →
            (two * anchor dataSet * increment dataSet) * anchor dataSet
            ≤ upperValue)
          (solve
            ( upper dataSet
            ∷ anchor dataSet
            ∷ increment dataSet
            ∷ []))
          secondRaw)
  in
  ℚₚ.≤-trans first second
