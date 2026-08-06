module DASHI.Physics.Closure.NSTriadKNLuoMagnitudeWeightedDirectionIncrementExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
-- Status: arXiv preprint, submitted 25 June 2026.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Yu's magnitude-weighted direction estimate is implemented in a stronger
-- radical-free squared form.  For unit directions xi, eta and ordered
-- amplitudes 0 <= a <= b,
--
--   |a xi - b eta|^2
--     = (b-a)^2 + a b |xi-eta|^2,
--
-- hence
--
--   a^2 |xi-eta|^2 <= |a xi - b eta|^2.
--
-- This avoids differentiating the singular normalized direction map and
-- shows exactly how the magnitude weights neutralize its zero-set problem.
-- The source's unsquared constant-two estimate follows conservatively, while
-- the checked ordered squared identity has constant one.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical

vectorDifference : Gram.Vec3 → Gram.Vec3 → Gram.Vec3
vectorDifference left right =
  Gram.vec3
    (Gram.x left - Gram.x right)
    (Gram.y left - Gram.y right)
    (Gram.z left - Gram.z right)

scaledDifferenceNormExpansion :
  ∀ a b left right →
  Gram.normSquared
    (vectorDifference
      (Physical.scaleVec3 a left)
      (Physical.scaleVec3 b right))
  ≡
  L2.square a * Gram.normSquared left
  + L2.square b * Gram.normSquared right
  - (2 * a * b * Gram.dot left right)
scaledDifferenceNormExpansion a b left right =
  solve
    ( a ∷ b
    ∷ Gram.x left ∷ Gram.y left ∷ Gram.z left
    ∷ Gram.x right ∷ Gram.y right ∷ Gram.z right
    ∷ [])

directionDifferenceNormExpansion :
  ∀ left right →
  Gram.normSquared (vectorDifference left right)
  ≡
  Gram.normSquared left + Gram.normSquared right
  - (2 * Gram.dot left right)
directionDifferenceNormExpansion left right =
  solve
    ( Gram.x left ∷ Gram.y left ∷ Gram.z left
    ∷ Gram.x right ∷ Gram.y right ∷ Gram.z right
    ∷ [])

record OrderedDirectionIncrement : Set where
  constructor orderedDirectionIncrement
  field
    smallerAmplitude largerAmplitude : ℚ
    smallerNonnegative : 0ℚ ≤ smallerAmplitude
    largerNonnegative : 0ℚ ≤ largerAmplitude
    smallerBelowLarger : smallerAmplitude ≤ largerAmplitude
    directions : Gram.UnitDirectionPair

open OrderedDirectionIncrement public

smallerDirection : OrderedDirectionIncrement → Gram.Vec3
smallerDirection dataSet = Gram.left (directions dataSet)

largerDirection : OrderedDirectionIncrement → Gram.Vec3
largerDirection dataSet = Gram.right (directions dataSet)

smallerVorticity : OrderedDirectionIncrement → Gram.Vec3
smallerVorticity dataSet =
  Physical.scaleVec3
    (smallerAmplitude dataSet)
    (smallerDirection dataSet)

largerVorticity : OrderedDirectionIncrement → Gram.Vec3
largerVorticity dataSet =
  Physical.scaleVec3
    (largerAmplitude dataSet)
    (largerDirection dataSet)

vorticityIncrementSquared : OrderedDirectionIncrement → ℚ
vorticityIncrementSquared dataSet =
  Gram.normSquared
    (vectorDifference
      (smallerVorticity dataSet)
      (largerVorticity dataSet))

directionIncrementSquared : OrderedDirectionIncrement → ℚ
directionIncrementSquared dataSet =
  Gram.normSquared
    (vectorDifference
      (smallerDirection dataSet)
      (largerDirection dataSet))

weightedDirectionIncrement : OrderedDirectionIncrement → ℚ
weightedDirectionIncrement dataSet =
  L2.square (smallerAmplitude dataSet)
  * directionIncrementSquared dataSet

exactAmplitudeDirectionDecomposition :
  ∀ dataSet →
  vorticityIncrementSquared dataSet
  ≡
  L2.square
    (largerAmplitude dataSet - smallerAmplitude dataSet)
  +
  smallerAmplitude dataSet * largerAmplitude dataSet
    * directionIncrementSquared dataSet
exactAmplitudeDirectionDecomposition dataSet =
  let
    a = smallerAmplitude dataSet
    b = largerAmplitude dataSet
    xi = smallerDirection dataSet
    eta = largerDirection dataSet

    expanded = scaledDifferenceNormExpansion a b xi eta

    normalized :
      L2.square a * Gram.normSquared xi
      + L2.square b * Gram.normSquared eta
      - (2 * a * b * Gram.dot xi eta)
      ≡
      L2.square (b - a)
      + a * b * Gram.normSquared (vectorDifference xi eta)
    normalized
      rewrite Gram.leftUnit (directions dataSet)
            | Gram.rightUnit (directions dataSet)
            | directionDifferenceNormExpansion xi eta =
      solve (a ∷ b ∷ Gram.dot xi eta ∷ [])
  in
  trans expanded normalized

amplitudeProductNonnegative :
  ∀ dataSet →
  0ℚ ≤ smallerAmplitude dataSet * largerAmplitude dataSet
amplitudeProductNonnegative dataSet =
  let
    instance
      smallerNN = nonNegative (smallerNonnegative dataSet)
      largerNN = nonNegative (largerNonnegative dataSet)
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (smallerAmplitude dataSet)
          (largerAmplitude dataSet)
  in
  ℚₚ.nonNegative⁻¹
    (smallerAmplitude dataSet * largerAmplitude dataSet)

smallerSquareBelowAmplitudeProduct :
  ∀ dataSet →
  L2.square (smallerAmplitude dataSet)
  ≤ smallerAmplitude dataSet * largerAmplitude dataSet
smallerSquareBelowAmplitudeProduct dataSet =
  ℚₚ.*-monoˡ-≤-nonNeg
    (smallerAmplitude dataSet)
    (smallerBelowLarger dataSet)
  where
  instance
    smallerNN = nonNegative (smallerNonnegative dataSet)

weightedDirectionBelowProductDirection :
  ∀ dataSet →
  weightedDirectionIncrement dataSet
  ≤
  smallerAmplitude dataSet * largerAmplitude dataSet
    * directionIncrementSquared dataSet
weightedDirectionBelowProductDirection dataSet =
  L2.nonnegativeProductMonotone
    (L2.squareNonnegative (smallerAmplitude dataSet))
    (Gram.normSquaredNonnegative
      (vectorDifference
        (smallerDirection dataSet)
        (largerDirection dataSet)))
    (amplitudeProductNonnegative dataSet)
    (Gram.normSquaredNonnegative
      (vectorDifference
        (smallerDirection dataSet)
        (largerDirection dataSet)))
    (smallerSquareBelowAmplitudeProduct dataSet)
    ℚₚ.≤-refl

productDirectionBelowVorticityIncrement :
  ∀ dataSet →
  smallerAmplitude dataSet * largerAmplitude dataSet
    * directionIncrementSquared dataSet
  ≤ vorticityIncrementSquared dataSet
productDirectionBelowVorticityIncrement dataSet =
  let
    amplitudeGapSquare =
      L2.square
        (largerAmplitude dataSet - smallerAmplitude dataSet)
    directionPart =
      smallerAmplitude dataSet * largerAmplitude dataSet
      * directionIncrementSquared dataSet

    addGap :
      0ℚ + directionPart
      ≤ amplitudeGapSquare + directionPart
    addGap =
      ℚₚ.+-mono-≤
        (L2.squareNonnegative
          (largerAmplitude dataSet - smallerAmplitude dataSet))
        ℚₚ.≤-refl

    normalizedLeft : 0ℚ + directionPart ≡ directionPart
    normalizedLeft = solve (directionPart ∷ [])

    toDecomposition :
      directionPart
      ≤ amplitudeGapSquare + directionPart
    toDecomposition =
      subst
        (λ left → left ≤ amplitudeGapSquare + directionPart)
        normalizedLeft
        addGap
  in
  subst
    (λ upper → directionPart ≤ upper)
    (sym (exactAmplitudeDirectionDecomposition dataSet))
    toDecomposition

magnitudeWeightedDirectionIncrementBound :
  ∀ dataSet →
  weightedDirectionIncrement dataSet
  ≤ vorticityIncrementSquared dataSet
magnitudeWeightedDirectionIncrementBound dataSet =
  ℚₚ.≤-trans
    (weightedDirectionBelowProductDirection dataSet)
    (productDirectionBelowVorticityIncrement dataSet)

record MagnitudeDirectionAuthorityBoundary : Set where
  constructor magnitudeDirectionAuthorityBoundary
  field
    exactOrderedDecompositionProved : Set
    squaredMagnitudeWeightedBoundProved : Set
    continuumDifferenceQuotientEstimateProved : Set

canonicalMagnitudeDirectionAuthorityBoundary :
  MagnitudeDirectionAuthorityBoundary
canonicalMagnitudeDirectionAuthorityBoundary =
  magnitudeDirectionAuthorityBoundary ⊤ ⊤ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
