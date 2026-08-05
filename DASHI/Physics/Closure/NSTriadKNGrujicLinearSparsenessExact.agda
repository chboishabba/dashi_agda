module DASHI.Physics.Closure.NSTriadKNGrujicLinearSparsenessExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Zoran Grujic.
-- Title: "A geometric measure-type regularity criterion for solutions to
-- the 3D Navier-Stokes equations".
-- Journal: Nonlinearity 26 (2013), 289--296.
-- DOI: 10.1088/0951-7715/26/1/289.
-- arXiv:1111.0217; arXiv DOI: 10.48550/arXiv.1111.0217.
--
-- PURPOSE
-- Formalise the scalar measure inequality in Definition 4.1.  A super-level
-- set is linearly delta-sparse around x0 at scale r when some diameter segment
-- of length 2r has occupied length at most delta times 2r.
--
-- This module proves the exact monotonicity in delta: delta-sparseness implies
-- delta'-sparseness for every larger delta'.  It does not identify this
-- physical-space super-level-set condition with vorticity-direction coherence
-- or with a dyadic triad defect; those remain separate bridge obligations.
------------------------------------------------------------------------

open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ

record LinearSparsenessData : Set where
  constructor linear-sparseness-data
  field
    occupiedLength segmentLength delta : ℚ
    segmentLengthNonnegative : 0ℚ ≤ segmentLength
    occupiedFractionBound :
      occupiedLength ≤ delta * segmentLength

open LinearSparsenessData public

record EnlargedSparsenessParameter
  (dataSet : LinearSparsenessData) : Set where
  constructor enlarged-sparseness-parameter
  field
    largerDelta : ℚ
    deltaMonotone : delta dataSet ≤ largerDelta

open EnlargedSparsenessParameter public

linearSparsenessMonotone :
  (dataSet : LinearSparsenessData) →
  (enlarged : EnlargedSparsenessParameter dataSet) →
  occupiedLength dataSet
  ≤ largerDelta enlarged * segmentLength dataSet
linearSparsenessMonotone dataSet enlarged =
  let
    scaledDelta :
      delta dataSet * segmentLength dataSet
      ≤ largerDelta enlarged * segmentLength dataSet
    scaledDelta =
      let
        instance
          segmentIsNonnegative =
            nonNegative (segmentLengthNonnegative dataSet)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (segmentLength dataSet)
        (deltaMonotone enlarged)
  in
  ℚₚ.≤-trans
    (occupiedFractionBound dataSet)
    scaledDelta

data GeometricCriterionLane : Set where
  physicalSuperlevelSparseness : GeometricCriterionLane
  vorticityDirectionCoherence : GeometricCriterionLane
  dyadicTriadDepletion : GeometricCriterionLane
