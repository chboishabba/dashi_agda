module DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineAffineChartsExact where

------------------------------------------------------------------------
-- LITERAL AFFINE CHART NORMALIZATION FOR CP^1
--
-- On z0 != 0, [z0:z1] rescales to [1:z1/z0].
-- On z1 != 0, [z0:z1] rescales to [z0/z1:1].
--
-- This is genuine projective geometry below the quotient boundary: both
-- normalizations are constructed from the exact inverse laws already proved
-- sufficient for projective rescaling.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact as CP
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineHomogeneousPairExact as P1

consCongruence :
  ∀ {A : Set} {x x' : A} {xs xs' : Agda.Builtin.List.List A} →
  x ≡ x' →
  xs ≡ xs' →
  x ∷ xs ≡ x' ∷ xs'
consCongruence refl refl = refl

record FirstAffineChartDomain
    {field : CP.ComplexFieldPresentation}
    (pair : P1.HomogeneousPair field) : Set where
  field
    firstNonzero :
      CP.nonzero field (P1.first pair)

open FirstAffineChartDomain public

record SecondAffineChartDomain
    {field : CP.ComplexFieldPresentation}
    (pair : P1.HomogeneousPair field) : Set where
  field
    secondNonzero :
      CP.nonzero field (P1.second pair)

open SecondAffineChartDomain public

firstAffineCoordinate :
  ∀ {field}
    (pair : P1.HomogeneousPair field) →
  FirstAffineChartDomain pair →
  CP.Complex field
firstAffineCoordinate {field} pair domain =
  CP.multiply field
    (CP.inverse field
      (P1.first pair)
      (firstNonzero domain))
    (P1.second pair)

firstAffineNormalizedPair :
  ∀ {field}
    (laws : CP.ProjectiveMultiplicativeLaws field)
    (pair : P1.HomogeneousPair field) →
  FirstAffineChartDomain pair →
  P1.HomogeneousPair field
firstAffineNormalizedPair {field} laws pair domain =
  P1.homogeneous-pair
    (CP.one field)
    (firstAffineCoordinate pair domain)
    (CP.hereNonzero (CP.oneNonzero laws))

firstAffineNormalizationRescaling :
  ∀ {field}
    (laws : CP.ProjectiveMultiplicativeLaws field)
    (pair : P1.HomogeneousPair field)
    (domain : FirstAffineChartDomain pair) →
  CP.ProjectiveRescaling
    (P1.pairToHomogeneousLine pair)
    (P1.pairToHomogeneousLine
      (firstAffineNormalizedPair laws pair domain))
firstAffineNormalizationRescaling {field} laws pair domain = record
  { CP.scalar =
      CP.inverse field
        (P1.first pair)
        (firstNonzero domain)
  ; CP.scalarNonzero =
      CP.inverseNonzero laws (firstNonzero domain)
  ; CP.coordinatewiseRescaling =
      consCongruence
        (CP.inverseLeft laws
          (P1.first pair)
          (firstNonzero domain))
        (consCongruence refl refl)
  }

secondAffineCoordinate :
  ∀ {field}
    (pair : P1.HomogeneousPair field) →
  SecondAffineChartDomain pair →
  CP.Complex field
secondAffineCoordinate {field} pair domain =
  CP.multiply field
    (CP.inverse field
      (P1.second pair)
      (secondNonzero domain))
    (P1.first pair)

secondAffineNormalizedPair :
  ∀ {field}
    (laws : CP.ProjectiveMultiplicativeLaws field)
    (pair : P1.HomogeneousPair field) →
  SecondAffineChartDomain pair →
  P1.HomogeneousPair field
secondAffineNormalizedPair {field} laws pair domain =
  P1.homogeneous-pair
    (secondAffineCoordinate pair domain)
    (CP.one field)
    (CP.thereNonzero (CP.hereNonzero (CP.oneNonzero laws)))

secondAffineNormalizationRescaling :
  ∀ {field}
    (laws : CP.ProjectiveMultiplicativeLaws field)
    (pair : P1.HomogeneousPair field)
    (domain : SecondAffineChartDomain pair) →
  CP.ProjectiveRescaling
    (P1.pairToHomogeneousLine pair)
    (P1.pairToHomogeneousLine
      (secondAffineNormalizedPair laws pair domain))
secondAffineNormalizationRescaling {field} laws pair domain = record
  { CP.scalar =
      CP.inverse field
        (P1.second pair)
        (secondNonzero domain)
  ; CP.scalarNonzero =
      CP.inverseNonzero laws (secondNonzero domain)
  ; CP.coordinatewiseRescaling =
      consCongruence
        refl
        (consCongruence
          (CP.inverseLeft laws
            (P1.second pair)
            (secondNonzero domain))
          refl)
  }

data AffineChartChoice
    {field : CP.ComplexFieldPresentation}
    (pair : P1.HomogeneousPair field) : Set where
  firstChart :
    FirstAffineChartDomain pair →
    AffineChartChoice pair

  secondChart :
    SecondAffineChartDomain pair →
    AffineChartChoice pair

homogeneousPairCoveredByAffineCharts :
  ∀ {field}
    (pair : P1.HomogeneousPair field) →
  AffineChartChoice pair
homogeneousPairCoveredByAffineCharts
    (P1.homogeneous-pair first second
      (CP.hereNonzero firstNonzero)) =
  firstChart record
    { firstNonzero = firstNonzero }
homogeneousPairCoveredByAffineCharts
    (P1.homogeneous-pair first second
      (CP.thereNonzero (CP.hereNonzero secondNonzero))) =
  secondChart record
    { secondNonzero = secondNonzero }

record ProjectiveLineAffineChartsBoundary : Set where
  constructor projective-line-affine-charts-boundary
  field
    firstAffineChartCoordinatePaid : Bool
    secondAffineChartCoordinatePaid : Bool
    firstAffineChartNormalizationPaid : Bool
    secondAffineChartNormalizationPaid : Bool
    normalizationRescalingProofsPaid : Bool
    chartCoverFromNonzeroPairPaid : Bool
    chartOverlapTransitionPaid : Bool
    globalProjectiveLineQuotientPaid : Bool
    projectiveLineCohomologyPaid : Bool
    pointDivisorCycleClassPaid : Bool
    literalP1HodgeWeldPaid : Bool
    generalHodgeConjecturePaid : Bool

canonicalProjectiveLineAffineChartsBoundary :
  ProjectiveLineAffineChartsBoundary
canonicalProjectiveLineAffineChartsBoundary =
  projective-line-affine-charts-boundary
    true true true true true true false false false false false false
