module DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineChartOverlapExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact as CP
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineHomogeneousPairExact as P1
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineAffineChartsExact as Charts

record ProjectiveOverlapFieldLaws
    (field : CP.ComplexFieldPresentation) : Set₁ where
  field
    base :
      CP.ProjectiveMultiplicativeLaws field

    multiplyCommutative :
      ∀ x y →
      CP.multiply field x y
      ≡ CP.multiply field y x

open ProjectiveOverlapFieldLaws public

multiplyOneRight :
  ∀ {field} →
  (laws : ProjectiveOverlapFieldLaws field) →
  (x : CP.Complex field) →
  CP.multiply field x (CP.one field) ≡ x
multiplyOneRight {field} laws x =
  trans
    (multiplyCommutative laws x (CP.one field))
    (CP.multiplyOneLeft (base laws) x)

inverseRight :
  ∀ {field} →
  (laws : ProjectiveOverlapFieldLaws field) →
  (x : CP.Complex field) →
  (xNonzero : CP.nonzero field x) →
  CP.multiply field x (CP.inverse field x xNonzero)
  ≡ CP.one field
inverseRight {field} laws x xNonzero =
  trans
    (multiplyCommutative laws
      x
      (CP.inverse field x xNonzero))
    (CP.inverseLeft (base laws) x xNonzero)

record ChartOverlapDomain
    {field : CP.ComplexFieldPresentation}
    (pair : P1.HomogeneousPair field) : Set where
  field
    firstNonzero :
      CP.nonzero field (P1.first pair)

    secondNonzero :
      CP.nonzero field (P1.second pair)

open ChartOverlapDomain public

firstDomainFromOverlap :
  ∀ {field pair} →
  ChartOverlapDomain {field} pair →
  Charts.FirstAffineChartDomain pair
firstDomainFromOverlap overlap = record
  { Charts.firstNonzero = firstNonzero overlap }

secondDomainFromOverlap :
  ∀ {field pair} →
  ChartOverlapDomain {field} pair →
  Charts.SecondAffineChartDomain pair
secondDomainFromOverlap overlap = record
  { Charts.secondNonzero = secondNonzero overlap }

firstOverlapCoordinate :
  ∀ {field}
    (pair : P1.HomogeneousPair field) →
  ChartOverlapDomain pair →
  CP.Complex field
firstOverlapCoordinate pair overlap =
  Charts.firstAffineCoordinate
    pair
    (firstDomainFromOverlap overlap)

secondOverlapCoordinate :
  ∀ {field}
    (pair : P1.HomogeneousPair field) →
  ChartOverlapDomain pair →
  CP.Complex field
secondOverlapCoordinate pair overlap =
  Charts.secondAffineCoordinate
    pair
    (secondDomainFromOverlap overlap)

firstOverlapCoordinateNonzero :
  ∀ {field}
    (laws : ProjectiveOverlapFieldLaws field)
    (pair : P1.HomogeneousPair field)
    (overlap : ChartOverlapDomain pair) →
  CP.nonzero field
    (firstOverlapCoordinate pair overlap)
firstOverlapCoordinateNonzero laws pair overlap =
  CP.multiplyNonzero (base laws)
    (CP.inverseNonzero (base laws)
      (firstNonzero overlap))
    (secondNonzero overlap)

secondOverlapCoordinateNonzero :
  ∀ {field}
    (laws : ProjectiveOverlapFieldLaws field)
    (pair : P1.HomogeneousPair field)
    (overlap : ChartOverlapDomain pair) →
  CP.nonzero field
    (secondOverlapCoordinate pair overlap)
secondOverlapCoordinateNonzero laws pair overlap =
  CP.multiplyNonzero (base laws)
    (CP.inverseNonzero (base laws)
      (secondNonzero overlap))
    (firstNonzero overlap)

chartOverlapProductIsOne :
  ∀ {field}
    (laws : ProjectiveOverlapFieldLaws field)
    (pair : P1.HomogeneousPair field)
    (overlap : ChartOverlapDomain pair) →
  CP.multiply field
    (firstOverlapCoordinate pair overlap)
    (secondOverlapCoordinate pair overlap)
  ≡ CP.one field
chartOverlapProductIsOne {field} laws pair overlap =
  trans
    (CP.multiplyAssociative (base laws)
      (CP.inverse field
        (P1.first pair)
        (firstNonzero overlap))
      (P1.second pair)
      (CP.multiply field
        (CP.inverse field
          (P1.second pair)
          (secondNonzero overlap))
        (P1.first pair)))
    (trans
      (cong
        (CP.multiply field
          (CP.inverse field
            (P1.first pair)
            (firstNonzero overlap)))
        (trans
          (sym
            (CP.multiplyAssociative (base laws)
              (P1.second pair)
              (CP.inverse field
                (P1.second pair)
                (secondNonzero overlap))
              (P1.first pair)))
          (trans
            (cong
              (λ coefficient →
                CP.multiply field coefficient
                  (P1.first pair))
              (inverseRight laws
                (P1.second pair)
                (secondNonzero overlap)))
            (CP.multiplyOneLeft (base laws)
              (P1.first pair)))))
      (CP.inverseLeft (base laws)
        (P1.first pair)
        (firstNonzero overlap)))

record ProjectiveLineChartOverlapBoundary : Set where
  constructor projective-line-chart-overlap-boundary
  field
    overlapDomainPaid : Bool
    overlapCoordinatesNonzeroPaid : Bool
    chartOverlapProductIsOnePaid : Bool
    inversionTransitionSemanticsPaid : Bool
    globalProjectiveLineQuotientPaid : Bool
    projectiveLineCohomologyPaid : Bool
    pointCycleClassPaid : Bool
    literalP1HodgeWeldPaid : Bool
    generalHodgeConjecturePaid : Bool

canonicalProjectiveLineChartOverlapBoundary :
  ProjectiveLineChartOverlapBoundary
canonicalProjectiveLineChartOverlapBoundary =
  projective-line-chart-overlap-boundary
    true true true true false false false false false
