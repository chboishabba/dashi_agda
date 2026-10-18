module DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineAtlasGluingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.QuotientSetoidSurface as Quotient
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact as CP
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineHomogeneousPairExact as P1
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineChartOverlapExact as Overlap

data ProjectiveLineChartPoint
    (field : CP.ComplexFieldPresentation) : Set where
  firstChartPoint :
    CP.Complex field →
    ProjectiveLineChartPoint field

  secondChartPoint :
    CP.Complex field →
    ProjectiveLineChartPoint field

data ProjectiveLineChartEquivalent
    {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field) :
    ProjectiveLineChartPoint field →
    ProjectiveLineChartPoint field →
    Set where

  chart-refl :
    ∀ point →
    ProjectiveLineChartEquivalent laws point point

  chart-glue :
    ∀ {z w} →
    CP.nonzero field z →
    CP.nonzero field w →
    CP.multiply field z w ≡ CP.one field →
    ProjectiveLineChartEquivalent laws
      (firstChartPoint z)
      (secondChartPoint w)

  chart-sym :
    ∀ {left right} →
    ProjectiveLineChartEquivalent laws left right →
    ProjectiveLineChartEquivalent laws right left

  chart-trans :
    ∀ {first second third} →
    ProjectiveLineChartEquivalent laws first second →
    ProjectiveLineChartEquivalent laws second third →
    ProjectiveLineChartEquivalent laws first third

chartEquivalence :
  ∀ {field}
    (laws : Overlap.ProjectiveOverlapFieldLaws field) →
  Quotient.IsEquivalence
    (ProjectiveLineChartEquivalent laws)
chartEquivalence laws = record
  { Quotient.refl≈ = chart-refl
  ; Quotient.sym≈ = chart-sym
  ; Quotient.trans≈ = chart-trans
  }

projectiveLineAtlasSetoid :
  ∀ {field} →
  (laws : Overlap.ProjectiveOverlapFieldLaws field) →
  Quotient.SetoidSurface _ _
projectiveLineAtlasSetoid {field} laws = record
  { Quotient.Carrier =
      ProjectiveLineChartPoint field
  ; Quotient._≈_ =
      ProjectiveLineChartEquivalent laws
  ; Quotient.isEquivalence =
      chartEquivalence laws
  }

firstRepresentative :
  ∀ {field}
    (pair : P1.HomogeneousPair field) →
  (overlap : Overlap.ChartOverlapDomain pair) →
  ProjectiveLineChartPoint field
firstRepresentative pair overlap =
  firstChartPoint
    (Overlap.firstOverlapCoordinate pair overlap)

secondRepresentative :
  ∀ {field}
    (pair : P1.HomogeneousPair field) →
  (overlap : Overlap.ChartOverlapDomain pair) →
  ProjectiveLineChartPoint field
secondRepresentative pair overlap =
  secondChartPoint
    (Overlap.secondOverlapCoordinate pair overlap)

overlapRepresentativesGlue :
  ∀ {field}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    (pair : P1.HomogeneousPair field)
    (overlap : Overlap.ChartOverlapDomain pair) →
  ProjectiveLineChartEquivalent laws
    (firstRepresentative pair overlap)
    (secondRepresentative pair overlap)
overlapRepresentativesGlue laws pair overlap =
  chart-glue
    (Overlap.firstOverlapCoordinateNonzero
      laws pair overlap)
    (Overlap.secondOverlapCoordinateNonzero
      laws pair overlap)
    (Overlap.chartOverlapProductIsOne
      laws pair overlap)

record ProjectiveLineAtlasGluingBoundary : Set where
  constructor projective-line-atlas-gluing-boundary
  field
    chartPointCarrierPaid : Bool
    literalAtlasGluingRelationPaid : Bool
    gluingEquivalenceSetoidPaid : Bool
    overlapRepresentativesGluePaid : Bool
    quotientCarrierInhabitedPaid : Bool
    quotientEliminatorPaid : Bool
    literalProjectiveLineGeometryPaid : Bool
    projectiveLineCohomologyPaid : Bool
    pointCycleClassPaid : Bool
    generalHodgeConjecturePaid : Bool

canonicalProjectiveLineAtlasGluingBoundary :
  ProjectiveLineAtlasGluingBoundary
canonicalProjectiveLineAtlasGluingBoundary =
  projective-line-atlas-gluing-boundary
    true true true true false false false false false false
