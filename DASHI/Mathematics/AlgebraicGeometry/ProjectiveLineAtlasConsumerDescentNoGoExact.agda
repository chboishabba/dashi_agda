module DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineAtlasConsumerDescentNoGoExact where

------------------------------------------------------------------------
-- PROJECTIVE-LINE ATLAS: CHART EQUIVALENCE IS NOT CONSUMER DESCENT
--
-- For a literal nonzero homogeneous point [1:1], the source repository
-- constructs two affine representatives of the SAME geometric overlap
-- location, related by chart-glue in the projective-line atlas setoid.
--
-- The observer "which chart did this presentation come from?" returns
-- different Boolean values on those related representatives. It therefore
-- does NOT descend to the quotient.
--
-- This is a concrete instance of the context-indexed WrongType distinction:
-- invertible/coherent transport of presentations does not make every
-- observer invariant, still less produce an algebraic cycle or a singular
-- cohomology class. It is not a proposed universal Hodge proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact as CP
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineHomogeneousPairExact as P1
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineChartOverlapExact as Overlap
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineAtlasGluingExact as Atlas

------------------------------------------------------------------------
-- The SAME literal homogeneous point has both charts available.
------------------------------------------------------------------------

unitOverlapPair :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field) →
  P1.HomogeneousPair field
unitOverlapPair {field} laws =
  P1.homogeneous-pair
    (CP.one field)
    (CP.one field)
    (CP.hereNonzero (CP.oneNonzero (Overlap.base laws)))

unitOverlap :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field) →
  Overlap.ChartOverlapDomain (unitOverlapPair laws)
unitOverlap laws =
  record
    { Overlap.firstNonzero =
        CP.oneNonzero (Overlap.base laws)
    ; Overlap.secondNonzero =
        CP.oneNonzero (Overlap.base laws)
    }

unitPointRepresentativesGlue :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field) →
  Atlas.ProjectiveLineChartEquivalent laws
    (Atlas.firstRepresentative
      (unitOverlapPair laws) (unitOverlap laws))
    (Atlas.secondRepresentative
      (unitOverlapPair laws) (unitOverlap laws))
unitPointRepresentativesGlue laws =
  Atlas.overlapRepresentativesGlue
    laws
    (unitOverlapPair laws)
    (unitOverlap laws)

------------------------------------------------------------------------
-- Presentation-only chart tags are not invariant under the actual gluing.
------------------------------------------------------------------------

chartSide :
  ∀ {field : CP.ComplexFieldPresentation} →
  Atlas.ProjectiveLineChartPoint field →
  Bool
chartSide (Atlas.firstChartPoint _) = false
chartSide (Atlas.secondChartPoint _) = true

chartSideNotInvariantAtUnitOverlap :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field) →
  chartSide
    (Atlas.firstRepresentative
      (unitOverlapPair laws) (unitOverlap laws))
  ≡
  chartSide
    (Atlas.secondRepresentative
      (unitOverlapPair laws) (unitOverlap laws)) →
  ⊥
chartSideNotInvariantAtUnitOverlap laws ()

------------------------------------------------------------------------
-- No descending Boolean consumer can agree pointwise with the chart tag.
------------------------------------------------------------------------

noChartSideDescentThroughAtlasGluing :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    (consumer : Atlas.ProjectiveLineChartPoint field → Bool) →
  ((left right : Atlas.ProjectiveLineChartPoint field) →
    Atlas.ProjectiveLineChartEquivalent laws left right →
    consumer left ≡ consumer right) →
  ((point : Atlas.ProjectiveLineChartPoint field) →
    consumer point ≡ chartSide point) →
  ⊥
noChartSideDescentThroughAtlasGluing
    laws consumer respectsChartTransport agreesWithChartSide =
  chartSideNotInvariantAtUnitOverlap laws
    (trans
      (sym
        (agreesWithChartSide
          (Atlas.firstRepresentative
            (unitOverlapPair laws) (unitOverlap laws))))
      (trans
        (respectsChartTransport
          (Atlas.firstRepresentative
            (unitOverlapPair laws) (unitOverlap laws))
          (Atlas.secondRepresentative
            (unitOverlapPair laws) (unitOverlap laws))
          (unitPointRepresentativesGlue laws))
        (agreesWithChartSide
          (Atlas.secondRepresentative
            (unitOverlapPair laws) (unitOverlap laws)))))

------------------------------------------------------------------------
-- To descend CYCLES, more is needed than this atlas's equality of points:
-- actual codimension-p algebraic subvarieties, their rational Chow relations,
-- and cycle-class compatibility on the literal smooth projective variety.
--
-- In particular a "9-sheet gluing" algebra cannot supply these automatically.
------------------------------------------------------------------------
