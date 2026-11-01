module DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineAtlasHomogeneousWeldExact where

------------------------------------------------------------------------
-- CP1 ATLAS GLUING = HOMOGENEOUS PROJECTIVE RESCALING ON OVERLAPS
--
-- The two normalized chart representatives
--
--   U0 : [1 : z]
--   U1 : [w : 1]
--
-- satisfy z*w = 1 on the overlap.  Therefore [1:z] rescales by w to [w:1].
-- This is the exact same-object weld between the atlas gluing semantics and
-- the original homogeneous-projective rescaling semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact as CP
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineHomogeneousPairExact as P1
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineAffineChartsExact as Charts
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineChartOverlapExact as Overlap

firstNormalizedOnOverlap :
  ∀ {field}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    (pair : P1.HomogeneousPair field)
    (overlap : Overlap.ChartOverlapDomain pair) →
  P1.HomogeneousPair field
firstNormalizedOnOverlap laws pair overlap =
  Charts.firstAffineNormalizedPair
    (Overlap.base laws)
    pair
    (Overlap.firstDomainFromOverlap overlap)

secondNormalizedOnOverlap :
  ∀ {field}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    (pair : P1.HomogeneousPair field)
    (overlap : Overlap.ChartOverlapDomain pair) →
  P1.HomogeneousPair field
secondNormalizedOnOverlap laws pair overlap =
  Charts.secondAffineNormalizedPair
    (Overlap.base laws)
    pair
    (Overlap.secondDomainFromOverlap overlap)

secondTimesFirstCoordinateIsOne :
  ∀ {field}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    (pair : P1.HomogeneousPair field)
    (overlap : Overlap.ChartOverlapDomain pair) →
  CP.multiply field
    (Overlap.secondOverlapCoordinate pair overlap)
    (Overlap.firstOverlapCoordinate pair overlap)
  ≡ CP.one field
secondTimesFirstCoordinateIsOne {field} laws pair overlap =
  trans
    (Overlap.multiplyCommutative laws
      (Overlap.secondOverlapCoordinate pair overlap)
      (Overlap.firstOverlapCoordinate pair overlap))
    (Overlap.chartOverlapProductIsOne laws pair overlap)

overlapNormalizedPairsRescale :
  ∀ {field}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    (pair : P1.HomogeneousPair field)
    (overlap : Overlap.ChartOverlapDomain pair) →
  CP.ProjectiveRescaling
    (P1.pairToHomogeneousLine
      (firstNormalizedOnOverlap laws pair overlap))
    (P1.pairToHomogeneousLine
      (secondNormalizedOnOverlap laws pair overlap))
overlapNormalizedPairsRescale {field} laws pair overlap = record
  { CP.scalar =
      Overlap.secondOverlapCoordinate pair overlap
  ; CP.scalarNonzero =
      Overlap.secondOverlapCoordinateNonzero laws pair overlap
  ; CP.coordinatewiseRescaling =
      Charts.consCongruence
        (sym
          (Overlap.multiplyOneRight laws
            (Overlap.secondOverlapCoordinate pair overlap)))
        (Charts.consCongruence
          (sym
            (secondTimesFirstCoordinateIsOne
              laws pair overlap))
          refl)
  }

literalProjectiveLineOverlapClassesAgree :
  ∀ {field}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    (space : CP.LiteralComplexProjectiveSpace field 1)
    (pair : P1.HomogeneousPair field)
    (overlap : Overlap.ChartOverlapDomain pair) →
  CP.classOf space
    (P1.pairToHomogeneousLine
      (firstNormalizedOnOverlap laws pair overlap))
  ≡
  CP.classOf space
    (P1.pairToHomogeneousLine
      (secondNormalizedOnOverlap laws pair overlap))
literalProjectiveLineOverlapClassesAgree laws space pair overlap =
  CP.rescalingGivesSameClass space
    (P1.pairToHomogeneousLine
      (firstNormalizedOnOverlap laws pair overlap))
    (P1.pairToHomogeneousLine
      (secondNormalizedOnOverlap laws pair overlap))
    (overlapNormalizedPairsRescale laws pair overlap)

record ProjectiveLineAtlasHomogeneousWeldBoundary : Set where
  constructor projective-line-atlas-homogeneous-weld-boundary
  field
    overlapNormalizedPairsRescalingPaid : Bool
    atlasHomogeneousSameObjectOverlapPaid : Bool
    literalProjectiveClassAgreementCompilerPaid : Bool
    actualProjectiveLineQuotientPaid : Bool
    quotientEliminatorPaid : Bool
    literalSmoothProjectiveLinePaid : Bool
    projectiveLineCohomologyPaid : Bool
    pointCycleClassPaid : Bool
    literalP1HodgeWeldPaid : Bool
    generalHodgeConjecturePaid : Bool

canonicalProjectiveLineAtlasHomogeneousWeldBoundary :
  ProjectiveLineAtlasHomogeneousWeldBoundary
canonicalProjectiveLineAtlasHomogeneousWeldBoundary =
  projective-line-atlas-homogeneous-weld-boundary
    true true true false false false false false false false
