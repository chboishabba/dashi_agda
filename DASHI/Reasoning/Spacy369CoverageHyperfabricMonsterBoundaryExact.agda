module DASHI.Reasoning.Spacy369CoverageHyperfabricMonsterBoundaryExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Algebra.Trit as Trit
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as MonsterH

------------------------------------------------------------------------
-- COVERAGE T^6 / T^9 CARRIER CROSS-POLLINATION WITH A MONSTER FIREWALL.
--
-- The coverage programme may reuse finite ternary product geometry.  A six-trit
-- coverage carrier can be encoded coordinatewise into the canonical X6=F3^6
-- Heisenberg carrier.  This is only a carrier/chart map.  It is NOT an action
-- intertwiner, central-character theorem, Stone-von Neumann identification, or
-- Monster representation promotion.
------------------------------------------------------------------------

record CoverageT6 : Set where
  constructor coverageT6
  field
    c0 c1 c2 c3 c4 c5 : Base.TriTruth

open CoverageT6 public

CoverageT9 : Set
CoverageT9 = CoverageT6 × (Base.TriTruth × (Base.TriTruth × Base.TriTruth))

triTruthToTrit : Base.TriTruth → Trit.Trit
triTruthToTrit Base.tri-low = Trit.neg
triTruthToTrit Base.tri-mid = Trit.zer
triTruthToTrit Base.tri-high = Trit.pos

coverageToX6 : CoverageT6 → MonsterH.X6
coverageToX6 coverage =
  MonsterH.x6
    (triTruthToTrit (c0 coverage))
    (triTruthToTrit (c1 coverage))
    (triTruthToTrit (c2 coverage))
    (triTruthToTrit (c3 coverage))
    (triTruthToTrit (c4 coverage))
    (triTruthToTrit (c5 coverage))

coverageCoordinate0Preserved :
  (coverage : CoverageT6) →
  MonsterH.x0 (coverageToX6 coverage) ≡ triTruthToTrit (c0 coverage)
coverageCoordinate0Preserved coverage = refl

coverageCoordinate5Preserved :
  (coverage : CoverageT6) →
  MonsterH.x5 (coverageToX6 coverage) ≡ triTruthToTrit (c5 coverage)
coverageCoordinate5Preserved coverage = refl

------------------------------------------------------------------------
-- Product-size arithmetic is retained as arithmetic only.
------------------------------------------------------------------------

coverageT6NominalStates : Nat
coverageT6NominalStates = 729

coverageT9NominalStates : Nat
coverageT9NominalStates = 19683

monsterSchrodingerBasisDimensionIs729 :
  MonsterH.schrodingerBasisDimension ≡ 729
monsterSchrodingerBasisDimensionIs729 = refl

coverageT6AndMonsterBasisShareNumber729 :
  coverageT6NominalStates ≡ MonsterH.schrodingerBasisDimension
coverageT6AndMonsterBasisShareNumber729 = refl

------------------------------------------------------------------------
-- No automatic representation promotion token exists here.
------------------------------------------------------------------------

data AutomaticCoverageMonsterRepresentationPromotion : Set where

noAutomaticCoverageMonsterRepresentationPromotion :
  AutomaticCoverageMonsterRepresentationPromotion → ⊥
noAutomaticCoverageMonsterRepresentationPromotion ()

monsterFiniteBoundary : MonsterH.FiniteHeisenbergBoundary
monsterFiniteBoundary = MonsterH.canonicalFiniteHeisenbergBoundary

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record Spacy369CoverageHyperfabricMonsterBoundary : Set where
  constructor spacy369CoverageHyperfabricMonsterBoundary
  field
    coverageMayReuseTernaryProductCarrierShape : Bool
    coverageMayReuseTernaryProductCarrierShapeIsTrue :
      coverageMayReuseTernaryProductCarrierShape ≡ true
    coverageT6CanMapCoordinatewiseIntoCanonicalX6 : Bool
    coverageT6CanMapCoordinatewiseIntoCanonicalX6IsTrue :
      coverageT6CanMapCoordinatewiseIntoCanonicalX6 ≡ true
    same729ArithmeticIdentifiesRepresentations : Bool
    same729ArithmeticIdentifiesRepresentationsIsFalse :
      same729ArithmeticIdentifiesRepresentations ≡ false
    coordinateCarrierMapIsHeisenbergActionIntertwiner : Bool
    coordinateCarrierMapIsHeisenbergActionIntertwinerIsFalse :
      coordinateCarrierMapIsHeisenbergActionIntertwiner ≡ false
    coverageHypercubeIsMonsterModule : Bool
    coverageHypercubeIsMonsterModuleIsFalse :
      coverageHypercubeIsMonsterModule ≡ false
    finiteStoneVonNeumannUniquenessFollowsFromCoverageMap : Bool
    finiteStoneVonNeumannUniquenessFollowsFromCoverageMapIsFalse :
      finiteStoneVonNeumannUniquenessFollowsFromCoverageMap ≡ false
    actualMonster3BMatricesFollowFromCoverageMap : Bool
    actualMonster3BMatricesFollowFromCoverageMapIsFalse :
      actualMonster3BMatricesFollowFromCoverageMap ≡ false
    proofShapeMayCrossDomainsWithoutRepresentationSemantics : Bool
    proofShapeMayCrossDomainsWithoutRepresentationSemanticsIsTrue :
      proofShapeMayCrossDomainsWithoutRepresentationSemantics ≡ true

canonicalSpacy369CoverageHyperfabricMonsterBoundary :
  Spacy369CoverageHyperfabricMonsterBoundary
canonicalSpacy369CoverageHyperfabricMonsterBoundary =
  spacy369CoverageHyperfabricMonsterBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
