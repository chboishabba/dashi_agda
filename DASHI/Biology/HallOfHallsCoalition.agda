module DASHI.Biology.HallOfHallsCoalition where

open import DASHI.Core.Prelude

import DASHI.Biology.RecursiveSpherePerforation as Perforation
import DASHI.Biology.NestedApertureVisibility as Visibility
import DASHI.Biology.LogPolarRetinotopyBridge as Retinotopy
import DASHI.Biology.FiniteCoalitionConstruction as PriorCoalition

------------------------------------------------------------------------
-- Finite coalition construction for the hall-of-halls scene.
--
-- The integrated candidate jointly carries architecture, recursive cavity
-- genealogy, viewpoint-dependent aperture reach, and log-polar-compatible
-- projective regularity.  The theorem is a finite construction result, not a
-- claim that the remembered scene has been uniquely recovered.

data HallCoalitionCandidate : Set where
  geometryOnlyCandidate : HallCoalitionCandidate
  architectureOnlyCandidate : HallCoalitionCandidate
  projectionOnlyCandidate : HallCoalitionCandidate
  integratedHallCandidate : HallCoalitionCandidate

ordinaryArchitectureDefect : HallCoalitionCandidate → Nat
ordinaryArchitectureDefect geometryOnlyCandidate = 1
ordinaryArchitectureDefect architectureOnlyCandidate = 0
ordinaryArchitectureDefect projectionOnlyCandidate = 2
ordinaryArchitectureDefect integratedHallCandidate = 3

internalGenerativeDefect : HallCoalitionCandidate → Nat
internalGenerativeDefect geometryOnlyCandidate = 2
internalGenerativeDefect architectureOnlyCandidate = 3
internalGenerativeDefect projectionOnlyCandidate = 2
internalGenerativeDefect integratedHallCandidate = 0

reachPenalty : HallCoalitionCandidate → Nat
reachPenalty geometryOnlyCandidate = 2
reachPenalty architectureOnlyCandidate = 2
reachPenalty projectionOnlyCandidate = 1
reachPenalty integratedHallCandidate = 0

depthPenalty : HallCoalitionCandidate → Nat
depthPenalty geometryOnlyCandidate = 2
depthPenalty architectureOnlyCandidate = 1
depthPenalty projectionOnlyCandidate = 2
depthPenalty integratedHallCandidate = 0

hallObjective : HallCoalitionCandidate → Nat
hallObjective c =
  internalGenerativeDefect c
  + reachPenalty c
  + depthPenalty c

geometryOnlyObjectiveIsSix :
  hallObjective geometryOnlyCandidate ≡ 6
geometryOnlyObjectiveIsSix = refl

architectureOnlyObjectiveIsSix :
  hallObjective architectureOnlyCandidate ≡ 6
architectureOnlyObjectiveIsSix = refl

projectionOnlyObjectiveIsFive :
  hallObjective projectionOnlyCandidate ≡ 5
projectionOnlyObjectiveIsFive = refl

integratedHallObjectiveIsZero :
  hallObjective integratedHallCandidate ≡ 0
integratedHallObjectiveIsZero = refl

selectedHallCoalition : HallCoalitionCandidate
selectedHallCoalition = integratedHallCandidate

selectedHallCoalitionMinimal :
  (c : HallCoalitionCandidate) →
  hallObjective selectedHallCoalition ≤ hallObjective c
selectedHallCoalitionMinimal geometryOnlyCandidate = z≤n
selectedHallCoalitionMinimal architectureOnlyCandidate = z≤n
selectedHallCoalitionMinimal projectionOnlyCandidate = z≤n
selectedHallCoalitionMinimal integratedHallCandidate = ≤-refl

hallCoalitionUpdate :
  HallCoalitionCandidate → HallCoalitionCandidate
hallCoalitionUpdate geometryOnlyCandidate = integratedHallCandidate
hallCoalitionUpdate architectureOnlyCandidate = integratedHallCandidate
hallCoalitionUpdate projectionOnlyCandidate = integratedHallCandidate
hallCoalitionUpdate integratedHallCandidate = integratedHallCandidate

selectedHallCoalitionIsFixedPoint :
  hallCoalitionUpdate selectedHallCoalition
  ≡
  selectedHallCoalition
selectedHallCoalitionIsFixedPoint = refl

highOrdinaryDefectLowInternalDefect :
  ordinaryArchitectureDefect integratedHallCandidate ≡ 3
  ×
  internalGenerativeDefect integratedHallCandidate ≡ 0
highOrdinaryDefectLowInternalDefect = refl , refl

record HallOfHallsCoalitionWitness : Set₁ where
  constructor hallOfHallsCoalitionWitness
  field
    candidate : HallCoalitionCandidate
    minimal :
      (c : HallCoalitionCandidate) →
      hallObjective candidate ≤ hallObjective c
    recurrent :
      hallCoalitionUpdate candidate ≡ candidate
    gapBranch :
      Perforation.ThreeWayGapBranch
    viewpointContrast :
      Visibility.ApertureVisibilityContrast
    sharedCorticalProjection :
      Retinotopy.corticalProjection Retinotopy.squareWorldGenerator
      ≡
      Retinotopy.corticalProjection Retinotopy.apollonianWorldGenerator
    priorCoalitionBoundary :
      PriorCoalition.CoalitionConstructionBoundary

open HallOfHallsCoalitionWitness public

canonicalHallOfHallsCoalitionWitness :
  HallOfHallsCoalitionWitness
canonicalHallOfHallsCoalitionWitness =
  hallOfHallsCoalitionWitness
    selectedHallCoalition
    selectedHallCoalitionMinimal
    selectedHallCoalitionIsFixedPoint
    Perforation.canonicalThreeWayGapBranch
    Visibility.canonicalApertureVisibilityContrast
    Retinotopy.squareAndApollonianCanShareCorticalProjection
    PriorCoalition.canonicalCoalitionConstructionBoundary

record HallCoalitionBoundary : Set where
  constructor hallCoalitionBoundary
  field
    finiteMinimumRecoversHistoricalVision : Bool
    finiteMinimumRecoversHistoricalVisionIsFalse :
      finiteMinimumRecoversHistoricalVision ≡ false

    internalCoherenceImpliesPhysicalBuildability : Bool
    internalCoherenceImpliesPhysicalBuildabilityIsFalse :
      internalCoherenceImpliesPhysicalBuildability ≡ false

open HallCoalitionBoundary public

canonicalHallCoalitionBoundary : HallCoalitionBoundary
canonicalHallCoalitionBoundary =
  hallCoalitionBoundary false refl false refl
