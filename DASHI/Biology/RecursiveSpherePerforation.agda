module DASHI.Biology.RecursiveSpherePerforation where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Finite recursive sphere-perforation model.
--
-- The solid is represented by a finite material count together with cavity
-- count and recursion depth.  This does not approximate Euclidean volume; it
-- supplies exact monotonicity, candidate-selection, gap-shape, and branching
-- theorems for the architectural generator described in the attached tranche.
--
-- Source-facing reference:
-- M. Borkovec, W. de Paris, and R. Peikert,
-- "The Fractal Dimension of the Apollonian Sphere Packing",
-- DOI 10.1142/S0218348X94000739.

record FiniteSolid : Set where
  constructor finiteSolid
  field
    materialCells : Nat
    cavityCount : Nat
    recursionDepth : Nat

open FiniteSolid public

subtractVoid : Nat → FiniteSolid → FiniteSolid
subtractVoid removed (finiteSolid material cavities depth) =
  finiteSolid
    (material ∸ removed)
    (suc cavities)
    (suc depth)

roomStage0 : FiniteSolid
roomStage0 = finiteSolid 12 0 0

roomStage1 : FiniteSolid
roomStage1 = subtractVoid 4 roomStage0

roomStage2 : FiniteSolid
roomStage2 = subtractVoid 3 roomStage1

roomStage3 : FiniteSolid
roomStage3 = subtractVoid 2 roomStage2

stage0MaterialIsTwelve : materialCells roomStage0 ≡ 12
stage0MaterialIsTwelve = refl

stage1MaterialIsEight : materialCells roomStage1 ≡ 8
stage1MaterialIsEight = refl

stage2MaterialIsFive : materialCells roomStage2 ≡ 5
stage2MaterialIsFive = refl

stage3MaterialIsThree : materialCells roomStage3 ≡ 3
stage3MaterialIsThree = refl

stage1IsContainedByStage0 :
  materialCells roomStage1 ≤ materialCells roomStage0
stage1IsContainedByStage0 =
  s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

stage2IsContainedByStage1 :
  materialCells roomStage2 ≤ materialCells roomStage1
stage2IsContainedByStage1 =
  s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

stage3IsContainedByStage2 :
  materialCells roomStage3 ≤ materialCells roomStage2
stage3IsContainedByStage2 =
  s≤s (s≤s (s≤s z≤n))

------------------------------------------------------------------------
-- Square and tangency seeds have different residual gap signatures.

data SeedGeometry : Set where
  squareGridSeed : SeedGeometry
  tangentTripleSeed : SeedGeometry
  hybridSquareTangencySeed : SeedGeometry

data GapShape : Set where
  curvedSquareGap : GapShape
  curvedTriangularGap : GapShape
  mixedCurvilinearGap : GapShape

dominantGapShape : SeedGeometry → GapShape
dominantGapShape squareGridSeed = curvedSquareGap
dominantGapShape tangentTripleSeed = curvedTriangularGap
dominantGapShape hybridSquareTangencySeed = mixedCurvilinearGap

squareSeedHasCurvedSquareGap :
  dominantGapShape squareGridSeed ≡ curvedSquareGap
squareSeedHasCurvedSquareGap = refl

tangentSeedHasCurvedTriangularGap :
  dominantGapShape tangentTripleSeed ≡ curvedTriangularGap
tangentSeedHasCurvedTriangularGap = refl

hybridSeedRetainsBothGapFamilies :
  dominantGapShape hybridSquareTangencySeed ≡ mixedCurvilinearGap
hybridSeedRetainsBothGapFamilies = refl

------------------------------------------------------------------------
-- Regularity is typed by source: periodic, tangency, recursion, projection,
-- or developmental law.

record RegularityProfile : Set where
  constructor regularityProfile
  field
    periodicRegularity : Bool
    tangencyRegularity : Bool
    recursiveRegularity : Bool
    projectiveRegularity : Bool
    developmentalRegularity : Bool

open RegularityProfile public

squareRegularity : RegularityProfile
squareRegularity =
  regularityProfile true false true true false

apollonianRegularity : RegularityProfile
apollonianRegularity =
  regularityProfile false true true true false

hybridRegularity : RegularityProfile
hybridRegularity =
  regularityProfile true true true true true

hybridIsPeriodicAndTangencyRegular :
  periodicRegularity hybridRegularity ≡ true
  ×
  tangencyRegularity hybridRegularity ≡ true
hybridIsPeriodicAndTangencyRegular = refl , refl

apollonianCanBeRegularWithoutPeriodicity :
  tangencyRegularity apollonianRegularity ≡ true
  ×
  periodicRegularity apollonianRegularity ≡ false
apollonianCanBeRegularWithoutPeriodicity = refl , refl

------------------------------------------------------------------------
-- Exact finite maximal-clearance selection.

data CandidateSite : Set where
  leftResidualSite : CandidateSite
  centreResidualSite : CandidateSite
  rightResidualSite : CandidateSite

clearance : CandidateSite → Nat
clearance leftResidualSite = 2
clearance centreResidualSite = 4
clearance rightResidualSite = 3

selectedResidualSite : CandidateSite
selectedResidualSite = centreResidualSite

selectedResidualSiteIsMaximal :
  (c : CandidateSite) →
  clearance c ≤ clearance selectedResidualSite
selectedResidualSiteIsMaximal leftResidualSite =
  s≤s (s≤s z≤n)
selectedResidualSiteIsMaximal centreResidualSite = ≤-refl
selectedResidualSiteIsMaximal rightResidualSite =
  s≤s (s≤s (s≤s z≤n))

------------------------------------------------------------------------
-- Recursive gap insertion generates a branching dual graph.

data ResidualGap : Set where
  rootCurvedGap : ResidualGap
  leftChildGap : ResidualGap
  middleChildGap : ResidualGap
  rightChildGap : ResidualGap

data GapChild : ResidualGap → ResidualGap → Set where
  rootToLeft : GapChild rootCurvedGap leftChildGap
  rootToMiddle : GapChild rootCurvedGap middleChildGap
  rootToRight : GapChild rootCurvedGap rightChildGap

record ThreeWayGapBranch : Set where
  constructor threeWayGapBranch
  field
    leftBranch : GapChild rootCurvedGap leftChildGap
    middleBranch : GapChild rootCurvedGap middleChildGap
    rightBranch : GapChild rootCurvedGap rightChildGap

open ThreeWayGapBranch public

canonicalThreeWayGapBranch : ThreeWayGapBranch
canonicalThreeWayGapBranch =
  threeWayGapBranch rootToLeft rootToMiddle rootToRight

record RecursivePerforationBoundary : Set where
  constructor recursivePerforationBoundary
  field
    finiteCellCountIsEuclideanVolume : Bool
    finiteCellCountIsEuclideanVolumeIsFalse :
      finiteCellCountIsEuclideanVolume ≡ false

    memorySelectsUniqueGenerator : Bool
    memorySelectsUniqueGeneratorIsFalse :
      memorySelectsUniqueGenerator ≡ false

    inverseApollonianIsEstablished : Bool
    inverseApollonianIsEstablishedIsFalse :
      inverseApollonianIsEstablished ≡ false

open RecursivePerforationBoundary public

canonicalRecursivePerforationBoundary : RecursivePerforationBoundary
canonicalRecursivePerforationBoundary =
  recursivePerforationBoundary false refl false refl false refl
