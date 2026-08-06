module DASHI.Visualisation.SliceObjectiveExact where

open import DASHI.Core.Prelude

import DASHI.Visualisation.CoarseSliceSearchExact as Search

------------------------------------------------------------------------
-- Activity, local mixture entropy, class coverage, spatial variation, and
-- boundary richness are separate score components.  The finite table gives a
-- concrete counterexample to selecting a plane by activity alone.

meanActivity : Search.PlaneCandidate → Nat
meanActivity Search.axisCandidate = 7
meanActivity Search.broadAngledCandidate = 10
meanActivity Search.compactIslandCandidate = 12

entropyDiversity : Search.PlaneCandidate → Nat
entropyDiversity Search.axisCandidate = 4
entropyDiversity Search.broadAngledCandidate = 8
entropyDiversity Search.compactIslandCandidate = 1

classCoverage : Search.PlaneCandidate → Nat
classCoverage Search.axisCandidate = 3
classCoverage Search.broadAngledCandidate = 5
classCoverage Search.compactIslandCandidate = 1

activeAreaCoverage : Search.PlaneCandidate → Nat
activeAreaCoverage Search.axisCandidate = 8
activeAreaCoverage Search.broadAngledCandidate = 9
activeAreaCoverage Search.compactIslandCandidate = 2

spatialVariation : Search.PlaneCandidate → Nat
spatialVariation Search.axisCandidate = 5
spatialVariation Search.broadAngledCandidate = 8
spatialVariation Search.compactIslandCandidate = 1

boundaryRichness : Search.PlaneCandidate → Nat
boundaryRichness Search.axisCandidate = 3
boundaryRichness Search.broadAngledCandidate = 7
boundaryRichness Search.compactIslandCandidate = 1

mixtureVolume : Search.PlaneCandidate → Nat
mixtureVolume Search.axisCandidate = 2
mixtureVolume Search.broadAngledCandidate = 6
mixtureVolume Search.compactIslandCandidate = 0

regionBalance : Search.PlaneCandidate → Nat
regionBalance Search.axisCandidate = 4
regionBalance Search.broadAngledCandidate = 7
regionBalance Search.compactIslandCandidate = 1

combinedObjective : Search.PlaneCandidate → Nat
combinedObjective candidate =
  2 * meanActivity candidate
  +
  entropyDiversity candidate
  +
  2 * activeAreaCoverage candidate
  +
  spatialVariation candidate
  +
  boundaryRichness candidate
  +
  classCoverage candidate
  +
  mixtureVolume candidate
  +
  regionBalance candidate

activityOnlyWinner : Search.PlaneCandidate
activityOnlyWinner = Search.compactIslandCandidate

combinedWinner : Search.PlaneCandidate
combinedWinner = Search.broadAngledCandidate

activityOnlyWinnerScore :
  meanActivity activityOnlyWinner ≡ 12
activityOnlyWinnerScore = refl

combinedWinnerScore :
  combinedObjective combinedWinner ≡ 79
combinedWinnerScore = refl

compactCombinedScore :
  combinedObjective Search.compactIslandCandidate ≡ 33
compactCombinedScore = refl

activityAndDiversitySelectDifferentPlanes :
  activityOnlyWinner ≡ combinedWinner → ⊥
activityAndDiversitySelectDifferentPlanes ()

------------------------------------------------------------------------
-- Area and normalisation metadata.

data BasisGeometry : Set where
  orthonormalBasis : BasisGeometry
  skewBasis : BasisGeometry

areaScale : BasisGeometry → Nat
areaScale orthonormalBasis = 1
areaScale skewBasis = 4

data NormalisationScope : Set where
  sharedAtlasNormalisation : NormalisationScope
  perSliceNormalisation : NormalisationScope

record SliceAtlasConfiguration : Set where
  constructor sliceAtlasConfiguration
  field
    normalisationScope : NormalisationScope
    sharedColourBasis : Bool
    sharedActivityReference : Bool
    candidateCount : Nat

open SliceAtlasConfiguration public

canonicalAtlasConfiguration : SliceAtlasConfiguration
canonicalAtlasConfiguration =
  sliceAtlasConfiguration
    sharedAtlasNormalisation
    true
    true
    3

atlasUsesSharedReference :
  normalisationScope canonicalAtlasConfiguration
  ≡
  sharedAtlasNormalisation
atlasUsesSharedReference = refl

------------------------------------------------------------------------
-- The slice is an observation map with three independently typed losses.

data ObservationLoss : Set where
  restrictionLoss : ObservationLoss
  colourProjectionLoss : ObservationLoss
  normalisationLoss : ObservationLoss

data PlaneControl : Set where
  offsetControl : PlaneControl
  orientationControl : PlaneControl
  scoreWeightControl : PlaneControl
  colourBasisControl : PlaneControl

record SliceSearchResult : Set where
  constructor sliceSearchResult
  field
    selectedPlane : Search.PlaneCandidate
    selectedScore : Nat
    atlasConfiguration : SliceAtlasConfiguration
    retainedLossOne : ObservationLoss
    retainedLossTwo : ObservationLoss
    retainedLossThree : ObservationLoss

canonicalSliceSearchResult : SliceSearchResult
canonicalSliceSearchResult =
  sliceSearchResult
    combinedWinner
    79
    canonicalAtlasConfiguration
    restrictionLoss
    colourProjectionLoss
    normalisationLoss

record SliceObjectiveBoundary : Set where
  constructor sliceObjectiveBoundary
  field
    highestActivityPlaneIsHighestDiversityPlane : Bool
    highestActivityPlaneIsHighestDiversityPlaneIsFalse :
      highestActivityPlaneIsHighestDiversityPlane ≡ false

    finiteSampledWinnerIsGlobalContinuousOptimum : Bool
    finiteSampledWinnerIsGlobalContinuousOptimumIsFalse :
      finiteSampledWinnerIsGlobalContinuousOptimum ≡ false

    bestVisualSliceIsPrivilegedOntology : Bool
    bestVisualSliceIsPrivilegedOntologyIsFalse :
      bestVisualSliceIsPrivilegedOntology ≡ false

    perSliceNormalisationPreservesAtlasComparability : Bool
    perSliceNormalisationPreservesAtlasComparabilityIsFalse :
      perSliceNormalisationPreservesAtlasComparability ≡ false

open SliceObjectiveBoundary public

canonicalSliceObjectiveBoundary : SliceObjectiveBoundary
canonicalSliceObjectiveBoundary =
  sliceObjectiveBoundary
    false refl
    false refl
    false refl
    false refl
