module DASHI.Biology.BrainITFunctionalClusterTransferExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BrainITSourceBoundaryExact as Source

------------------------------------------------------------------------
-- Paper-facing architectural coordinates.
-- These are metadata / typed commitments, not a reimplementation of Brain-IT.

reportedVoxelCount : Nat
reportedVoxelCount = 40000

reportedFunctionalClusterCount : Nat
reportedFunctionalClusterCount = 128

record FunctionalClusterArchitecture : Set where
  constructor functionalClusterArchitecture
  field
    voxelCount : Nat
    functionalClusterCount : Nat
    sharedAcrossSubjects : Bool
    sharedClusterWeights : Bool
    clusterInteractionTransformer : Bool
    semanticAndLowLevelBranches : Bool

open FunctionalClusterArchitecture public

canonicalBrainITArchitecture : FunctionalClusterArchitecture
canonicalBrainITArchitecture =
  functionalClusterArchitecture
    reportedVoxelCount
    reportedFunctionalClusterCount
    true
    true
    true
    true

canonicalVoxelCount : voxelCount canonicalBrainITArchitecture ≡ 40000
canonicalVoxelCount = refl

canonicalClusterCount :
  functionalClusterCount canonicalBrainITArchitecture ≡ 128
canonicalClusterCount = refl

canonicalSharedClusterWeights :
  sharedClusterWeights canonicalBrainITArchitecture ≡ true
canonicalSharedClusterWeights = refl

------------------------------------------------------------------------
-- Transfer-learning regime reported by the Brain-IT paper.

record TransferRegime : Set where
  constructor transferRegime
  field
    newSubjectMinutes : Nat
    fullBaselineMinutes : Nat
    usesSharedFunctionalClusters : Bool
    usesSharedParameters : Bool
    sourceReportsComparablePerformance : Bool

open TransferRegime public

brainITOneHourTransfer : TransferRegime
brainITOneHourTransfer = transferRegime 60 2400 true true true

oneHourTransferComparableToFortyHourBaseline :
  sourceReportsComparablePerformance brainITOneHourTransfer ≡ true
oneHourTransferComparableToFortyHourBaseline = refl

oneHourIsSixtyMinutes : newSubjectMinutes brainITOneHourTransfer ≡ 60
oneHourIsSixtyMinutes = refl

fortyHoursIsTwentyFourHundredMinutes :
  fullBaselineMinutes brainITOneHourTransfer ≡ 2400
fortyHoursIsTwentyFourHundredMinutes = refl

record TransferInterpretationBoundary : Set where
  constructor transferInterpretationBoundary
  field
    sharedClustersEliminateSubjectSpecificCalibration : Bool
    sharedClustersEliminateSubjectSpecificCalibrationIsFalse :
      sharedClustersEliminateSubjectSpecificCalibration ≡ false

    transferResultIsUniversalMindDecoder : Bool
    transferResultIsUniversalMindDecoderIsFalse :
      transferResultIsUniversalMindDecoder ≡ false

    sourceBoundaryRetained :
      Source.arbitraryThoughtReadingSupported
        Source.canonicalBrainITSourceBoundary
      ≡ false

canonicalTransferInterpretationBoundary : TransferInterpretationBoundary
canonicalTransferInterpretationBoundary =
  transferInterpretationBoundary false refl false refl refl
