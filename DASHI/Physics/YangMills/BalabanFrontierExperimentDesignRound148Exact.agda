{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFrontierExperimentDesignRound148Exact where

------------------------------------------------------------------------
-- ROUND148: EXPERIMENT-DESIGN COORDINATES FOR THE LIVE BALABAN FRONTIER
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Core.ExperimentalCoordinateDesignExact as Design
import DASHI.Physics.Foundations.GRQFTExperimentDesignCrossPollinationExact as GRQFT
import DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact as R146

data BalabanFrontierCoordinate : Set where
  a1CouplingHistoryResidual
  a2CouplingHistoryResidual
  densityPotentialResidual
  componentD1Residual
  stressSumResidual
  metricDomainMargin
  schwingerPairingResidual
  cutoffSystematic
  finiteVolumeSystematic
  discretizationSystematic
  : BalabanFrontierCoordinate

coordinateRole : BalabanFrontierCoordinate → Design.CoordinateRole
coordinateRole a1CouplingHistoryResidual = Design.derivedDiscriminator
coordinateRole a2CouplingHistoryResidual = Design.derivedDiscriminator
coordinateRole densityPotentialResidual = Design.derivedDiscriminator
coordinateRole componentD1Residual = Design.derivedDiscriminator
coordinateRole stressSumResidual = Design.derivedDiscriminator
coordinateRole metricDomainMargin = Design.measuredObservable
coordinateRole schwingerPairingResidual = Design.derivedDiscriminator
coordinateRole cutoffSystematic = Design.nuisanceCoordinate
coordinateRole finiteVolumeSystematic = Design.nuisanceCoordinate
coordinateRole discretizationSystematic = Design.nuisanceCoordinate

coordinateTargetsLeaf : BalabanFrontierCoordinate → R146.BalabanFrontierLeaf
coordinateTargetsLeaf a1CouplingHistoryResidual = R146.a1CouplingToBetaHistory
coordinateTargetsLeaf a2CouplingHistoryResidual = R146.a2CouplingToBetaHistory
coordinateTargetsLeaf densityPotentialResidual = R146.combinedRGStateToBC1Potential
coordinateTargetsLeaf componentD1Residual = R146.componentLocalizedD1ToPhysicalD1
coordinateTargetsLeaf stressSumResidual = R146.stressInsertionEqualsPhysicalD1Sum
coordinateTargetsLeaf metricDomainMargin = R146.metricPerturbationAdmission
coordinateTargetsLeaf schwingerPairingResidual = R146.cmp119FiniteMeasureSchwingerEndpoint
coordinateTargetsLeaf cutoffSystematic = R146.cmp119FiniteMeasureSchwingerEndpoint
coordinateTargetsLeaf finiteVolumeSystematic = R146.cmp119FiniteMeasureSchwingerEndpoint
coordinateTargetsLeaf discretizationSystematic = R146.componentLocalizedD1ToPhysicalD1

-- Search measurements are useful when they discriminate two candidate source
-- realizations which the current proof-language observer has not separated.
record FrontierCoordinateDiscrimination : Set₁ where
  field
    CandidateRealization : Set
    currentObservation : CandidateRealization → Bool
    coordinateValue : BalabanFrontierCoordinate → CandidateRealization → Bool
    coordinate : BalabanFrontierCoordinate
    left right : CandidateRealization
    currentlyCollapsed : currentObservation left ≡ currentObservation right
    coordinateSeparates :
      coordinateValue coordinate left ≡ coordinateValue coordinate right → ⊥

open FrontierCoordinateDiscrimination public

record BalabanFrontierExperimentBoundary : Set where
  constructor balabanFrontierExperimentBoundary
  field
    derivedResidualIsAutomaticallyPhysicalObservable : Bool
    derivedResidualIsAutomaticallyPhysicalObservableIsFalse :
      derivedResidualIsAutomaticallyPhysicalObservable ≡ false
    numericalResidualZeroIsAutomaticallyFormalSourceIdentity : Bool
    numericalResidualZeroIsAutomaticallyFormalSourceIdentityIsFalse :
      numericalResidualZeroIsAutomaticallyFormalSourceIdentity ≡ false
    nuisanceCoordinateMayBeDroppedWithoutValidation : Bool
    nuisanceCoordinateMayBeDroppedWithoutValidationIsFalse :
      nuisanceCoordinateMayBeDroppedWithoutValidation ≡ false
    addedDiscriminatorCanIncreaseInformationalResolution : Bool
    addedDiscriminatorCanIncreaseInformationalResolutionIsTrue :
      addedDiscriminatorCanIncreaseInformationalResolution ≡ true

canonicalBalabanFrontierExperimentBoundary : BalabanFrontierExperimentBoundary
canonicalBalabanFrontierExperimentBoundary =
  balabanFrontierExperimentBoundary false refl false refl false refl true refl

grqftExperimentDesignBoundaryReused : GRQFT.GRQFTExperimentDesignBoundary
grqftExperimentDesignBoundaryReused = GRQFT.canonicalGRQFTExperimentDesignBoundary

balabanFrontierExperimentDesignLevel : ProofLevel
balabanFrontierExperimentDesignLevel = machineChecked
