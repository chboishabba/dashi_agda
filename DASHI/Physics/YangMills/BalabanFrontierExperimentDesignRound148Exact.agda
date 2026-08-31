{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFrontierExperimentDesignRound148Exact where

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
  densityActionResidual
  round108PotentialMatchResidual
  combinedRGDensityStateResidual
  combinedRGStatePotentialResidual
  physicalD1ChainRuleResidual
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
coordinateRole densityActionResidual = Design.derivedDiscriminator
coordinateRole round108PotentialMatchResidual = Design.derivedDiscriminator
coordinateRole combinedRGDensityStateResidual = Design.derivedDiscriminator
coordinateRole combinedRGStatePotentialResidual = Design.derivedDiscriminator
coordinateRole physicalD1ChainRuleResidual = Design.derivedDiscriminator
coordinateRole stressSumResidual = Design.derivedDiscriminator
coordinateRole metricDomainMargin = Design.measuredObservable
coordinateRole schwingerPairingResidual = Design.derivedDiscriminator
coordinateRole cutoffSystematic = Design.nuisanceCoordinate
coordinateRole finiteVolumeSystematic = Design.nuisanceCoordinate
coordinateRole discretizationSystematic = Design.nuisanceCoordinate

coordinateTargetsLeaf : BalabanFrontierCoordinate → R146.BalabanFrontierLeaf
coordinateTargetsLeaf a1CouplingHistoryResidual = R146.a1CouplingToBetaHistory
coordinateTargetsLeaf a2CouplingHistoryResidual = R146.a2CouplingToBetaHistory
coordinateTargetsLeaf densityActionResidual = R146.densityActionRealization
coordinateTargetsLeaf round108PotentialMatchResidual = R146.round108SelectedPotentialMatchesBC1
coordinateTargetsLeaf combinedRGDensityStateResidual = R146.densityToCombinedRGState
coordinateTargetsLeaf combinedRGStatePotentialResidual = R146.combinedRGStateToBC1Potential
coordinateTargetsLeaf physicalD1ChainRuleResidual = R146.physicalCompositeD1ChainRule
coordinateTargetsLeaf stressSumResidual = R146.stressInsertionEqualsPhysicalD1Sum
coordinateTargetsLeaf metricDomainMargin = R146.metricPerturbationAdmission
coordinateTargetsLeaf schwingerPairingResidual = R146.cmp119FiniteMeasureSchwingerEndpoint
coordinateTargetsLeaf cutoffSystematic = R146.cmp119FiniteMeasureSchwingerEndpoint
coordinateTargetsLeaf finiteVolumeSystematic = R146.cmp119FiniteMeasureSchwingerEndpoint
coordinateTargetsLeaf discretizationSystematic = R146.physicalCompositeD1ChainRule

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
