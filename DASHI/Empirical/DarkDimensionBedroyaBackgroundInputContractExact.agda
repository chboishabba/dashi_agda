module DASHI.Empirical.DarkDimensionBedroyaBackgroundInputContractExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Empirical.DarkDimensionBedroyaBackgroundReconstructionExact as Background
import DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact as Manifest

record BedroyaBackgroundInputStatus : Set where
  constructor bedroyaBackgroundInputStatus
  field
    backgroundEquationsLocated : Bool
    cBestFitLocated : Bool
    cPrimeBestFitLocated : Bool
    simulationStartLocated : Bool
    phiInitialLocated : Bool
    paperDMNormalizationLocated : Bool
    exactH0SameFitLocated : Bool
    exactOmegaR0Located : Bool
    exactOmegaB0SameFitLocated : Bool
    sampledDMNormalizationMappingLocated : Bool
    v0NormalizationLocated : Bool
    initialScalarVelocityConventionLocated : Bool
    exactRDragSameFitLocated : Bool
    completeBackgroundInputManifestLocated : Bool

open BedroyaBackgroundInputStatus public

canonicalBedroyaBackgroundInputStatus : BedroyaBackgroundInputStatus
canonicalBedroyaBackgroundInputStatus =
  bedroyaBackgroundInputStatus
    true true true true true true
    false false false false false false false false

partialInputSurfacePaid :
  paperDMNormalizationLocated canonicalBedroyaBackgroundInputStatus ≡ true
partialInputSurfacePaid = refl

initialVelocityConventionStillOpen :
  initialScalarVelocityConventionLocated canonicalBedroyaBackgroundInputStatus ≡ false
initialVelocityConventionStillOpen = refl

exactRDragSameFitStillOpen :
  exactRDragSameFitLocated canonicalBedroyaBackgroundInputStatus ≡ false
exactRDragSameFitStillOpen = refl

completeBackgroundInputStillOpen :
  completeBackgroundInputManifestLocated canonicalBedroyaBackgroundInputStatus ≡ false
completeBackgroundInputStillOpen = refl

data HubbleFrozenMeansExactZeroInitialVelocity : Set where

data PosteriorCoordinateDisplayedMeansExactSameFitInput : Set where

data BackgroundHVectorPaysBAOWithoutRDrag : Set where

hubbleFrozenDoesNotManufactureExactInitialVelocity :
  HubbleFrozenMeansExactZeroInitialVelocity → ⊥
hubbleFrozenDoesNotManufactureExactInitialVelocity ()

displayedPosteriorDoesNotManufactureExactSameFitInput :
  PosteriorCoordinateDisplayedMeansExactSameFitInput → ⊥
displayedPosteriorDoesNotManufactureExactSameFitInput ()

backgroundHVectorDoesNotPayBAOWithoutRDrag :
  BackgroundHVectorPaysBAOWithoutRDrag → ⊥
backgroundHVectorDoesNotPayBAOWithoutRDrag ()

backgroundEquationsRemainLocated :
  Background.friedmannEquationLocated
    Background.canonicalBedroyaBackgroundReconstructionStatus
  ≡ true
backgroundEquationsRemainLocated = refl

manifestPaperDMIdentityRemainsPaid :
  Manifest.m0n0ToRhoDM0PaperIdentityLocated
    Manifest.canonicalBedroyaParameterManifestStatus
  ≡ true
manifestPaperDMIdentityRemainsPaid = Manifest.paperDMNormalizationIdentityPaid
