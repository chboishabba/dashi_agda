module DASHI.Empirical.DarkDimensionBedroyaBackgroundInputContractExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Empirical.DarkDimensionBedroyaBackgroundReconstructionExact as Background
import DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact as Manifest

------------------------------------------------------------------------
-- BEDROYA BACKGROUND INPUT COMPLETENESS
--
-- Source-paid equations and qualitative early-time freezing do not manufacture
-- the exact numerical initial-value manifest used by the authors' CLASS run.
------------------------------------------------------------------------

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
    completeBackgroundInputManifestLocated : Bool

open BedroyaBackgroundInputStatus public

canonicalBedroyaBackgroundInputStatus : BedroyaBackgroundInputStatus
canonicalBedroyaBackgroundInputStatus =
  bedroyaBackgroundInputStatus
    true true true true true true
    false false false false false false false

partialInputSurfacePaid :
  paperDMNormalizationLocated canonicalBedroyaBackgroundInputStatus ≡ true
partialInputSurfacePaid = Manifest.paperDMNormalizationIdentityPaid

initialVelocityConventionStillOpen :
  initialScalarVelocityConventionLocated canonicalBedroyaBackgroundInputStatus ≡ false
initialVelocityConventionStillOpen = refl

completeBackgroundInputStillOpen :
  completeBackgroundInputManifestLocated canonicalBedroyaBackgroundInputStatus ≡ false
completeBackgroundInputStillOpen = refl

data HubbleFrozenMeansExactZeroInitialVelocity : Set where

data PosteriorCoordinateDisplayedMeansExactSameFitInput : Set where

hubbleFrozenDoesNotManufactureExactInitialVelocity :
  HubbleFrozenMeansExactZeroInitialVelocity → ⊥
hubbleFrozenDoesNotManufactureExactInitialVelocity ()

displayedPosteriorDoesNotManufactureExactSameFitInput :
  PosteriorCoordinateDisplayedMeansExactSameFitInput → ⊥
displayedPosteriorDoesNotManufactureExactSameFitInput ()

backgroundEquationsRemainLocated :
  Background.friedmannEquationLocated
    Background.canonicalBedroyaBackgroundReconstructionStatus
  ≡ true
backgroundEquationsRemainLocated = refl
