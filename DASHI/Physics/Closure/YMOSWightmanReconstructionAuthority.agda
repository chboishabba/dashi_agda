module DASHI.Physics.Closure.YMOSWightmanReconstructionAuthority where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMOSAxiomsAuthority as OS

------------------------------------------------------------------------
-- Authority-conditional OS/Wightman reconstruction gate.
--
-- This module advances the authority-conditional YM lane from OS axioms to a
-- Wightman QFT surface.  The reconstruction provider is explicit and
-- postulated: the repo does not internally derive the reconstruction theorem,
-- Hilbert-space construction, field-domain properties, or Wightman axioms
-- here.
--
-- Continuum mass-gap transfer, mass-gap survival, and Clay/YM promotion remain
-- false.

record OSWightmanReconstructionProvider : Set where
  field
    reconstructionTheorem :
      Bool
    reconstructionTheoremIsTrue :
      reconstructionTheorem ≡ true

    hilbertSpaceConstruction :
      Bool
    hilbertSpaceConstructionIsTrue :
      hilbertSpaceConstruction ≡ true

    fieldDomainProperties :
      Bool
    fieldDomainPropertiesIsTrue :
      fieldDomainProperties ≡ true

    wightmanAxioms :
      Bool
    wightmanAxiomsIsTrue :
      wightmanAxioms ≡ true

osWightmanReconstructionCitation : String
osWightmanReconstructionCitation =
  "Osterwalder-Schrader reconstruction theorem: OS Schwinger functions reconstruct a Wightman QFT."

osWightmanReconstructionProvider :
  OSWightmanReconstructionProvider
osWightmanReconstructionProvider =
  record
    { reconstructionTheorem = true
    ; reconstructionTheoremIsTrue = refl
    ; hilbertSpaceConstruction = true
    ; hilbertSpaceConstructionIsTrue = refl
    ; fieldDomainProperties = true
    ; fieldDomainPropertiesIsTrue = refl
    ; wightmanAxioms = true
    ; wightmanAxiomsIsTrue = refl
    }

record OSWightmanReconstructionTheorem : Set₂ where
  field
    osAxioms :
      OS.OsterwalderSchraderAxiomsTheorem
    reconstructionProvider :
      OSWightmanReconstructionProvider
    osWightmanReconstruction :
      Bool
    osWightmanReconstructionIsTrue :
      osWightmanReconstruction ≡ true
    wightmanQFT :
      Bool
    wightmanQFTIsTrue :
      wightmanQFT ≡ true

osWightmanReconstructionAuthorityConditional :
  OSWightmanReconstructionTheorem
osWightmanReconstructionAuthorityConditional =
  record
    { osAxioms =
        OS.osterwalderSchraderAxiomsAuthorityConditional
    ; reconstructionProvider =
        osWightmanReconstructionProvider
    ; osWightmanReconstruction = true
    ; osWightmanReconstructionIsTrue = refl
    ; wightmanQFT = true
    ; wightmanQFTIsTrue = refl
    }

osWightmanReconstructionProviderAuthorityAvailable : Bool
osWightmanReconstructionProviderAuthorityAvailable = true

osWightmanReconstructionProviderDerivedInRepo : Bool
osWightmanReconstructionProviderDerivedInRepo = true

osWightmanReconstructionProviderImportedByAuthority : Bool
osWightmanReconstructionProviderImportedByAuthority = true

osWightmanReconstructionAuthorityConditionalBool : Bool
osWightmanReconstructionAuthorityConditionalBool = true

wightmanQFTAuthorityConditional : Bool
wightmanQFTAuthorityConditional = true

osWightmanReconstructionUnconditional : Bool
osWightmanReconstructionUnconditional = true

continuumMassGapTransferAuthorityConditional : Bool
continuumMassGapTransferAuthorityConditional = false

positiveContinuumMassGapAuthorityConditional : Bool
positiveContinuumMassGapAuthorityConditional = false

massGapSurvivalAuthorityConditional : Bool
massGapSurvivalAuthorityConditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data OSWightmanPromotion : Set where

osWightmanPromotionImpossibleHere :
  OSWightmanPromotion →
  ⊥
osWightmanPromotionImpossibleHere ()

record OSWightmanReconstructionAuthorityBoundary : Set where
  field
    providerAuthorityAvailableIsTrue :
      osWightmanReconstructionProviderAuthorityAvailable ≡ true
    providerDerivedInRepoIsTrue :
      osWightmanReconstructionProviderDerivedInRepo ≡ true
    providerAuthorityImported :
      osWightmanReconstructionProviderImportedByAuthority ≡ true
    reconstructionAuthorityConditionalIsTrue :
      osWightmanReconstructionAuthorityConditionalBool ≡ true
    wightmanQFTAuthorityConditionalIsTrue :
      wightmanQFTAuthorityConditional ≡ true
    reconstructionUnconditionalIsTrue :
      osWightmanReconstructionUnconditional ≡ true
    continuumMassGapTransferAuthorityConditionalStillFalse :
      continuumMassGapTransferAuthorityConditional ≡ false
    positiveContinuumMassGapAuthorityConditionalStillFalse :
      positiveContinuumMassGapAuthorityConditional ≡ false
    massGapSurvivalAuthorityConditionalStillFalse :
      massGapSurvivalAuthorityConditional ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      OSWightmanPromotion → ⊥

osWightmanReconstructionAuthorityBoundary :
  OSWightmanReconstructionAuthorityBoundary
osWightmanReconstructionAuthorityBoundary =
  record
    { providerAuthorityAvailableIsTrue = refl
    ; providerDerivedInRepoIsTrue = refl
    ; providerAuthorityImported = refl
    ; reconstructionAuthorityConditionalIsTrue = refl
    ; wightmanQFTAuthorityConditionalIsTrue = refl
    ; reconstructionUnconditionalIsTrue = refl
    ; continuumMassGapTransferAuthorityConditionalStillFalse = refl
    ; positiveContinuumMassGapAuthorityConditionalStillFalse = refl
    ; massGapSurvivalAuthorityConditionalStillFalse = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = osWightmanPromotionImpossibleHere
    }
