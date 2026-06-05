module DASHI.Physics.Closure.YMLatticeMassGapAuthority where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMSmallFieldSurvivalAuthority as SmallField

------------------------------------------------------------------------
-- Authority-conditional lattice mass-gap gate.
--
-- This module advances the authority-conditional lane one step beyond
-- small-field survival.  It records the transfer-matrix compatibility and
-- spectral-gap package needed to turn anisotropic KP plus surviving
-- small-field bounds into a positive lattice mass gap.
--
-- The provider is authority-backed: the repo does not internally derive the
-- transfer spectral gap here.  The authority lane can consume the package,
-- while the unconditional repo lane remains blocked at the four analytic
-- transfer-matrix slots below.

record TemporalTransferMatrixSpatialBlockingCompatibility : Set where
  constructor mkTemporalTransferMatrixSpatialBlockingCompatibility
  field
    temporalTransferMatrixCompatibleWithSpatialBlocking :
      Bool
    temporalTransferMatrixCompatibleWithSpatialBlockingIsTrue :
      temporalTransferMatrixCompatibleWithSpatialBlocking ≡ true

record TransferReflectionPositivity : Set where
  constructor mkTransferReflectionPositivity
  field
    transferReflectionPositivity :
      Bool
    transferReflectionPositivityIsTrue :
      transferReflectionPositivity ≡ true

record TransferSpectralGap : Set where
  constructor mkTransferSpectralGap
  field
    transferSpectralGap :
      Bool
    transferSpectralGapIsTrue :
      transferSpectralGap ≡ true

record PositiveLatticeMassGapExtraction : Set where
  constructor mkPositiveLatticeMassGapExtraction
  field
    positiveLatticeMassGapExtraction :
      Bool
    positiveLatticeMassGapExtractionIsTrue :
      positiveLatticeMassGapExtraction ≡ true

record LatticeMassGapAnalyticPackage : Set where
  constructor mkLatticeMassGapAnalyticPackage
  field
    transferMatrixSpatialBlockingCompatibility :
      TemporalTransferMatrixSpatialBlockingCompatibility
    transferReflectionPositivityInput :
      TransferReflectionPositivity
    transferSpectralGapInput :
      TransferSpectralGap
    positiveLatticeMassGapExtractionInput :
      PositiveLatticeMassGapExtraction

temporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo : Bool
temporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo = false

transferReflectionPositivityDerivedInRepo : Bool
transferReflectionPositivityDerivedInRepo = false

transferSpectralGapDerivedInRepo : Bool
transferSpectralGapDerivedInRepo = false

positiveLatticeMassGapExtractionDerivedInRepo : Bool
positiveLatticeMassGapExtractionDerivedInRepo = false

record LatticeMassGapProvider : Set where
  constructor mkLatticeMassGapProvider
  field
    temporalTransferMatrixCompatibleWithSpatialBlocking :
      Bool
    temporalTransferMatrixCompatibleWithSpatialBlockingIsTrue :
      temporalTransferMatrixCompatibleWithSpatialBlocking ≡ true

    transferReflectionPositivity :
      Bool
    transferReflectionPositivityIsTrue :
      transferReflectionPositivity ≡ true

    transferSpectralGap :
      Bool
    transferSpectralGapIsTrue :
      transferSpectralGap ≡ true

    positiveLatticeMassGapExtraction :
      Bool
    positiveLatticeMassGapExtractionIsTrue :
      positiveLatticeMassGapExtraction ≡ true

latticeMassGapProviderFromAnalyticPackage :
  LatticeMassGapAnalyticPackage →
  LatticeMassGapProvider
latticeMassGapProviderFromAnalyticPackage package =
  record
    { temporalTransferMatrixCompatibleWithSpatialBlocking =
        TemporalTransferMatrixSpatialBlockingCompatibility.temporalTransferMatrixCompatibleWithSpatialBlocking
          (LatticeMassGapAnalyticPackage.transferMatrixSpatialBlockingCompatibility package)
    ; temporalTransferMatrixCompatibleWithSpatialBlockingIsTrue =
        TemporalTransferMatrixSpatialBlockingCompatibility.temporalTransferMatrixCompatibleWithSpatialBlockingIsTrue
          (LatticeMassGapAnalyticPackage.transferMatrixSpatialBlockingCompatibility package)
    ; transferReflectionPositivity =
        TransferReflectionPositivity.transferReflectionPositivity
          (LatticeMassGapAnalyticPackage.transferReflectionPositivityInput package)
    ; transferReflectionPositivityIsTrue =
        TransferReflectionPositivity.transferReflectionPositivityIsTrue
          (LatticeMassGapAnalyticPackage.transferReflectionPositivityInput package)
    ; transferSpectralGap =
        TransferSpectralGap.transferSpectralGap
          (LatticeMassGapAnalyticPackage.transferSpectralGapInput package)
    ; transferSpectralGapIsTrue =
        TransferSpectralGap.transferSpectralGapIsTrue
          (LatticeMassGapAnalyticPackage.transferSpectralGapInput package)
    ; positiveLatticeMassGapExtraction =
        PositiveLatticeMassGapExtraction.positiveLatticeMassGapExtraction
          (LatticeMassGapAnalyticPackage.positiveLatticeMassGapExtractionInput package)
    ; positiveLatticeMassGapExtractionIsTrue =
        PositiveLatticeMassGapExtraction.positiveLatticeMassGapExtractionIsTrue
          (LatticeMassGapAnalyticPackage.positiveLatticeMassGapExtractionInput package)
    }

temporalTransferMatrixSpatialBlockingCompatibilityCitation : String
temporalTransferMatrixSpatialBlockingCompatibilityCitation =
  "Balaban transfer-matrix compatibility: spatial blocking is compatible with temporal transfer after small-field survival."

transferReflectionPositivityCitation : String
transferReflectionPositivityCitation =
  "Constructive lattice gauge theory transfer matrix: reflection positivity for the lattice transfer operator."

transferSpectralGapCitation : String
transferSpectralGapCitation =
  "Balaban/KP small-field transfer analysis: positive transfer spectral gap from anisotropic KP plus surviving small-field bounds."

positiveLatticeMassGapExtractionCitation : String
positiveLatticeMassGapExtractionCitation =
  "Transfer-matrix spectral theorem: positive transfer spectral gap extracts a positive lattice mass gap."

record LatticeMassGapProviderSourceMap : Set where
  field
    temporalTransferMatrixSpatialBlockingCompatibilitySource :
      TemporalTransferMatrixSpatialBlockingCompatibility
    temporalTransferMatrixSpatialBlockingCompatibilitySourceCitation :
      String
    temporalTransferMatrixSpatialBlockingCompatibilityStillAuthorityOnly :
      temporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo ≡ false

    transferReflectionPositivitySource :
      TransferReflectionPositivity
    transferReflectionPositivitySourceCitation :
      String
    transferReflectionPositivityStillAuthorityOnly :
      transferReflectionPositivityDerivedInRepo ≡ false

    transferSpectralGapSource :
      TransferSpectralGap
    transferSpectralGapSourceCitation :
      String
    transferSpectralGapStillAuthorityOnly :
      transferSpectralGapDerivedInRepo ≡ false

    positiveLatticeMassGapExtractionSource :
      PositiveLatticeMassGapExtraction
    positiveLatticeMassGapExtractionSourceCitation :
      String
    positiveLatticeMassGapExtractionStillAuthorityOnly :
      positiveLatticeMassGapExtractionDerivedInRepo ≡ false

temporalTransferMatrixSpatialBlockingCompatibilityProvider :
  TemporalTransferMatrixSpatialBlockingCompatibility
temporalTransferMatrixSpatialBlockingCompatibilityProvider =
  mkTemporalTransferMatrixSpatialBlockingCompatibility true refl

transferReflectionPositivityProvider :
  TransferReflectionPositivity
transferReflectionPositivityProvider =
  mkTransferReflectionPositivity true refl

transferSpectralGapProvider :
  TransferSpectralGap
transferSpectralGapProvider =
  mkTransferSpectralGap true refl

positiveLatticeMassGapExtractionProvider :
  PositiveLatticeMassGapExtraction
positiveLatticeMassGapExtractionProvider =
  mkPositiveLatticeMassGapExtraction true refl

latticeMassGapProviderSourceMap :
  LatticeMassGapProviderSourceMap
latticeMassGapProviderSourceMap =
  record
    { temporalTransferMatrixSpatialBlockingCompatibilitySource =
        temporalTransferMatrixSpatialBlockingCompatibilityProvider
    ; temporalTransferMatrixSpatialBlockingCompatibilitySourceCitation =
        temporalTransferMatrixSpatialBlockingCompatibilityCitation
    ; temporalTransferMatrixSpatialBlockingCompatibilityStillAuthorityOnly =
        refl
    ; transferReflectionPositivitySource =
        transferReflectionPositivityProvider
    ; transferReflectionPositivitySourceCitation =
        transferReflectionPositivityCitation
    ; transferReflectionPositivityStillAuthorityOnly =
        refl
    ; transferSpectralGapSource =
        transferSpectralGapProvider
    ; transferSpectralGapSourceCitation =
        transferSpectralGapCitation
    ; transferSpectralGapStillAuthorityOnly =
        refl
    ; positiveLatticeMassGapExtractionSource =
        positiveLatticeMassGapExtractionProvider
    ; positiveLatticeMassGapExtractionSourceCitation =
        positiveLatticeMassGapExtractionCitation
    ; positiveLatticeMassGapExtractionStillAuthorityOnly =
        refl
    }

balabanTransferSpectralGapAnalyticPackage :
  LatticeMassGapAnalyticPackage
balabanTransferSpectralGapAnalyticPackage =
  record
    { transferMatrixSpatialBlockingCompatibility =
        temporalTransferMatrixSpatialBlockingCompatibilityProvider
    ; transferReflectionPositivityInput =
        transferReflectionPositivityProvider
    ; transferSpectralGapInput =
        transferSpectralGapProvider
    ; positiveLatticeMassGapExtractionInput =
        positiveLatticeMassGapExtractionProvider
    }

balabanTransferSpectralGapProvider :
  LatticeMassGapProvider
balabanTransferSpectralGapProvider =
  latticeMassGapProviderFromAnalyticPackage
    balabanTransferSpectralGapAnalyticPackage

record LatticeMassGapFromAnisotropicKPTheorem : Set₂ where
  field
    smallFieldSurvival :
      SmallField.SmallFieldBoundsSurviveAnisotropicBlockingTheorem
    latticeProvider :
      LatticeMassGapProvider
    latticeMassGapFromAnisotropicKP :
      Bool
    latticeMassGapFromAnisotropicKPIsTrue :
      latticeMassGapFromAnisotropicKP ≡ true

latticeMassGapFromAnisotropicKPAuthorityConditional :
  LatticeMassGapFromAnisotropicKPTheorem
latticeMassGapFromAnisotropicKPAuthorityConditional =
  record
    { smallFieldSurvival =
        SmallField.smallFieldBoundsSurviveAnisotropicBlockingAuthorityConditional
    ; latticeProvider =
        balabanTransferSpectralGapProvider
    ; latticeMassGapFromAnisotropicKP = true
    ; latticeMassGapFromAnisotropicKPIsTrue = refl
    }

latticeMassGapProviderAuthorityAvailable : Bool
latticeMassGapProviderAuthorityAvailable = true

latticeMassGapProviderDerivedInRepo : Bool
latticeMassGapProviderDerivedInRepo = false

latticeMassGapProviderImportedByAuthority : Bool
latticeMassGapProviderImportedByAuthority = true

latticeMassGapProviderSplitIntoFourAnalyticLemmas : Bool
latticeMassGapProviderSplitIntoFourAnalyticLemmas = true

temporalTransferMatrixCompatibleWithSpatialBlockingAuthorityConditional : Bool
temporalTransferMatrixCompatibleWithSpatialBlockingAuthorityConditional = true

transferSpectralGapAuthorityConditional : Bool
transferSpectralGapAuthorityConditional = true

latticeMassGapFromAnisotropicKPAuthorityConditionalBool : Bool
latticeMassGapFromAnisotropicKPAuthorityConditionalBool = true

latticeMassGapFromAnisotropicKPUnconditional : Bool
latticeMassGapFromAnisotropicKPUnconditional = false

thermodynamicLimitAuthorityConditional : Bool
thermodynamicLimitAuthorityConditional = false

continuumMassGapTransferAuthorityConditional : Bool
continuumMassGapTransferAuthorityConditional = false

osWightmanReconstructionAuthorityConditional : Bool
osWightmanReconstructionAuthorityConditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data LatticeMassGapPromotion : Set where

latticeMassGapPromotionImpossibleHere :
  LatticeMassGapPromotion →
  ⊥
latticeMassGapPromotionImpossibleHere ()

record LatticeMassGapAuthorityBoundary : Set where
  field
    providerAuthorityAvailableIsTrue :
      latticeMassGapProviderAuthorityAvailable ≡ true
    providerDerivedInRepoStillFalse :
      latticeMassGapProviderDerivedInRepo ≡ false
    providerAuthorityImported :
      latticeMassGapProviderImportedByAuthority ≡ true
    providerSplitIntoFourAnalyticLemmas :
      latticeMassGapProviderSplitIntoFourAnalyticLemmas ≡ true
    providerSourceMap :
      LatticeMassGapProviderSourceMap
    temporalTransferMatrixSpatialBlockingCompatibilityStillAuthorityOnly :
      temporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo ≡ false
    transferReflectionPositivityStillAuthorityOnly :
      transferReflectionPositivityDerivedInRepo ≡ false
    transferSpectralGapStillAuthorityOnly :
      transferSpectralGapDerivedInRepo ≡ false
    positiveLatticeMassGapExtractionStillAuthorityOnly :
      positiveLatticeMassGapExtractionDerivedInRepo ≡ false
    transferCompatibilityAuthorityConditionalIsTrue :
      temporalTransferMatrixCompatibleWithSpatialBlockingAuthorityConditional
        ≡ true
    transferSpectralGapAuthorityConditionalIsTrue :
      transferSpectralGapAuthorityConditional ≡ true
    latticeMassGapAuthorityConditionalIsTrue :
      latticeMassGapFromAnisotropicKPAuthorityConditionalBool ≡ true
    latticeMassGapUnconditionalStillFalse :
      latticeMassGapFromAnisotropicKPUnconditional ≡ false
    thermodynamicLimitAuthorityConditionalStillFalse :
      thermodynamicLimitAuthorityConditional ≡ false
    continuumMassGapTransferAuthorityConditionalStillFalse :
      continuumMassGapTransferAuthorityConditional ≡ false
    osWightmanAuthorityConditionalStillFalse :
      osWightmanReconstructionAuthorityConditional ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      LatticeMassGapPromotion → ⊥

latticeMassGapAuthorityBoundary :
  LatticeMassGapAuthorityBoundary
latticeMassGapAuthorityBoundary =
  record
    { providerAuthorityAvailableIsTrue = refl
    ; providerDerivedInRepoStillFalse = refl
    ; providerAuthorityImported = refl
    ; providerSplitIntoFourAnalyticLemmas = refl
    ; providerSourceMap = latticeMassGapProviderSourceMap
    ; temporalTransferMatrixSpatialBlockingCompatibilityStillAuthorityOnly =
        refl
    ; transferReflectionPositivityStillAuthorityOnly = refl
    ; transferSpectralGapStillAuthorityOnly = refl
    ; positiveLatticeMassGapExtractionStillAuthorityOnly = refl
    ; transferCompatibilityAuthorityConditionalIsTrue = refl
    ; transferSpectralGapAuthorityConditionalIsTrue = refl
    ; latticeMassGapAuthorityConditionalIsTrue = refl
    ; latticeMassGapUnconditionalStillFalse = refl
    ; thermodynamicLimitAuthorityConditionalStillFalse = refl
    ; continuumMassGapTransferAuthorityConditionalStillFalse = refl
    ; osWightmanAuthorityConditionalStillFalse = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = latticeMassGapPromotionImpossibleHere
    }
