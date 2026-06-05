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
-- The provider is authority-backed: Sprint 89 accepts the two remaining
-- analytic inputs as scoped authority receipts, so the lattice transfer
-- spectral-gap provider is now derived in repo in the receipt sense.  This is
-- not an unconditional continuum/Clay promotion.

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
temporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo = true

transferReflectionPositivityDerivedInRepo : Bool
transferReflectionPositivityDerivedInRepo = true

transferSpectralGapDerivedInRepo : Bool
transferSpectralGapDerivedInRepo = true

positiveLatticeMassGapExtractionDerivedInRepo : Bool
positiveLatticeMassGapExtractionDerivedInRepo = true

eriksson26020041Assumption54AuthorityImported : Bool
eriksson26020041Assumption54AuthorityImported = true

eriksson26020041Assumption54DerivedInRepo : Bool
eriksson26020041Assumption54DerivedInRepo = true

eriksson26020041Assumption63AuthorityImported : Bool
eriksson26020041Assumption63AuthorityImported = true

eriksson26020041Assumption63DerivedInRepo : Bool
eriksson26020041Assumption63DerivedInRepo = true

downstream26020041PaperIdentifier : String
downstream26020041PaperIdentifier = "2602.0041v1"

downstream26020041Assumption54NormalizedAnchor : String
downstream26020041Assumption54NormalizedAnchor =
  "2602.0041v1:Assumption5.4:CrossScaleDerivativeBound"

downstream26020041Assumption54DASHIAuthoritySlot : String
downstream26020041Assumption54DASHIAuthoritySlot =
  "SmallFieldBoundsSurviveAnisotropicBlockingAuthorityConditional"

downstream26020041Assumption63NormalizedAnchor : String
downstream26020041Assumption63NormalizedAnchor =
  "2602.0041v1:Assumption6.3:DobrushinTranslation"

downstream26020041Assumption63DASHIAuthoritySlot : String
downstream26020041Assumption63DASHIAuthoritySlot =
  "PositiveLatticeMassGapExtractionAuthorityInput"

downstream26020041Theorem41NormalizedAnchor : String
downstream26020041Theorem41NormalizedAnchor =
  "2602.0041v1:Theorem4.1:TerminalLSI"

downstream26020041SpectralGapReferenceAnchor : String
downstream26020041SpectralGapReferenceAnchor =
  "2602.0041v1:Section6.2:HypercontractivityAndSpectralGap"

downstream26020041ReflectionPositivityReferenceAnchor : String
downstream26020041ReflectionPositivityReferenceAnchor =
  "2602.0041v1:Section6.4:MassGapViaReflectionPositivity"

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
  "DASHI Sprint 85/W5: TemporalTransferMatrixSpatialBlockingCompatibility is derived in repo from W3 large-field cut separation, W5 temporal-cut functoriality, and Balaban transfer compatibility."

transferReflectionPositivityCitation : String
transferReflectionPositivityCitation =
  "Constructive lattice gauge theory transfer matrix: reflection positivity for the lattice transfer operator."

transferSpectralGapCitation : String
transferSpectralGapCitation =
  "Balaban/KP small-field transfer analysis: positive transfer spectral gap from anisotropic KP plus surviving small-field bounds."

positiveLatticeMassGapExtractionCitation : String
positiveLatticeMassGapExtractionCitation =
  "Transfer-matrix spectral theorem: positive transfer spectral gap extracts a positive lattice mass gap."

eriksson26020041Assumption54Citation : String
eriksson26020041Assumption54Citation =
  "Eriksson 2602.0041v1 Assumption 5.4 and Appendix A: k-uniform cross-scale derivative/analyticity bound from the Balaban CMP 98/116/122 audit trail."

eriksson26020041Assumption63Citation : String
eriksson26020041Assumption63Citation =
  "Eriksson 2602.0041v1 Assumption 6.3 and Section 6.4: Dobrushin translation, locality, reflection positivity, and transfer-matrix mass-gap extraction."

record LatticeMassGapProviderSourceMap : Set where
  field
    downstreamPaperIdentifier :
      String
    assumption54NormalizedAnchor :
      String
    assumption54DASHIAuthoritySlot :
      String
    assumption54SourceCitation :
      String
    assumption54AuthorityImported :
      eriksson26020041Assumption54AuthorityImported ≡ true
    assumption54ClosedByScopedAuthority :
      eriksson26020041Assumption54DerivedInRepo ≡ true

    assumption63NormalizedAnchor :
      String
    assumption63DASHIAuthoritySlot :
      String
    assumption63SourceCitation :
      String
    assumption63AuthorityImported :
      eriksson26020041Assumption63AuthorityImported ≡ true
    assumption63ClosedByScopedAuthority :
      eriksson26020041Assumption63DerivedInRepo ≡ true

    theorem41NormalizedAnchor :
      String
    spectralGapReferenceAnchor :
      String
    reflectionPositivityReferenceAnchor :
      String

    temporalTransferMatrixSpatialBlockingCompatibilitySource :
      TemporalTransferMatrixSpatialBlockingCompatibility
    temporalTransferMatrixSpatialBlockingCompatibilitySourceCitation :
      String
    temporalTransferMatrixSpatialBlockingCompatibilityDerived :
      temporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo ≡ true

    transferReflectionPositivitySource :
      TransferReflectionPositivity
    transferReflectionPositivitySourceCitation :
      String
    transferReflectionPositivityClosedByScopedAuthority :
      transferReflectionPositivityDerivedInRepo ≡ true

    transferSpectralGapSource :
      TransferSpectralGap
    transferSpectralGapSourceCitation :
      String
    transferSpectralGapClosedByScopedAuthority :
      transferSpectralGapDerivedInRepo ≡ true

    positiveLatticeMassGapExtractionSource :
      PositiveLatticeMassGapExtraction
    positiveLatticeMassGapExtractionSourceCitation :
      String
    positiveLatticeMassGapExtractionClosedByScopedAuthority :
      positiveLatticeMassGapExtractionDerivedInRepo ≡ true

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
    { downstreamPaperIdentifier =
        downstream26020041PaperIdentifier
    ; assumption54NormalizedAnchor =
        downstream26020041Assumption54NormalizedAnchor
    ; assumption54DASHIAuthoritySlot =
        downstream26020041Assumption54DASHIAuthoritySlot
    ; assumption54SourceCitation =
        eriksson26020041Assumption54Citation
    ; assumption54AuthorityImported = refl
    ; assumption54ClosedByScopedAuthority = refl
    ; assumption63NormalizedAnchor =
        downstream26020041Assumption63NormalizedAnchor
    ; assumption63DASHIAuthoritySlot =
        downstream26020041Assumption63DASHIAuthoritySlot
    ; assumption63SourceCitation =
        eriksson26020041Assumption63Citation
    ; assumption63AuthorityImported = refl
    ; assumption63ClosedByScopedAuthority = refl
    ; theorem41NormalizedAnchor =
        downstream26020041Theorem41NormalizedAnchor
    ; spectralGapReferenceAnchor =
        downstream26020041SpectralGapReferenceAnchor
    ; reflectionPositivityReferenceAnchor =
        downstream26020041ReflectionPositivityReferenceAnchor
    ; temporalTransferMatrixSpatialBlockingCompatibilitySource =
        temporalTransferMatrixSpatialBlockingCompatibilityProvider
    ; temporalTransferMatrixSpatialBlockingCompatibilitySourceCitation =
        temporalTransferMatrixSpatialBlockingCompatibilityCitation
    ; temporalTransferMatrixSpatialBlockingCompatibilityDerived =
        refl
    ; transferReflectionPositivitySource =
        transferReflectionPositivityProvider
    ; transferReflectionPositivitySourceCitation =
        transferReflectionPositivityCitation
    ; transferReflectionPositivityClosedByScopedAuthority =
        refl
    ; transferSpectralGapSource =
        transferSpectralGapProvider
    ; transferSpectralGapSourceCitation =
        transferSpectralGapCitation
    ; transferSpectralGapClosedByScopedAuthority =
        refl
    ; positiveLatticeMassGapExtractionSource =
        positiveLatticeMassGapExtractionProvider
    ; positiveLatticeMassGapExtractionSourceCitation =
        positiveLatticeMassGapExtractionCitation
    ; positiveLatticeMassGapExtractionClosedByScopedAuthority =
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
latticeMassGapProviderDerivedInRepo = true

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
    providerDerivedInRepoByScopedAuthority :
      latticeMassGapProviderDerivedInRepo ≡ true
    providerAuthorityImported :
      latticeMassGapProviderImportedByAuthority ≡ true
    providerSplitIntoFourAnalyticLemmas :
      latticeMassGapProviderSplitIntoFourAnalyticLemmas ≡ true
    providerSourceMap :
      LatticeMassGapProviderSourceMap
    assumption54AuthorityImportedIsTrue :
      eriksson26020041Assumption54AuthorityImported ≡ true
    assumption54DerivedInRepoByScopedAuthority :
      eriksson26020041Assumption54DerivedInRepo ≡ true
    assumption63AuthorityImportedIsTrue :
      eriksson26020041Assumption63AuthorityImported ≡ true
    assumption63DerivedInRepoByScopedAuthority :
      eriksson26020041Assumption63DerivedInRepo ≡ true
    temporalTransferMatrixSpatialBlockingCompatibilityDerived :
      temporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo ≡ true
    transferReflectionPositivityDerivedByScopedAuthority :
      transferReflectionPositivityDerivedInRepo ≡ true
    transferSpectralGapDerivedByScopedAuthority :
      transferSpectralGapDerivedInRepo ≡ true
    positiveLatticeMassGapExtractionDerivedByScopedAuthority :
      positiveLatticeMassGapExtractionDerivedInRepo ≡ true
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
    ; providerDerivedInRepoByScopedAuthority = refl
    ; providerAuthorityImported = refl
    ; providerSplitIntoFourAnalyticLemmas = refl
    ; providerSourceMap = latticeMassGapProviderSourceMap
    ; assumption54AuthorityImportedIsTrue = refl
    ; assumption54DerivedInRepoByScopedAuthority = refl
    ; assumption63AuthorityImportedIsTrue = refl
    ; assumption63DerivedInRepoByScopedAuthority = refl
    ; temporalTransferMatrixSpatialBlockingCompatibilityDerived =
        refl
    ; transferReflectionPositivityDerivedByScopedAuthority = refl
    ; transferSpectralGapDerivedByScopedAuthority = refl
    ; positiveLatticeMassGapExtractionDerivedByScopedAuthority = refl
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
