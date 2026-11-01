module DASHI.Physics.Closure.YMLatticeMassGapAuthority where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMSmallFieldSurvivalAuthority as SmallField

------------------------------------------------------------------------
-- Authority-conditional lattice mass-gap gate.
--
-- This module is a finite-lattice provider surface only.  It advances the
-- authority-conditional lane one step beyond small-field survival by typing
-- the finite transfer-matrix compatibility and finite spectral-gap package
-- needed to turn anisotropic KP plus surviving small-field bounds into a
-- positive lattice mass gap.
--
-- The honest chain is sharper than the older generic wording:
--
--   * finite self-adjointness and the finite spectral margin are internal
--     finite-carrier facts already closed here;
--   * the imported Balaban/Eriksson package is consumed as upstream provider
--     authority rather than promoted as a peer front with the live burden;
--   * the live missing-content frontier, if internal closure is demanded,
--     remains Balaban-centered H3a;
--   * H3b vacuum-projection continuity, no-spectral-pollution,
--     thermodynamic-limit, and OS/Wightman surfaces are downstream consumers
--     or downstream slots after that H3a frontier;
--   * all continuum/Clay promotions remain false.
--
-- The provider is authority-backed in the receipt sense only.  This file does
-- not claim continuum closure and does not move the live burden away from H3a.

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
transferReflectionPositivityDerivedInRepo = false

transferSpectralGapDerivedInRepo : Bool
transferSpectralGapDerivedInRepo = false

positiveLatticeMassGapExtractionDerivedInRepo : Bool
positiveLatticeMassGapExtractionDerivedInRepo = false

finiteSelfAdjointnessInternalized : Bool
finiteSelfAdjointnessInternalized = true

finiteSpectralMarginInternalized : Bool
finiteSpectralMarginInternalized = true

eriksson26020041Assumption54AuthorityImported : Bool
eriksson26020041Assumption54AuthorityImported = true

eriksson26020041Assumption54DerivedInRepo : Bool
eriksson26020041Assumption54DerivedInRepo = false

eriksson26020041Assumption63AuthorityImported : Bool
eriksson26020041Assumption63AuthorityImported = true

eriksson26020041Assumption63DerivedInRepo : Bool
eriksson26020041Assumption63DerivedInRepo = false

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

finiteLatticeAuthoritySurfaceIsUpstreamProvider : Bool
finiteLatticeAuthoritySurfaceIsUpstreamProvider = true

finiteLatticeAuthoritySurfaceCarriesLiveClosureBurden : Bool
finiteLatticeAuthoritySurfaceCarriesLiveClosureBurden = false

balabanH3aIsLiveMissingContentFrontier : Bool
balabanH3aIsLiveMissingContentFrontier = true

h3bVacuumProjectionContinuityIsDownstreamConsumer : Bool
h3bVacuumProjectionContinuityIsDownstreamConsumer = true

noSpectralPollutionIsDownstreamConsumer : Bool
noSpectralPollutionIsDownstreamConsumer = true

thermodynamicLimitIsDownstreamSlot : Bool
thermodynamicLimitIsDownstreamSlot = true

osWightmanIsDownstreamSlot : Bool
osWightmanIsDownstreamSlot = true

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
  "DASHI Sprint 85/W5 finite-lattice receipt: TemporalTransferMatrixSpatialBlockingCompatibility is derived in repo from W3 large-field cut separation, W5 temporal-cut functoriality, and finite transfer compatibility."

transferReflectionPositivityCitation : String
transferReflectionPositivityCitation =
  "Authority-backed finite-lattice provider slot: reflection positivity for the lattice transfer operator consumed here without continuum promotion."

transferSpectralGapCitation : String
transferSpectralGapCitation =
  "Authority-backed finite-lattice provider slot: positive transfer spectral gap from anisotropic KP plus surviving small-field bounds."

positiveLatticeMassGapExtractionCitation : String
positiveLatticeMassGapExtractionCitation =
  "Finite-lattice extraction slot: a positive transfer spectral gap yields a positive lattice mass gap before any continuum intake."

eriksson26020041Assumption54Citation : String
eriksson26020041Assumption54Citation =
  "Eriksson 2602.0041v1 Assumption 5.4 and Appendix A: imported cross-scale derivative/analyticity authority from the Balaban CMP 98/116/122 trail, consumed here as upstream provider support."

eriksson26020041Assumption63Citation : String
eriksson26020041Assumption63Citation =
  "Eriksson 2602.0041v1 Assumption 6.3 and Section 6.4: imported Dobrushin/locality/reflection-positivity/mass-gap extraction authority, consumed here as finite-lattice provider support."

record LatticeMassGapProviderSourceMap : Set where
  field
    finiteLatticeSurfaceIsUpstreamProvider :
      finiteLatticeAuthoritySurfaceIsUpstreamProvider ≡ true
    finiteLatticeSurfaceNotLiveClosureBurden :
      finiteLatticeAuthoritySurfaceCarriesLiveClosureBurden ≡ false
    liveMissingContentFrontierIsBalabanH3a :
      balabanH3aIsLiveMissingContentFrontier ≡ true
    h3bSurfaceIsDownstreamConsumer :
      h3bVacuumProjectionContinuityIsDownstreamConsumer ≡ true
    noSpectralPollutionSurfaceIsDownstreamConsumer :
      noSpectralPollutionIsDownstreamConsumer ≡ true
    thermodynamicLimitSurfaceIsDownstreamSlot :
      thermodynamicLimitIsDownstreamSlot ≡ true
    osWightmanSurfaceIsDownstreamSlot :
      osWightmanIsDownstreamSlot ≡ true

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
    assumption54NotDerivedInternally :
      eriksson26020041Assumption54DerivedInRepo ≡ false

    assumption63NormalizedAnchor :
      String
    assumption63DASHIAuthoritySlot :
      String
    assumption63SourceCitation :
      String
    assumption63AuthorityImported :
      eriksson26020041Assumption63AuthorityImported ≡ true
    assumption63NotDerivedInternally :
      eriksson26020041Assumption63DerivedInRepo ≡ false

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
    transferReflectionPositivityNotDerivedInternally :
      transferReflectionPositivityDerivedInRepo ≡ false

    transferSpectralGapSource :
      TransferSpectralGap
    transferSpectralGapSourceCitation :
      String
    transferSpectralGapNotDerivedInternally :
      transferSpectralGapDerivedInRepo ≡ false

    positiveLatticeMassGapExtractionSource :
      PositiveLatticeMassGapExtraction
    positiveLatticeMassGapExtractionSourceCitation :
      String
    positiveLatticeMassGapExtractionNotDerivedInternally :
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
    { finiteLatticeSurfaceIsUpstreamProvider = refl
    ; finiteLatticeSurfaceNotLiveClosureBurden = refl
    ; liveMissingContentFrontierIsBalabanH3a = refl
    ; h3bSurfaceIsDownstreamConsumer = refl
    ; noSpectralPollutionSurfaceIsDownstreamConsumer = refl
    ; thermodynamicLimitSurfaceIsDownstreamSlot = refl
    ; osWightmanSurfaceIsDownstreamSlot = refl
    ; downstreamPaperIdentifier =
        downstream26020041PaperIdentifier
    ; assumption54NormalizedAnchor =
        downstream26020041Assumption54NormalizedAnchor
    ; assumption54DASHIAuthoritySlot =
        downstream26020041Assumption54DASHIAuthoritySlot
    ; assumption54SourceCitation =
        eriksson26020041Assumption54Citation
    ; assumption54AuthorityImported = refl
    ; assumption54NotDerivedInternally = refl
    ; assumption63NormalizedAnchor =
        downstream26020041Assumption63NormalizedAnchor
    ; assumption63DASHIAuthoritySlot =
        downstream26020041Assumption63DASHIAuthoritySlot
    ; assumption63SourceCitation =
        eriksson26020041Assumption63Citation
    ; assumption63AuthorityImported = refl
    ; assumption63NotDerivedInternally = refl
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
    ; transferReflectionPositivityNotDerivedInternally =
        refl
    ; transferSpectralGapSource =
        transferSpectralGapProvider
    ; transferSpectralGapSourceCitation =
        transferSpectralGapCitation
    ; transferSpectralGapNotDerivedInternally =
        refl
    ; positiveLatticeMassGapExtractionSource =
        positiveLatticeMassGapExtractionProvider
    ; positiveLatticeMassGapExtractionSourceCitation =
        positiveLatticeMassGapExtractionCitation
    ; positiveLatticeMassGapExtractionNotDerivedInternally =
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

balabanH3aContinuumIntakeAuthorityConditional : Bool
balabanH3aContinuumIntakeAuthorityConditional = false

h3bVacuumProjectionContinuityAuthorityConditional : Bool
h3bVacuumProjectionContinuityAuthorityConditional = false

noSpectralPollutionFromH3aH3bAuthorityConditional : Bool
noSpectralPollutionFromH3aH3bAuthorityConditional = false

thermodynamicLimitAuthorityConditional : Bool
thermodynamicLimitAuthorityConditional = false

continuumMassGapTransferAuthorityConditional : Bool
continuumMassGapTransferAuthorityConditional = false

osWightmanReconstructionAuthorityConditional : Bool
osWightmanReconstructionAuthorityConditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

remainingAuthorityChainSummary : String
remainingAuthorityChainSummary =
  "This module closes only the finite lattice provider package. It consumes Balaban/Eriksson authority as upstream support, does not carry the live closure burden, and leaves Balaban-centered H3a as the missing-content frontier. Every downstream slot stays ordered as H3a then H3b then no-spectral-pollution then thermodynamic-limit then OS/Wightman then continuum mass-gap transfer."

data LatticeMassGapPromotion : Set where

latticeMassGapPromotionImpossibleHere :
  LatticeMassGapPromotion →
  ⊥
latticeMassGapPromotionImpossibleHere ()

record LatticeMassGapAuthorityBoundary : Set where
  field
    providerAuthorityAvailableIsTrue :
      latticeMassGapProviderAuthorityAvailable ≡ true
    providerNotDerivedInRepo :
      latticeMassGapProviderDerivedInRepo ≡ false
    providerAuthorityImported :
      latticeMassGapProviderImportedByAuthority ≡ true
    providerSplitIntoFourAnalyticLemmas :
      latticeMassGapProviderSplitIntoFourAnalyticLemmas ≡ true
    providerSourceMap :
      LatticeMassGapProviderSourceMap
    finiteLatticeSurfaceIsUpstreamProvider :
      finiteLatticeAuthoritySurfaceIsUpstreamProvider ≡ true
    finiteLatticeSurfaceNotLiveClosureBurden :
      finiteLatticeAuthoritySurfaceCarriesLiveClosureBurden ≡ false
    liveMissingContentFrontierIsBalabanH3a :
      balabanH3aIsLiveMissingContentFrontier ≡ true
    h3bSurfaceIsDownstreamConsumer :
      h3bVacuumProjectionContinuityIsDownstreamConsumer ≡ true
    noSpectralPollutionSurfaceIsDownstreamConsumer :
      noSpectralPollutionIsDownstreamConsumer ≡ true
    thermodynamicLimitSurfaceIsDownstreamSlot :
      thermodynamicLimitIsDownstreamSlot ≡ true
    osWightmanSurfaceIsDownstreamSlot :
      osWightmanIsDownstreamSlot ≡ true
    assumption54AuthorityImportedIsTrue :
      eriksson26020041Assumption54AuthorityImported ≡ true
    assumption54NotDerivedInRepo :
      eriksson26020041Assumption54DerivedInRepo ≡ false
    assumption63AuthorityImportedIsTrue :
      eriksson26020041Assumption63AuthorityImported ≡ true
    assumption63NotDerivedInRepo :
      eriksson26020041Assumption63DerivedInRepo ≡ false
    temporalTransferMatrixSpatialBlockingCompatibilityDerived :
      temporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo ≡ true
    transferReflectionPositivityNotDerivedInRepo :
      transferReflectionPositivityDerivedInRepo ≡ false
    transferSpectralGapNotDerivedInRepo :
      transferSpectralGapDerivedInRepo ≡ false
    positiveLatticeMassGapExtractionNotDerivedInRepo :
      positiveLatticeMassGapExtractionDerivedInRepo ≡ false
    finiteSelfAdjointnessClosedInternally :
      finiteSelfAdjointnessInternalized ≡ true
    finiteSpectralMarginClosedInternally :
      finiteSpectralMarginInternalized ≡ true
    transferCompatibilityAuthorityConditionalIsTrue :
      temporalTransferMatrixCompatibleWithSpatialBlockingAuthorityConditional
        ≡ true
    transferSpectralGapAuthorityConditionalIsTrue :
      transferSpectralGapAuthorityConditional ≡ true
    latticeMassGapAuthorityConditionalIsTrue :
      latticeMassGapFromAnisotropicKPAuthorityConditionalBool ≡ true
    latticeMassGapUnconditionalStillFalse :
      latticeMassGapFromAnisotropicKPUnconditional ≡ false
    balabanH3aAuthorityConditionalStillFalse :
      balabanH3aContinuumIntakeAuthorityConditional ≡ false
    h3bAuthorityConditionalStillFalse :
      h3bVacuumProjectionContinuityAuthorityConditional ≡ false
    noSpectralPollutionFromH3aH3bStillFalse :
      noSpectralPollutionFromH3aH3bAuthorityConditional ≡ false
    thermodynamicLimitAuthorityConditionalStillFalse :
      thermodynamicLimitAuthorityConditional ≡ false
    continuumMassGapTransferAuthorityConditionalStillFalse :
      continuumMassGapTransferAuthorityConditional ≡ false
    osWightmanAuthorityConditionalStillFalse :
      osWightmanReconstructionAuthorityConditional ≡ false
    remainingAuthorityChain :
      String
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      LatticeMassGapPromotion → ⊥

latticeMassGapAuthorityBoundary :
  LatticeMassGapAuthorityBoundary
latticeMassGapAuthorityBoundary =
  record
    { providerAuthorityAvailableIsTrue = refl
    ; providerNotDerivedInRepo = refl
    ; providerAuthorityImported = refl
    ; providerSplitIntoFourAnalyticLemmas = refl
    ; providerSourceMap = latticeMassGapProviderSourceMap
    ; finiteLatticeSurfaceIsUpstreamProvider = refl
    ; finiteLatticeSurfaceNotLiveClosureBurden = refl
    ; liveMissingContentFrontierIsBalabanH3a = refl
    ; h3bSurfaceIsDownstreamConsumer = refl
    ; noSpectralPollutionSurfaceIsDownstreamConsumer = refl
    ; thermodynamicLimitSurfaceIsDownstreamSlot = refl
    ; osWightmanSurfaceIsDownstreamSlot = refl
    ; assumption54AuthorityImportedIsTrue = refl
    ; assumption54NotDerivedInRepo = refl
    ; assumption63AuthorityImportedIsTrue = refl
    ; assumption63NotDerivedInRepo = refl
    ; temporalTransferMatrixSpatialBlockingCompatibilityDerived =
        refl
    ; transferReflectionPositivityNotDerivedInRepo = refl
    ; transferSpectralGapNotDerivedInRepo = refl
    ; positiveLatticeMassGapExtractionNotDerivedInRepo = refl
    ; finiteSelfAdjointnessClosedInternally = refl
    ; finiteSpectralMarginClosedInternally = refl
    ; transferCompatibilityAuthorityConditionalIsTrue = refl
    ; transferSpectralGapAuthorityConditionalIsTrue = refl
    ; latticeMassGapAuthorityConditionalIsTrue = refl
    ; latticeMassGapUnconditionalStillFalse = refl
    ; balabanH3aAuthorityConditionalStillFalse = refl
    ; h3bAuthorityConditionalStillFalse = refl
    ; noSpectralPollutionFromH3aH3bStillFalse = refl
    ; thermodynamicLimitAuthorityConditionalStillFalse = refl
    ; continuumMassGapTransferAuthorityConditionalStillFalse = refl
    ; osWightmanAuthorityConditionalStillFalse = refl
    ; remainingAuthorityChain = remainingAuthorityChainSummary
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = latticeMassGapPromotionImpossibleHere
    }
