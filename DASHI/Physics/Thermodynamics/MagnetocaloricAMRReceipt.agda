module DASHI.Physics.Thermodynamics.MagnetocaloricAMRReceipt where

open import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial
open import DASHI.Physics.Thermodynamics.CaloricRegenerator
open import DASHI.Physics.Thermodynamics.ActiveMagneticRegenerator
open import DASHI.Physics.Thermodynamics.ProtectedMagnetocaloricSystem
open import DASHI.Physics.Thermodynamics.MagnothermSourceBoundary
open import DASHI.Physics.Thermodynamics.MagnetocaloricConsumerAtlasExact

------------------------------------------------------------------------
-- Terminal receipt for the reusable magnetocaloric / AMR lane.
--
-- The structural formalisation is complete at the generic interface level.
-- Cross-domain consumers are populated through explicit bridges.  The
-- remaining frontier is deliberately physical/calibration-bound.
------------------------------------------------------------------------

record MagnetocaloricAMRStructuralReceipt : Set₁ where
  field
    materialResponseSeparatedFromDevicePerformance : Set
    maxwellAndAdiabaticLawsAreEvidenceBearing      : Set
    porousTransportOwnsConservation                : Set
    hydraulicCoefficientsRemainCalibrated          : Set
    fourPhaseCycleIsExplicit                       : Set
    periodicityIsExplicitWitness                   : Set
    positiveCoolingIsExplicitWitness               : Set
    degradationFeedsSystemValidity                 : Set
    qualifiedIntegrityIsTimeBounded                : Set
    workRecoveryIsBounded                          : Set
    firstAndSecondLawAccountingExplicit            : Set
    magnothermEvidenceAttributionSeparated          : Set
    vendorClaimsBlockedFromPromotion               : Set

    siMetrologyConsumerPopulated                   : Set
    electromagneticConsumerPopulated               : Set
    condensedMatterConsumerPopulated               : Set
    atomicChemistryConsumerPopulated               : Set
    protectionChemistryConsumerPopulated           : Set
    quantumStatisticalConsumerPopulated            : Set
    continuumTransportConsumerPopulated            : Set
    magnetostructuralConsumerPopulated              : Set

    magneticBAndHRemainDistinct                    : Set
    sharedMaterialCarrierDoesNotCollapseObservables : Set
    coatingAndSubstrateRemainDistinctMaterials      : Set
    magnetostrictionIsCalibrationBound              : Set
    clayNSNotRequiredForDeviceTransport             : Set
    nonAbelianYMNotApplicationMagnetism             : Set
    biologicalAgencyControlNotImportedAsDeviceControl : Set

record MagnetocaloricAMRRemainingFrontier : Set₁ where
  field
    materialSpecificConstitutiveData : Set
    measuredFieldTemperatureResponse : Set
    measuredPorousHydraulics         : Set
    measuredHeatTransfer             : Set
    cycleTimingAndControlCalibration : Set
    sameDeviceCoolingEnergy          : Set
    sameDeviceInputWork              : Set
    sameDeviceRecoveredWork          : Set
    degradationTimeSeries            : Set
    deviceLevelCOPValidation         : Set

    materialSpecificCrystalIdentification : Set
    materialSpecificMagneticSymmetry       : Set
    validatedHamiltonianOrElectronicModel  : Set
    ensembleAndFreeEnergyCalibration       : Set
    compositionSubstitutionHydrogenationResponse : Set
    coatingInhibitorFluidCorrosionCalibration : Set
    transitionStrainAndFatigueCalibration : Set
    electromagneticFieldMapAndBHCalibration : Set

record MagnetocaloricAMRPromotionGate : Set₁ where
  field
    StructuralReceipt : MagnetocaloricAMRStructuralReceipt
    RemainingFrontier : MagnetocaloricAMRRemainingFrontier
    ConsumerAtlas : MagnetocaloricConsumerAtlas
    noStructuralShortcutToCalibratedPerformance : Set
    noSourceShortcutToTheoremAuthority           : Set
    noMicroscopicShortcutToBulkResponse           : Set
    noMechanicalShortcutToQualifiedLifetime       : Set
    noClayShortcutToDevicePhysics                 : Set
