module DASHI.Physics.Thermodynamics.MagnetocaloricAMRReceipt where

open import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial
open import DASHI.Physics.Thermodynamics.CaloricRegenerator
open import DASHI.Physics.Thermodynamics.ActiveMagneticRegenerator
open import DASHI.Physics.Thermodynamics.ProtectedMagnetocaloricSystem
open import DASHI.Physics.Thermodynamics.MagnothermSourceBoundary
open import DASHI.Physics.Thermodynamics.MagnetocaloricConsumerAtlasExact
import DASHI.Physics.Thermodynamics.MagnetocaloricEvidenceMaxCutExact as MaxCut

------------------------------------------------------------------------
-- Terminal receipt for the reusable magnetocaloric / AMR lane.
--
-- Structural formalisation and the current source-payment atlas are explicit.
-- The remaining frontier is same-object physical acquisition/calibration, not
-- another ungrounded abstraction layer.
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

    canonicalAttributedSourceCoreUsed              : Set
    claimRelativePrimarynessEncoded                : Set
    accessCarrierSeparateFromAuthorship             : Set
    sixWeekPeerReviewedAgingPaymentEncoded          : Set
    preliminaryThreeMonthPaymentQualified           : Set
    plannedLongTermExperimentNotPromoted            : Set

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
    completedLongDurationSameObjectAging : Set
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
    EvidenceMaxCutReceipt : MaxCut.MagnetocaloricMaxCutReceipt
    noStructuralShortcutToCalibratedPerformance : Set
    noSourceShortcutToTheoremAuthority           : Set
    noMicroscopicShortcutToBulkResponse           : Set
    noMechanicalShortcutToQualifiedLifetime       : Set
    noVendorShortcutToSameDevicePerformance       : Set
    noPlannedExperimentShortcutToObservedLifetime : Set
    noClayShortcutToDevicePhysics                 : Set
