module DASHI.Physics.Thermodynamics.MagnetocaloricAMRReceipt where

open import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial
open import DASHI.Physics.Thermodynamics.CaloricRegenerator
open import DASHI.Physics.Thermodynamics.ActiveMagneticRegenerator
open import DASHI.Physics.Thermodynamics.ProtectedMagnetocaloricSystem
open import DASHI.Physics.Thermodynamics.MagnothermSourceBoundary

------------------------------------------------------------------------
-- Terminal receipt for the reusable magnetocaloric / AMR lane.
--
-- The structural formalisation is complete at the generic interface level.
-- The remaining frontier is deliberately physical/calibration-bound.
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

record MagnetocaloricAMRPromotionGate : Set₁ where
  field
    StructuralReceipt : MagnetocaloricAMRStructuralReceipt
    RemainingFrontier : MagnetocaloricAMRRemainingFrontier
    noStructuralShortcutToCalibratedPerformance : Set
    noSourceShortcutToTheoremAuthority           : Set
