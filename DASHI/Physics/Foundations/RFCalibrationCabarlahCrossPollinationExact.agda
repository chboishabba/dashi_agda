module DASHI.Physics.Foundations.RFCalibrationCabarlahCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.RFCalibrationGoniometerRelevanceExact as Calibration
import DASHI.Physics.Foundations.CabarlahGoniometerAcquisitionExact as Cabarlah
import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as Goniometer
import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as Array

------------------------------------------------------------------------
-- CABARLAH CALIBRATION BOUNDARY
--
-- Cabarlah has sourced DF lineage, but the available acquisition does not pay
-- a particular calibration model for the historical equipment.  Modern array
-- calibration concepts are therefore retained as comparison coordinates only.
------------------------------------------------------------------------

record CabarlahCalibrationBoundary : Set where
  constructor cabarlah-calibration-boundary
  field
    cabarlahDirectionFindingAcquisitionRetained :
      Cabarlah.CabarlahDirectionFindingAcquisition

    cabarlahGoniometerBoundaryRetained :
      Cabarlah.CabarlahGoniometerBoundary

    calibrationRelevanceRetained :
      Calibration.GoniometerCalibrationRelevanceReceipt

    cabarlahHistoricalDFPaid : Bool
    cabarlahHistoricalDFPaidIsTrue :
      cabarlahHistoricalDFPaid ≡ true

    cabarlahHistoricalGainPhaseCalibrationPaid : Bool
    cabarlahHistoricalGainPhaseCalibrationPaidIsFalse :
      cabarlahHistoricalGainPhaseCalibrationPaid ≡ false

    cabarlahHistoricalPhaseQuantisationPaid : Bool
    cabarlahHistoricalPhaseQuantisationPaidIsFalse :
      cabarlahHistoricalPhaseQuantisationPaid ≡ false

    cabarlahHistoricalMutualCouplingCorrectionPaid : Bool
    cabarlahHistoricalMutualCouplingCorrectionPaidIsFalse :
      cabarlahHistoricalMutualCouplingCorrectionPaid ≡ false

open CabarlahCalibrationBoundary public

canonicalCabarlahCalibrationBoundary : CabarlahCalibrationBoundary
canonicalCabarlahCalibrationBoundary =
  cabarlah-calibration-boundary
    Cabarlah.canonicalCabarlahDirectionFindingAcquisition
    Cabarlah.canonicalCabarlahGoniometerBoundary
    Calibration.canonicalGoniometerCalibrationRelevanceReceipt
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- HISTORICAL / MODERN BRIDGE
--
-- This records only a role-level continuity: both historical goniometer DF
-- and modern phase-sensitive arrays estimate angle.  Their error models remain
-- implementation-specific and cannot be transported across the historical gap
-- without source payment.
------------------------------------------------------------------------

record HistoricalModernCalibrationBridge : Set where
  constructor historical-modern-calibration-bridge
  field
    mechanicalAngleRole :
      Goniometer.implementationRole Goniometer.mechanicalAngleReadout
      ≡ Goniometer.angleEstimationRole

    electronicPhaseAngleRole :
      Goniometer.implementationRole Goniometer.phaseComparison
      ≡ Goniometer.angleEstimationRole

    phasedArrayAngularRole :
      Array.supportsAngularObservation Array.electronicallySteeredPhasedArray
      ≡ Array.angularObservationRole

    commonRoleAllowsErrorModelTransport : Bool
    commonRoleAllowsErrorModelTransportIsFalse :
      commonRoleAllowsErrorModelTransport ≡ false

    modernErrorModelProvesHistoricalHardwareFamily : Bool
    modernErrorModelProvesHistoricalHardwareFamilyIsFalse :
      modernErrorModelProvesHistoricalHardwareFamily ≡ false

    historicalHardwareSimilarityProvesModernSignalModel : Bool
    historicalHardwareSimilarityProvesModernSignalModelIsFalse :
      historicalHardwareSimilarityProvesModernSignalModel ≡ false

open HistoricalModernCalibrationBridge public

canonicalHistoricalModernCalibrationBridge :
  HistoricalModernCalibrationBridge
canonicalHistoricalModernCalibrationBridge =
  historical-modern-calibration-bridge
    refl
    refl
    refl
    false refl
    false refl
    false refl
