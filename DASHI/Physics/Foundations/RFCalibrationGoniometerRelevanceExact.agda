module DASHI.Physics.Foundations.RFCalibrationGoniometerRelevanceExact where

open import DASHI.Core.Prelude

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Foundations.RFCalibrationSourceAtlasExact as Sources
import DASHI.Physics.Foundations.RFMutualCouplingManifoldExact as Coupling
import DASHI.Physics.Foundations.RFArrayManifoldPhasorCrossPollinationExact as Manifold
import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as Array
import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as Goniometer

------------------------------------------------------------------------
-- CALIBRATION RESIDUALS
--
-- The original question concerns how historical/mechanical goniometer DF,
-- modern phased-array/interferometric DF, and complex-RF machinery relate.
-- Calibration is relevant because it preserves the common angular-observation
-- role while exposing implementation-specific error coordinates.
------------------------------------------------------------------------

data CalibrationResidual : Set where
  gainMismatchResidual : CalibrationResidual
  phaseMismatchResidual : CalibrationResidual
  mutualCouplingResidual : CalibrationResidual
  phaseQuantisationResidual : CalibrationResidual
  manifoldMismatchResidual : CalibrationResidual

gainMismatchIsNotPhaseMismatch :
  gainMismatchResidual ≡ phaseMismatchResidual → ⊥
gainMismatchIsNotPhaseMismatch ()

record ArrayCalibrationResidualReceipt : Set where
  constructor array-calibration-residual-receipt
  field
    wanPartialCalibrationRetained :
      Snowball.SourceRoleSnowballReceipt Sources.wanPartialCalibrationPrimary
    liJointCalibrationRetained :
      Snowball.SourceRoleSnowballReceipt Sources.liJointCalibrationPrimary
    singhCouplingReviewRetained :
      Snowball.SourceRoleSnowballReceipt Sources.singhCouplingReview

    gainAndPhaseResidualsRemainDistinct :
      gainMismatchResidual ≡ phaseMismatchResidual → ⊥

    gainPhaseMismatchRelevantToDirectionFinding : Bool
    gainPhaseMismatchRelevantToDirectionFindingIsTrue :
      gainPhaseMismatchRelevantToDirectionFinding ≡ true

    mutualCouplingMayPerturbSteeringResponse : Bool
    mutualCouplingMayPerturbSteeringResponseIsTrue :
      mutualCouplingMayPerturbSteeringResponse ≡ true

    couplingReceiptRetained :
      Coupling.MutualCouplingObservationReceipt

    manifoldReceiptRetained :
      Manifold.ArrayManifoldReceipt

open ArrayCalibrationResidualReceipt public

canonicalArrayCalibrationResidualReceipt : ArrayCalibrationResidualReceipt
canonicalArrayCalibrationResidualReceipt =
  array-calibration-residual-receipt
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.wanPartialCalibrationPrimary)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.liJointCalibrationPrimary)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.singhCouplingReview)
    gainMismatchIsNotPhaseMismatch
    true refl
    true refl
    Coupling.canonicalMutualCouplingObservationReceipt
    Manifold.canonicalArrayManifoldReceipt

------------------------------------------------------------------------
-- PHASE-SHIFTER QUANTISATION
------------------------------------------------------------------------

data PhaseControlState : Set where
  idealContinuousPhaseControl : PhaseControlState
  quantisedPhaseControl : PhaseControlState

idealIsNotQuantised :
  idealContinuousPhaseControl ≡ quantisedPhaseControl → ⊥
idealIsNotQuantised ()

record PhaseQuantizationResidualReceipt : Set where
  constructor phase-quantization-residual-receipt
  field
    kamodaSourceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.kamodaQuantizationPrimary
    ieiceSourceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.ieiceQuantizationPrimary

    idealAndQuantisedControlRemainDistinct :
      idealContinuousPhaseControl ≡ quantisedPhaseControl → ⊥

    finitePhaseResolutionCreatesResidual : Bool
    finitePhaseResolutionCreatesResidualIsTrue :
      finitePhaseResolutionCreatesResidual ≡ true

    quantisationCanDegradeBeamformingGain : Bool
    quantisationCanDegradeBeamformingGainIsTrue :
      quantisationCanDegradeBeamformingGain ≡ true

    quantisationErrorEqualsBearing : Bool
    quantisationErrorEqualsBearingIsFalse :
      quantisationErrorEqualsBearing ≡ false

open PhaseQuantizationResidualReceipt public

canonicalPhaseQuantizationResidualReceipt :
  PhaseQuantizationResidualReceipt
canonicalPhaseQuantizationResidualReceipt =
  phase-quantization-residual-receipt
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.kamodaQuantizationPrimary)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.ieiceQuantizationPrimary)
    idealIsNotQuantised
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- RELEVANCE TO THE GONIOMETER / PHASED-ARRAY QUESTION
--
-- Historical mechanical goniometers and modern arrays share an angular
-- observation role, but their calibration residual vocabularies differ.
-- This is a structural comparison only; it does not assign modern array
-- calibration errors to a historical Cabarlah instrument.
------------------------------------------------------------------------

data CalibrationFamily : Set where
  mechanicalAngleCalibrationFamily : CalibrationFamily
  electronicGainPhaseCalibrationFamily : CalibrationFamily
  couplingManifoldCalibrationFamily : CalibrationFamily

mechanicalIsNotElectronic :
  mechanicalAngleCalibrationFamily ≡ electronicGainPhaseCalibrationFamily → ⊥
mechanicalIsNotElectronic ()

record GoniometerCalibrationRelevanceReceipt : Set where
  constructor goniometer-calibration-relevance-receipt
  field
    mechanicalGoniometerAngleRoleRetained :
      Goniometer.implementationRole Goniometer.mechanicalAngleReadout
      ≡ Goniometer.angleEstimationRole

    phaseComparisonAngleRoleRetained :
      Goniometer.implementationRole Goniometer.phaseComparison
      ≡ Goniometer.angleEstimationRole

    phasedArrayAngularRoleRetained :
      Array.supportsAngularObservation Array.electronicallySteeredPhasedArray
      ≡ Array.angularObservationRole

    mechanicalAndElectronicCalibrationFamiliesDistinct :
      mechanicalAngleCalibrationFamily
      ≡ electronicGainPhaseCalibrationFamily → ⊥

    sameAngleRoleImpliesSameCalibrationModel : Bool
    sameAngleRoleImpliesSameCalibrationModelIsFalse :
      sameAngleRoleImpliesSameCalibrationModel ≡ false

    calibrationResidualMayAffectAngularAccuracy : Bool
    calibrationResidualMayAffectAngularAccuracyIsTrue :
      calibrationResidualMayAffectAngularAccuracy ≡ true

open GoniometerCalibrationRelevanceReceipt public

canonicalGoniometerCalibrationRelevanceReceipt :
  GoniometerCalibrationRelevanceReceipt
canonicalGoniometerCalibrationRelevanceReceipt =
  goniometer-calibration-relevance-receipt
    refl
    refl
    refl
    mechanicalIsNotElectronic
    false refl
    true refl

------------------------------------------------------------------------
-- ORIGINAL-TASK RELEVANCE BOUNDARY
------------------------------------------------------------------------

record OriginalTaskRelevanceBoundary : Set where
  constructor original-task-relevance-boundary
  field
    calibrationExplainsImplementationDifference : Bool
    calibrationExplainsImplementationDifferenceIsTrue :
      calibrationExplainsImplementationDifference ≡ true

    calibrationPreservesCommonAngleRole : Bool
    calibrationPreservesCommonAngleRoleIsTrue :
      calibrationPreservesCommonAngleRole ≡ true

    modernCalibrationModelIdentifiesHistoricalInstrument : Bool
    modernCalibrationModelIdentifiesHistoricalInstrumentIsFalse :
      modernCalibrationModelIdentifiesHistoricalInstrument ≡ false

    cabarlahDFHistoryProvesModernGainPhaseCalibration : Bool
    cabarlahDFHistoryProvesModernGainPhaseCalibrationIsFalse :
      cabarlahDFHistoryProvesModernGainPhaseCalibration ≡ false

    smithChartCalibrationEqualsDirectionFinding : Bool
    smithChartCalibrationEqualsDirectionFindingIsFalse :
      smithChartCalibrationEqualsDirectionFinding ≡ false

    calibrationErrorDeterminesExactWorld : Bool
    calibrationErrorDeterminesExactWorldIsFalse :
      calibrationErrorDeterminesExactWorld ≡ false

open OriginalTaskRelevanceBoundary public

canonicalOriginalTaskRelevanceBoundary : OriginalTaskRelevanceBoundary
canonicalOriginalTaskRelevanceBoundary =
  original-task-relevance-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
