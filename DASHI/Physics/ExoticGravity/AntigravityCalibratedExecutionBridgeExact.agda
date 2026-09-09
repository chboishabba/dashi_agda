module DASHI.Physics.ExoticGravity.AntigravityCalibratedExecutionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityExecutionCalibrationExact as Calibration
import DASHI.Physics.ExoticGravity.AntigravitySourceAcquisitionCompilationExact as Source
import DASHI.Physics.ExoticGravity.AntigravityExperimentalCutProvenanceExact as Provenance
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- TYPED CALIBRATION -> EXECUTION PROVENANCE
------------------------------------------------------------------------

record CalibratedSourceAcquisition
    (receipt : Source.SourceAcquisitionReceipt) : Set₁ where
  constructor calibrated-source-acquisition
  field
    calibration : Calibration.ExecutionCalibrationReceipt
    refinedEvidenceMatchesRawData :
      Calibration.refinedEvidenceCarrier calibration
        ≡ Source.rawDataCarrier (Source.provenance receipt)
    calibrationCarrierMatches :
      Calibration.calibrationCarrier calibration
        ≡ Source.calibrationCarrier (Source.provenance receipt)
    calibrationRevisionMatches :
      Calibration.calibrationRevision calibration
        ≡ Source.calibrationRevision (Source.provenance receipt)
    instrumentConfigurationMatches :
      Calibration.instrumentConfigurationCarrier calibration
        ≡ Source.instrumentConfigurationCarrier (Source.provenance receipt)

open CalibratedSourceAcquisition public

record CalibratedBundleExecution
    (execution : Provenance.BundleExecutionProvenance) : Set₁ where
  constructor calibrated-bundle-execution
  field
    calibration : Calibration.ExecutionCalibrationReceipt
    refinedEvidenceMatchesRawData :
      Calibration.refinedEvidenceCarrier calibration
        ≡ Provenance.rawDataCarrier execution
    calibrationCarrierMatches :
      Calibration.calibrationCarrier calibration
        ≡ Provenance.calibrationCarrier execution
    calibrationRevisionMatches :
      Calibration.calibrationRevision calibration
        ≡ Provenance.calibrationRevision execution
    instrumentConfigurationMatches :
      Calibration.instrumentConfigurationCarrier calibration
        ≡ Provenance.instrumentConfigurationCarrier execution

open CalibratedBundleExecution public

------------------------------------------------------------------------
-- SOURCE ACQUISITION <-> SOURCE EXECUTION SAME-OBJECT WELD
------------------------------------------------------------------------

record SourceExecutionIdentityWeld
    (receipt : Source.SourceAcquisitionReceipt)
    (execution : Provenance.BundleExecutionProvenance) : Set where
  constructor source-execution-identity-weld
  field
    runIdentifierMatches :
      Provenance.runIdentifier execution
        ≡ Source.runIdentifier (Source.provenance receipt)
    rawDataCarrierMatches :
      Provenance.rawDataCarrier execution
        ≡ Source.rawDataCarrier (Source.provenance receipt)
    rawDataHashMatches :
      Provenance.rawDataHash execution
        ≡ Source.rawDataHash (Source.provenance receipt)
    dataRevisionMatches :
      Provenance.dataRevision execution
        ≡ Source.dataRevision (Source.provenance receipt)
    instrumentConfigurationMatches :
      Provenance.instrumentConfigurationCarrier execution
        ≡ Source.instrumentConfigurationCarrier (Source.provenance receipt)
    calibrationCarrierMatches :
      Provenance.calibrationCarrier execution
        ≡ Source.calibrationCarrier (Source.provenance receipt)
    calibrationRevisionMatches :
      Provenance.calibrationRevision execution
        ≡ Source.calibrationRevision (Source.provenance receipt)

open SourceExecutionIdentityWeld public

------------------------------------------------------------------------
-- Reverse residuals.
------------------------------------------------------------------------

data CalibratedExecutionResidual : Set where
  missingTypedCalibration : CalibratedExecutionResidual
  calibrationEvidenceDoesNotMatchRawData : CalibratedExecutionResidual
  calibrationCarrierMismatch : CalibratedExecutionResidual
  calibrationRevisionMismatch : CalibratedExecutionResidual
  instrumentConfigurationMismatch : CalibratedExecutionResidual
  missingSourceExecutionIdentityWeld : CalibratedExecutionResidual

producerForCalibratedExecutionResidual :
  CalibratedExecutionResidual → Search.ProducerClass
producerForCalibratedExecutionResidual missingTypedCalibration = Search.empiricalEvidenceProducer
producerForCalibratedExecutionResidual calibrationEvidenceDoesNotMatchRawData = Search.identityProducer
producerForCalibratedExecutionResidual calibrationCarrierMismatch = Search.identityProducer
producerForCalibratedExecutionResidual calibrationRevisionMismatch = Search.temporalProducer
producerForCalibratedExecutionResidual instrumentConfigurationMismatch = Search.identityProducer
producerForCalibratedExecutionResidual missingSourceExecutionIdentityWeld = Search.identityProducer

record CalibratedExecutionBridgeBoundary : Set where
  constructor calibrated-execution-bridge-boundary
  field
    calibrationStringAlonePaysTypedCalibration : Bool
    refinedEvidenceMustBeExactExecutionData : Bool
    calibrationRevisionMustMatchExecution : Bool
    instrumentConfigurationMustMatchExecution : Bool
    sameApparatusLabelAloneWeldsSourceReceiptToExecution : Bool
    calibratedExecutionAutomaticallyValidatesMechanism : Bool

canonicalCalibratedExecutionBridgeBoundary : CalibratedExecutionBridgeBoundary
canonicalCalibratedExecutionBridgeBoundary =
  calibrated-execution-bridge-boundary false true true true false false
