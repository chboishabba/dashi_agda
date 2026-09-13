module DASHI.Physics.ExoticGravity.AntigravityCalibratedExecutionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityExecutionCalibrationExact as Calibration
import DASHI.Physics.ExoticGravity.AntigravitySourceAcquisitionCompilationExact as Source
import DASHI.Physics.ExoticGravity.AntigravityExperimentalCutProvenanceExact as Provenance
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- TYPED CALIBRATION -> EXECUTION PROVENANCE
--
-- Projection names are deliberately record-specific so no downstream consumer
-- relies on ambiguous open-record fields.
------------------------------------------------------------------------

record CalibratedSourceAcquisition
    (receipt : Source.SourceAcquisitionReceipt) : Set₁ where
  constructor calibrated-source-acquisition
  field
    sourceCalibration : Calibration.ExecutionCalibrationReceipt
    sourceRefinedEvidenceMatchesRawData :
      Calibration.refinedEvidenceCarrier sourceCalibration
        ≡ Source.rawDataCarrier (Source.provenance receipt)
    sourceCalibrationCarrierMatches :
      Calibration.calibrationCarrier sourceCalibration
        ≡ Source.calibrationCarrier (Source.provenance receipt)
    sourceCalibrationRevisionMatches :
      Calibration.calibrationRevision sourceCalibration
        ≡ Source.calibrationRevision (Source.provenance receipt)
    sourceInstrumentConfigurationMatches :
      Calibration.instrumentConfigurationCarrier sourceCalibration
        ≡ Source.instrumentConfigurationCarrier (Source.provenance receipt)

open CalibratedSourceAcquisition public

record CalibratedBundleExecution
    (execution : Provenance.BundleExecutionProvenance) : Set₁ where
  constructor calibrated-bundle-execution
  field
    bundleCalibration : Calibration.ExecutionCalibrationReceipt
    bundleRefinedEvidenceMatchesRawData :
      Calibration.refinedEvidenceCarrier bundleCalibration
        ≡ Provenance.rawDataCarrier execution
    bundleCalibrationCarrierMatches :
      Calibration.calibrationCarrier bundleCalibration
        ≡ Provenance.calibrationCarrier execution
    bundleCalibrationRevisionMatches :
      Calibration.calibrationRevision bundleCalibration
        ≡ Provenance.calibrationRevision execution
    bundleInstrumentConfigurationMatches :
      Calibration.instrumentConfigurationCarrier bundleCalibration
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
    sourceExecutionApparatusMatches :
      Provenance.apparatusCarrier execution
        ≡ Source.apparatusIdentityCarrier (Source.provenance receipt)
    sourceExecutionRunIdentifierMatches :
      Provenance.runIdentifier execution
        ≡ Source.runIdentifier (Source.provenance receipt)
    sourceExecutionRawDataCarrierMatches :
      Provenance.rawDataCarrier execution
        ≡ Source.rawDataCarrier (Source.provenance receipt)
    sourceExecutionRawDataHashMatches :
      Provenance.rawDataHash execution
        ≡ Source.rawDataHash (Source.provenance receipt)
    sourceExecutionDataRevisionMatches :
      Provenance.dataRevision execution
        ≡ Source.dataRevision (Source.provenance receipt)
    sourceExecutionInstrumentConfigurationMatches :
      Provenance.instrumentConfigurationCarrier execution
        ≡ Source.instrumentConfigurationCarrier (Source.provenance receipt)
    sourceExecutionCalibrationCarrierMatches :
      Provenance.calibrationCarrier execution
        ≡ Source.calibrationCarrier (Source.provenance receipt)
    sourceExecutionCalibrationRevisionMatches :
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
    apparatusIdentityAndRunIdentityAreDistinct : Bool
    sameApparatusLabelAloneWeldsSourceReceiptToExecution : Bool
    calibratedExecutionAutomaticallyValidatesMechanism : Bool

canonicalCalibratedExecutionBridgeBoundary : CalibratedExecutionBridgeBoundary
canonicalCalibratedExecutionBridgeBoundary =
  calibrated-execution-bridge-boundary false true true true true false false
