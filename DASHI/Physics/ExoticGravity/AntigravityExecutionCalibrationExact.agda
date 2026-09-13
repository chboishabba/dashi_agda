module DASHI.Physics.ExoticGravity.AntigravityExecutionCalibrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.CalibratedExperimentInferenceExact as Calibrated
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- TYPED CALIBRATION RECEIPT
--
-- A string naming a calibration file is not enough.  This adapter reuses the
-- existing CalibratedExperimentInferenceExact DataRefinement certificate and
-- binds the refined evidence to a stable carrier.  The execution owners then
-- bind that carrier to the exact raw-data carrier they consume.
------------------------------------------------------------------------

record ExecutionCalibrationReceipt : Set₁ where
  constructor execution-calibration-receipt
  field
    family : Calibrated.ExperimentFamily
    evidenceCarrier : Calibrated.Evidence family → String
    evidenceRefinement : Calibrated.DataRefinement family

    refinedEvidenceCarrier : String
    refinedEvidenceCarrierMatches :
      evidenceCarrier (Calibrated.refinedEvidence evidenceRefinement)
        ≡ refinedEvidenceCarrier

    previousEvidenceCarrier : String
    previousEvidenceCarrierMatches :
      evidenceCarrier (Calibrated.previousEvidence evidenceRefinement)
        ≡ previousEvidenceCarrier

    calibrationCarrier : String
    calibrationRevision : String
    instrumentConfigurationCarrier : String

    CalibrationAdequacy : Set
    calibrationAdequacy : CalibrationAdequacy

open ExecutionCalibrationReceipt public

------------------------------------------------------------------------
-- Reverse residuals.
------------------------------------------------------------------------

data ExecutionCalibrationResidual : Set where
  missingExperimentFamily : ExecutionCalibrationResidual
  missingEvidenceCarrierMap : ExecutionCalibrationResidual
  missingDataRefinement : ExecutionCalibrationResidual
  missingRefinedEvidenceBinding : ExecutionCalibrationResidual
  missingPreviousEvidenceBinding : ExecutionCalibrationResidual
  missingCalibrationCarrier : ExecutionCalibrationResidual
  missingCalibrationRevision : ExecutionCalibrationResidual
  missingInstrumentConfiguration : ExecutionCalibrationResidual
  missingCalibrationAdequacyWitness : ExecutionCalibrationResidual

producerForExecutionCalibrationResidual :
  ExecutionCalibrationResidual → Search.ProducerClass
producerForExecutionCalibrationResidual missingExperimentFamily = Search.identityProducer
producerForExecutionCalibrationResidual missingEvidenceCarrierMap = Search.identityProducer
producerForExecutionCalibrationResidual missingDataRefinement = Search.empiricalEvidenceProducer
producerForExecutionCalibrationResidual missingRefinedEvidenceBinding = Search.identityProducer
producerForExecutionCalibrationResidual missingPreviousEvidenceBinding = Search.identityProducer
producerForExecutionCalibrationResidual missingCalibrationCarrier = Search.empiricalEvidenceProducer
producerForExecutionCalibrationResidual missingCalibrationRevision = Search.temporalProducer
producerForExecutionCalibrationResidual missingInstrumentConfiguration = Search.empiricalEvidenceProducer
producerForExecutionCalibrationResidual missingCalibrationAdequacyWitness = Search.discriminatorProducer

------------------------------------------------------------------------
-- Boundary.  Calibration/refinement authority stays weaker than sensitivity,
-- mechanism, or posterior/coverage claims.
------------------------------------------------------------------------

record ExecutionCalibrationBoundary : Set where
  constructor execution-calibration-boundary
  field
    calibrationCarrierStringEqualsTypedRefinement : Bool
    typedDataRefinementRequired : Bool
    refinedEvidenceMustBindExecutionData : Bool
    calibrationAutomaticallyCertifiesSensitivity : Bool
    calibrationAutomaticallyValidatesPhysicalMechanism : Bool
    calibrationAutomaticallyCreatesPosteriorSupport : Bool

canonicalExecutionCalibrationBoundary : ExecutionCalibrationBoundary
canonicalExecutionCalibrationBoundary =
  execution-calibration-boundary false true true false false false

existingCalibratedExperimentBoundary : Calibrated.CalibratedExperimentBoundary
existingCalibratedExperimentBoundary = Calibrated.canonicalCalibratedExperimentBoundary
