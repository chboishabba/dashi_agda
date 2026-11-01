module DASHI.Physics.ExoticGravity.AntigravityClaimScopedExperimentalCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityCalibratedExecutionBridgeExact as CalibratedExecution
import DASHI.Physics.ExoticGravity.AntigravityCalibratedFullyDerivedExperimentalCutExact as CalibratedCut
import DASHI.Physics.ExoticGravity.AntigravityConsumerScopedCalibrationExact as ConsumerCalibration
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- CLAIM-SCOPED CALIBRATED EXPERIMENTAL CUT
--
-- The same physical execution may be reusable for several consumers only after
-- a consumer-specific adequacy receipt is supplied.  Every stage below is
-- therefore indexed by the exact antigravity claim whose comparison will consume
-- the experimental cut.
------------------------------------------------------------------------

record ClaimScopedCalibratedExperimentalCut
    (claim : Anti.AntigravityClaim) : Set₁ where
  constructor claim-scoped-calibrated-experimental-cut
  field
    calibratedCut : CalibratedCut.CalibratedFullyDerivedSameApparatusExperimentalCut

    sourceCalibrationScope : ConsumerCalibration.ConsumerScopedCalibration claim
    sourceCalibrationMatches :
      ConsumerCalibration.calibration sourceCalibrationScope
        ≡ CalibratedExecution.sourceCalibration
            (CalibratedCut.sourceAcquisitionCalibration calibratedCut)

    phaseProbeCalibrationScope : ConsumerCalibration.ConsumerScopedCalibration claim
    phaseProbeCalibrationMatches :
      ConsumerCalibration.calibration phaseProbeCalibrationScope
        ≡ CalibratedExecution.bundleCalibration
            (CalibratedCut.phaseProbeCalibration calibratedCut)

    ordinaryModelCalibrationScope : ConsumerCalibration.ConsumerScopedCalibration claim
    ordinaryModelCalibrationMatches :
      ConsumerCalibration.calibration ordinaryModelCalibrationScope
        ≡ CalibratedExecution.bundleCalibration
            (CalibratedCut.ordinaryModelCalibration calibratedCut)

    scalingReplicationCalibrationScope : ConsumerCalibration.ConsumerScopedCalibration claim
    scalingReplicationCalibrationMatches :
      ConsumerCalibration.calibration scalingReplicationCalibrationScope
        ≡ CalibratedExecution.bundleCalibration
            (CalibratedCut.scalingReplicationCalibration calibratedCut)

open ClaimScopedCalibratedExperimentalCut public

------------------------------------------------------------------------
-- Reverse residuals.
------------------------------------------------------------------------

data ClaimScopedCutResidual : Set where
  missingSourceConsumerCalibration : ClaimScopedCutResidual
  missingPhaseProbeConsumerCalibration : ClaimScopedCutResidual
  missingOrdinaryModelConsumerCalibration : ClaimScopedCutResidual
  missingScalingReplicationConsumerCalibration : ClaimScopedCutResidual
  sourceCalibrationObjectMismatch : ClaimScopedCutResidual
  phaseProbeCalibrationObjectMismatch : ClaimScopedCutResidual
  ordinaryModelCalibrationObjectMismatch : ClaimScopedCutResidual
  scalingReplicationCalibrationObjectMismatch : ClaimScopedCutResidual

producerForClaimScopedCutResidual :
  ClaimScopedCutResidual → Search.ProducerClass
producerForClaimScopedCutResidual missingSourceConsumerCalibration = Search.empiricalEvidenceProducer
producerForClaimScopedCutResidual missingPhaseProbeConsumerCalibration = Search.empiricalEvidenceProducer
producerForClaimScopedCutResidual missingOrdinaryModelConsumerCalibration = Search.empiricalEvidenceProducer
producerForClaimScopedCutResidual missingScalingReplicationConsumerCalibration = Search.empiricalEvidenceProducer
producerForClaimScopedCutResidual sourceCalibrationObjectMismatch = Search.identityProducer
producerForClaimScopedCutResidual phaseProbeCalibrationObjectMismatch = Search.identityProducer
producerForClaimScopedCutResidual ordinaryModelCalibrationObjectMismatch = Search.identityProducer
producerForClaimScopedCutResidual scalingReplicationCalibrationObjectMismatch = Search.identityProducer

data CurrentClaimScopedCutAuthority : Set where

noCurrentClaimScopedCut :
  {claim : Anti.AntigravityClaim} →
  CurrentClaimScopedCutAuthority → ClaimScopedCalibratedExperimentalCut claim
noCurrentClaimScopedCut ()

record ClaimScopedCutBoundary : Set where
  constructor claim-scoped-cut-boundary
  field
    genericTypedCalibrationAutomaticallyPaysClaimScope : Bool
    allFourStagesMustMatchSameClaimConsumer : Bool
    sameCalibrationCarrierAutomaticallyMeansSameCalibrationObject : Bool
    claimScopedCutAutomaticallyProvesClaim : Bool

canonicalClaimScopedCutBoundary : ClaimScopedCutBoundary
canonicalClaimScopedCutBoundary =
  claim-scoped-cut-boundary false true false false
