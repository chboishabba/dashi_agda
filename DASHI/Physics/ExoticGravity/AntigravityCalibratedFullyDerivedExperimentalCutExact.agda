module DASHI.Physics.ExoticGravity.AntigravityCalibratedFullyDerivedExperimentalCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravitySourceBundleDerivationLineageExact as SourceDerivation
import DASHI.Physics.ExoticGravity.AntigravityExperimentalCutProvenanceExact as Provenance
import DASHI.Physics.ExoticGravity.AntigravityFullyDerivedExperimentalCutExact as FullyDerived
import DASHI.Physics.ExoticGravity.AntigravityCalibratedExecutionBridgeExact as Calibrated
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- CALIBRATED + FULLY DERIVED SAME-APPARATUS CUT
------------------------------------------------------------------------

record CalibratedFullyDerivedSameApparatusExperimentalCut : Set₁ where
  constructor calibrated-fully-derived-same-apparatus-experimental-cut
  field
    fullyDerivedCut : FullyDerived.FullyDerivedSameApparatusExperimentalCut

    sourceAcquisitionCalibration :
      Calibrated.CalibratedSourceAcquisition
        (SourceDerivation.acquisition
          (Provenance.sourceReceipt
            (FullyDerived.provenancedCut fullyDerivedCut)))

    sourceExecutionCalibration :
      Calibrated.CalibratedBundleExecution
        (Provenance.sourceExecution
          (FullyDerived.provenancedCut fullyDerivedCut))

    sourceAcquisitionExecutionIdentity :
      Calibrated.SourceExecutionIdentityWeld
        (SourceDerivation.acquisition
          (Provenance.sourceReceipt
            (FullyDerived.provenancedCut fullyDerivedCut)))
        (Provenance.sourceExecution
          (FullyDerived.provenancedCut fullyDerivedCut))

    sourceTypedCalibrationIsSame :
      Calibrated.calibration sourceAcquisitionCalibration
        ≡ Calibrated.calibration sourceExecutionCalibration

    phaseProbeCalibration :
      Calibrated.CalibratedBundleExecution
        (Provenance.phaseProbeExecution
          (FullyDerived.provenancedCut fullyDerivedCut))

    ordinaryModelCalibration :
      Calibrated.CalibratedBundleExecution
        (Provenance.ordinaryModelExecution
          (FullyDerived.provenancedCut fullyDerivedCut))

    scalingReplicationCalibration :
      Calibrated.CalibratedBundleExecution
        (Provenance.scalingReplicationExecution
          (FullyDerived.provenancedCut fullyDerivedCut))

open CalibratedFullyDerivedSameApparatusExperimentalCut public

record CalibratedFullyDerivedComparativeAnomalyReceipt
    (claim : Anti.AntigravityClaim) : Set₁ where
  constructor calibrated-fully-derived-comparative-anomaly-receipt
  field
    experimentalCut : CalibratedFullyDerivedSameApparatusExperimentalCut
    anomaly : FullyDerived.FullyDerivedComparativeAnomalyReceipt claim
    anomalyCutMatches :
      FullyDerived.experimentalCut anomaly
        ≡ fullyDerivedCut experimentalCut

open CalibratedFullyDerivedComparativeAnomalyReceipt public

------------------------------------------------------------------------
-- Reverse residuals.
------------------------------------------------------------------------

data CalibratedFullyDerivedCutResidual : Set where
  missingSourceAcquisitionCalibration : CalibratedFullyDerivedCutResidual
  missingSourceExecutionCalibration : CalibratedFullyDerivedCutResidual
  missingSourceAcquisitionExecutionIdentity : CalibratedFullyDerivedCutResidual
  sourceTypedCalibrationsDiffer : CalibratedFullyDerivedCutResidual
  missingPhaseProbeCalibration : CalibratedFullyDerivedCutResidual
  missingOrdinaryModelCalibration : CalibratedFullyDerivedCutResidual
  missingScalingReplicationCalibration : CalibratedFullyDerivedCutResidual
  missingCalibratedAnomalyCutIdentity : CalibratedFullyDerivedCutResidual

producerForCalibratedFullyDerivedResidual :
  CalibratedFullyDerivedCutResidual → Search.ProducerClass
producerForCalibratedFullyDerivedResidual missingSourceAcquisitionCalibration = Search.empiricalEvidenceProducer
producerForCalibratedFullyDerivedResidual missingSourceExecutionCalibration = Search.empiricalEvidenceProducer
producerForCalibratedFullyDerivedResidual missingSourceAcquisitionExecutionIdentity = Search.identityProducer
producerForCalibratedFullyDerivedResidual sourceTypedCalibrationsDiffer = Search.identityProducer
producerForCalibratedFullyDerivedResidual missingPhaseProbeCalibration = Search.empiricalEvidenceProducer
producerForCalibratedFullyDerivedResidual missingOrdinaryModelCalibration = Search.empiricalEvidenceProducer
producerForCalibratedFullyDerivedResidual missingScalingReplicationCalibration = Search.empiricalEvidenceProducer
producerForCalibratedFullyDerivedResidual missingCalibratedAnomalyCutIdentity = Search.identityProducer

data CurrentCalibratedFullyDerivedCutAuthority : Set where

noCurrentCalibratedFullyDerivedCut :
  CurrentCalibratedFullyDerivedCutAuthority →
  CalibratedFullyDerivedSameApparatusExperimentalCut
noCurrentCalibratedFullyDerivedCut ()

record CalibratedFullyDerivedBoundary : Set where
  constructor calibrated-fully-derived-boundary
  field
    provenanceStringsAlonePayCalibration : Bool
    sourceAcquisitionAndExecutionMustBeSameRun : Bool
    sourceTypedCalibrationMustBeSameObject : Bool
    allFourStagesNeedTypedCalibration : Bool
    calibratedFullyDerivedCutAutomaticallyProvesMechanism : Bool
    calibratedFullyDerivedCutAutomaticallyProvesUniversalLaw : Bool

canonicalCalibratedFullyDerivedBoundary : CalibratedFullyDerivedBoundary
canonicalCalibratedFullyDerivedBoundary =
  calibrated-fully-derived-boundary false true true true false false
