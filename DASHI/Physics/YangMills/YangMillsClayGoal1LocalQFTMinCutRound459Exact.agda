{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1LocalQFTMinCutRound459Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND459: LOCAL-QFT (C) MIN-CUT ON ONE SAME-FAMILY OBJECT.
--
-- The modern C lane no longer needs:
--   * a new continuum stress-convergence theorem,
--   * a new OPE remainder decay proof,
--   * an all-depth OPE coefficient comparison,
--   * or the optional Q_T = H_OS common-core theorem.
--
-- The remaining physical work is four same-family attachments:
--
--   C1  literal Round109 completed curvature/stress source;
--   C2  literal physical OPE remainder = shared marked composite tail;
--   C3  literal OPE coefficient uses the SAME one-step AF/RG mixing law and UV
--       normalization;
--   C4  instantiate the density-anchored Round123 stress lane on the literal
--       finite/continuum/Schwinger family.
--
-- R442 gives the quantitative OPE modulus after C2.
-- recurrence uniqueness gives all-depth coefficient equality after C3.
-- R129/R131 give continuum stress recovery and first-variation pairing after C4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayGoal1CanonicalCSourceRound437Exact as R437
import DASHI.Physics.YangMills.YangMillsPhysicalOPERemainderSharedTailRound442Exact as R442
import DASHI.Physics.YangMills.BalabanOPECoefficientRGRecurrenceUniquenessExact as Recurrence
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as R129
import DASHI.Physics.YangMills.BalabanCommonMetricSectorRecoveryRound131Exact as R131
import DASHI.Physics.YangMills.YangMillsClayGoal1StressSourceRound466Exact as R466

c1LiteralSameCompletedCurvatureStressLevel : ProofLevel
c1LiteralSameCompletedCurvatureStressLevel =
  R437.literalRound437Goal1CSourceLevel

c2PhysicalRemainderIsMarkedTailLevel : ProofLevel
c2PhysicalRemainderIsMarkedTailLevel =
  R442.literalRound442PhysicalRemainderIsCompositeTailLevel

c2QuantitativeRemainderDecayAfterIdentityLevel : ProofLevel
c2QuantitativeRemainderDecayAfterIdentityLevel =
  R442.round442PhysicalOPERemainderCompilerLevel

c3PhysicalOneStepAFRGIdentificationLevel : ProofLevel
c3PhysicalOneStepAFRGIdentificationLevel =
  Recurrence.physicalSameFamilyOPECoefficientOneStepAFIdentificationLevel

c3AllDepthCoefficientEqualityAfterOneStepLevel : ProofLevel
c3AllDepthCoefficientEqualityAfterOneStepLevel =
  Recurrence.coefficientRGRecurrenceUniquenessLevel

c1c4FiniteSameFamilyStressSourceLevel : ProofLevel
c1c4FiniteSameFamilyStressSourceLevel =
  R466.s12DensityAnchoredStressLaneLevel

c1c4LiteralDensityDerivativeLevel : ProofLevel
c1c4LiteralDensityDerivativeLevel =
  R466.s2LiteralDensityNumeratorDenominatorDerivativeLevel

c1c4SameFamilyOSRecoveryLevel : ProofLevel
c1c4SameFamilyOSRecoveryLevel =
  R466.s3SameFamilyOSStressRecoveryLevel

c4DensityAnchoredLiteralStressLaneFallbackLevel : ProofLevel
c4DensityAnchoredLiteralStressLaneFallbackLevel =
  R123.literalDensityAnchoredStressLaneInstantiationLevel

c4ContinuumStressRecoveryAfterLaneLevel : ProofLevel
c4ContinuumStressRecoveryAfterLaneLevel =
  R129.balabanSectorQFTRecoveryExportCompilerLevel

c4MetricFirstVariationPairingAfterLaneLevel : ProofLevel
c4MetricFirstVariationPairingAfterLaneLevel =
  R131.commonMetricReadyBalabanSectorCompilerLevel

freshWardConvergenceTheoremMandatory : Bool
freshWardConvergenceTheoremMandatory = false

freshOPERemainderDecayTheoremMandatory : Bool
freshOPERemainderDecayTheoremMandatory = false

allDepthOPECoefficientComparisonMandatory : Bool
allDepthOPECoefficientComparisonMandatory = false

commonCoreQTEqualsHOSMandatoryForGoal1 : Bool
commonCoreQTEqualsHOSMandatoryForGoal1 = false

round459LocalQFTMinCutCompilerLevel : ProofLevel
round459LocalQFTMinCutCompilerLevel = machineChecked
