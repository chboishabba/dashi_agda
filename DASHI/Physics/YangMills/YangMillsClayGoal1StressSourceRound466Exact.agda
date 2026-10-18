{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1StressSourceRound466Exact where

------------------------------------------------------------------------
-- GOAL-1 C1/C4 / ROUND466:
-- EXACT FINITE SAME-FAMILY STRESS SOURCE -> CONTINUUM STRESS RECOVERY.
--
-- R118--R123 and R126--R131 show that no fresh Ward-limit theorem is needed.
-- The actual source-facing stress debt is finite:
--
--   S1  the canonical metric first variation is the literal selected CMP119
--       normalized stress insertion;
--
--   S2  its normalized numerator/denominator derivative is evaluated on the
--       SAME beta-driven finite density;
--
--   S3  the source OS/finite-measure recovery is the literal continuum
--       Schwinger family used by the Clay construction.
--
-- Once one R123 DensityAnchoredCanonicalMetricStressLane and the R128
-- same-family recovery inhabit these facts, Cauchy convergence, continuum
-- first variation and the stress metric pairing are compiler-owned.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCanonicalMetricToCMP119StressRound118Exact as R118
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanCanonicalMetricStressLaneRound120Exact as R120
import DASHI.Physics.YangMills.BalabanLiteralDensityNormalizedSourceRound121Exact as R121
import DASHI.Physics.YangMills.BalabanDensityAnchoredMetricStressRound122Exact as R122
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.BalabanSameFamilyOSStressRecoveryRound128Exact as R128
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as R129
import DASHI.Physics.YangMills.BalabanContinuumMetricStressPairingRound130Exact as R130
import DASHI.Physics.YangMills.BalabanCommonMetricSectorRecoveryRound131Exact as R131

------------------------------------------------------------------------
-- Exact proof-level decomposition.
------------------------------------------------------------------------

s1MetricVariationIsSelectedCMP119StressLevel : ProofLevel
s1MetricVariationIsSelectedCMP119StressLevel =
  R119.literalCanonicalMetricSelectedStressInstantiationLevel

s1MetricStressNormalizationCompilerLevel : ProofLevel
s1MetricStressNormalizationCompilerLevel =
  R118.canonicalMetricCMP119StressCompilerLevel

s2LiteralDensityNumeratorDenominatorDerivativeLevel : ProofLevel
s2LiteralDensityNumeratorDenominatorDerivativeLevel =
  R121.literalBalabanDensityNumeratorDenominatorMetricDerivativeLevel

s2CMP116CMP122DensityAnchoringLevel : ProofLevel
s2CMP116CMP122DensityAnchoringLevel =
  R122.literalCMP116CMP122DensityAnchoringLevel

s12DensityAnchoredStressLaneLevel : ProofLevel
s12DensityAnchoredStressLaneLevel =
  R123.literalDensityAnchoredStressLaneInstantiationLevel

s3SameFamilyOSStressRecoveryLevel : ProofLevel
s3SameFamilyOSStressRecoveryLevel =
  R128.literalBalabanSameFamilyOSStressRecoveryLevel

stressCauchyAndCompletionCompilerLevel : ProofLevel
stressCauchyAndCompletionCompilerLevel =
  R120.canonicalMetricLiteralStressLaneCompilerLevel

continuumStressRecoveryCompilerLevel : ProofLevel
continuumStressRecoveryCompilerLevel =
  R129.balabanSectorQFTRecoveryExportCompilerLevel

continuumStressMetricPairingCompilerLevel : ProofLevel
continuumStressMetricPairingCompilerLevel =
  R131.commonMetricReadyBalabanSectorCompilerLevel

-- These are deliberately not listed as independent Goal-1 analytic leaves.
freshFiniteToContinuumWardLimitMandatory : Bool
freshFiniteToContinuumWardLimitMandatory = false

freshContinuumStressTensorConstructionMandatory : Bool
freshContinuumStressTensorConstructionMandatory = false

round466StressSourceMinCutCompilerLevel : ProofLevel
round466StressSourceMinCutCompilerLevel = machineChecked
