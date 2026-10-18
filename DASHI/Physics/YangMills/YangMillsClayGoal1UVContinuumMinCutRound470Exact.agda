{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1UVContinuumMinCutRound470Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND470: CURRENT UV -> CONTINUUM MIN-CUT.
--
-- This replaces the stale "A1--A5 + three historical RG lemmas" picture with
-- the least-privilege source-facing obligations after R461--R467.
--
-- Published / compiler-owned:
--   * finite Euclidean/bosonic symmetry source application (R462);
--   * finite Wilson reflection positivity source application (R461);
--   * common CMP116 source domains / baseline finite RG stability;
--   * canonical expectation-limit algebra;
--   * source-native finite->continuum/Schwinger same-family compiler (R126-128);
--   * canonical OS0/OS5 limit closure once finite predicates are supplied.
--
-- Genuine physical UV/continuum leaves:
--
--   U1  arbitrary compact-simple selected-background/KKT/Green source map
--       producing the group-parametric five-block estimate;
--
--   U2  literal Wilson+FP+Haar one-loop normalization in the project/source
--       convention, sufficient to enter the positive-beta CMP122 trajectory;
--
--   U3  source-native physical unified one-step YM estimate on the ACTUAL
--       imported CMP122 complete density, carrying the strengthened composite /
--       weighted-correlation / characteristic coordinates needed by Goal-1;
--
--   U4  literal finite Balaban family -> declared continuum measure/Schwinger
--       family + literal source-OS Schwinger weld (R126--R128);
--
--   U5  quantitative finite moment/distribution estimates instantiate the
--       selected finite OS0/OS5 predicates (R464).
--
-- A1/A2 are source applications, not fresh analysis; projective Prokhorov and
-- explicit Peter-Weyl/Haar reconstructions remain optional audit routes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanGroupParametricFiveBlockSignedG2Exact as G2
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound73EightAnalyticCutsetExact as R73
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound76SixAnalyticCutsetExact as R76
import DASHI.Physics.YangMills.BalabanSameFamilyOSStressRecoveryRound128Exact as R128
import DASHI.Physics.YangMills.YangMillsClayPublishedWilsonRPRound461Exact as R461
import DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSSourceRound462Exact as R462
import DASHI.Physics.YangMills.YangMillsClayGoal1A1SourceCutRound473Exact as R473
import DASHI.Physics.YangMills.BalabanA2BetaMarkSourceCoordinateRound250Exact as R250
import DASHI.Physics.YangMills.YangMillsClayT5MomentToOS05Round464Exact as R464

preferredA1CurrentStepBetaSourceLevel : ProofLevel
preferredA1CurrentStepBetaSourceLevel =
  R473.literalRound473A1SourceInstantiationLevel

preferredA2HistoryShellSameObjectLevel : ProofLevel
preferredA2HistoryShellSameObjectLevel =
  R250.literalCMP116BetaMarkIsGeneratedHistoryShellLevel

preferredA2ShellToPartialSumCompilerLevel : ProofLevel
preferredA2ShellToPartialSumCompilerLevel =
  R250.a2ShellIdentityToPartialSumCompilerLevel

-- Historical stronger finite-RG/Hessian route retained for audit only.
u1CompactSimpleFiveBlockSourceMapFallbackLevel : ProofLevel
u1CompactSimpleFiveBlockSourceMapFallbackLevel =
  G2.physicalGroupParametricFiveBlockSourceMapLevel

u2LegacyOneLoopPackageFallbackLevel : ProofLevel
u2LegacyOneLoopPackageFallbackLevel =
  R73.literalWilsonFPHaarOneLoopRGCoefficientLevel

u3LegacyUnifiedOneStepYMEstimateFallbackLevel : ProofLevel
u3LegacyUnifiedOneStepYMEstimateFallbackLevel =
  R73.physicalUnifiedOneStepYMEstimateLevel

u3PublishedFlowEntryAfterSourceNativeEstimateCompilerLevel : ProofLevel
u3PublishedFlowEntryAfterSourceNativeEstimateCompilerLevel =
  R76.round76SourceEntryDependencyCompilerLevel

u4SameFamilyFiniteContinuumOSWeldLevel : ProofLevel
u4SameFamilyFiniteContinuumOSWeldLevel =
  R128.literalBalabanSameFamilyOSStressRecoveryLevel

u5QuantitativeMomentsToFiniteOS05Level : ProofLevel
u5QuantitativeMomentsToFiniteOS05Level =
  R464.literalRound464QuantitativeMomentToOS05Level

a1PublishedFiniteSymmetryApplicationLevel : ProofLevel
a1PublishedFiniteSymmetryApplicationLevel =
  R462.literalRound462PublishedFiniteOSApplicationLevel

a2PublishedWilsonRPApplicationLevel : ProofLevel
a2PublishedWilsonRPApplicationLevel =
  R461.literalRound461PublishedWilsonSameObjectApplicationLevel

explicitHaarChangeOfVariablesMandatory : Bool
explicitHaarChangeOfVariablesMandatory = false

explicitPeterWeylSquareReconstructionMandatory : Bool
explicitPeterWeylSquareReconstructionMandatory = false

projectiveProkhorovMandatory : Bool
projectiveProkhorovMandatory = false

standalonePublishedFlowEntryMandatory : Bool
standalonePublishedFlowEntryMandatory = false

legacyFiveBlockAndUnifiedHessianRouteMandatory : Bool
legacyFiveBlockAndUnifiedHessianRouteMandatory = false

round470UVContinuumMinCutCompilerLevel : ProofLevel
round470UVContinuumMinCutCompilerLevel = machineChecked

import DASHI.Physics.YangMills.BalabanLiteralFourReceiptBetaRound471Exact

import DASHI.Physics.YangMills.YangMillsClayGoal1PresentCutRound472Exact as R472

preferredFiniteRGPresentCutLevel : ProofLevel
preferredFiniteRGPresentCutLevel =
  R472.literalRound472PresentCutInstantiationLevel

historicalBC1BC2MandatoryForPreferredGoal1 : Bool
historicalBC1BC2MandatoryForPreferredGoal1 = false
