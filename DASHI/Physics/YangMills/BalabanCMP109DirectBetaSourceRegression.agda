module DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceRegression where

------------------------------------------------------------------------
-- Focused elaboration root for the current Row-A1 source-facing route.
--
-- Primary source:
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
--
-- Background/averaging sources:
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", CMP 99 (1985), 389--434. DOI: 10.1007/BF01240355.
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- CMP 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- Current Row-A1 dependency history:
--
--   source transcription
--     -> direct p=0 beta projection / trace-log route
--     -> seagull-sign + history refinement
--     -> positive-measure patch correction
--     -> W/Q/R constrained first-variation decomposition
--     -> five-channel quartic current-step remainder
--     -> HISTORY ANTI-DOUBLE-COUNTING:
--          beta_j is projected from current E^(j+1), which already depends on
--          preceding couplings; if the five-channel remainder bound is uniform
--          over the admissible history, history is an argument of betaInt, not a
--          second additive final debt.
--
-- Hence the highest-alpha final A1 margin can collapse to
--
--   b_patch - C_beta gamma^4 > 0
--
-- PROVIDED the physical five-channel instantiation is uniform over the full
-- admissible preceding-coupling history.  Localization/history estimates may be
-- used internally to prove that uniformity, but must not then be subtracted a
-- second time.
--
-- The Gaussian W channel is D_background of the Wilson HESSIAN, hence a mixed
-- third Wilson variation.  The existing literal first-variation plaquette owner
-- is useful coordinate/support infrastructure but is not itself W.  A literal
-- third-variation/right-exponential source weld remains open.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel; conditional)
open import DASHI.Physics.YangMills.BalabanCMP109SourceTranscriptionExact
open import DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceCutsetExact
open import DASHI.Physics.YangMills.BalabanCMP109SeagullHistorySourceRefinementExact
open import DASHI.Physics.YangMills.BalabanCMP109UniformFloorSummableHistoryRefinementExact
open import DASHI.Physics.YangMills.BalabanCMP109ReducedMarginSourceCutsetExact
open import DASHI.Physics.YangMills.BalabanCMP109A1CrossPollinatedDebtProducersExact
open import DASHI.Physics.YangMills.BalabanCMP109GaussianPositivePatchCorrectionExact
open import DASHI.Physics.YangMills.BalabanCMP109GaussianFirstVariationSourceDecompositionExact
open import DASHI.Physics.YangMills.BalabanCMP109CorrectedPatchMarginCrossProverExact
open import DASHI.Physics.YangMills.BalabanA1HistoryUniformRemainderAntiDoubleCountExact
open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound82FiveAnalyticLeafExact

------------------------------------------------------------------------
-- Current shortest Row-A1 Gaussian source blockers
------------------------------------------------------------------------

literalWilsonHessianVariationRegressionLevel : ProofLevel
literalWilsonHessianVariationRegressionLevel =
  cmp109LiteralWilsonHessianVariationCurrentLevel

-- Sharper description of the same W seam: D_background Delta is a mixed third
-- Wilson variation, not the already-existing first action variation.
literalWilsonMixedThirdVariationRegressionLevel : ProofLevel
literalWilsonMixedThirdVariationRegressionLevel = conditional

literalAveragingConstraintVariationRegressionLevel : ProofLevel
literalAveragingConstraintVariationRegressionLevel =
  cmp109LiteralAveragingConstraintVariationCurrentLevel

literalGaugeProjectionVariationRegressionLevel : ProofLevel
literalGaugeProjectionVariationRegressionLevel =
  cmp109LiteralGaugeProjectionVariationCurrentLevel

literalWQRAssemblyRegressionLevel : ProofLevel
literalWQRAssemblyRegressionLevel = cmp109LiteralWQRAssemblyCurrentLevel

literalMixedVertexPositivePatchRegressionLevel : ProofLevel
literalMixedVertexPositivePatchRegressionLevel =
  cmp109LiteralPositivePatchCurrentLevel

------------------------------------------------------------------------
-- Current shortest Row-A1 remainder/history blocker
------------------------------------------------------------------------

literalFiveChannelTaylorInstantiationRegressionLevel : ProofLevel
literalFiveChannelTaylorInstantiationRegressionLevel =
  cmp109LiteralFiveChannelTaylorInstantiationLevel

literalFiveChannelQuotientMajorantRegressionLevel : ProofLevel
literalFiveChannelQuotientMajorantRegressionLevel =
  cmp109LiteralFiveChannelCurrentLevel

-- Highest-alpha source weld: the current five-channel betaInt must be bounded
-- uniformly over the complete admissible preceding-coupling history.
literalFiveChannelUniformOverHistoryRegressionLevel : ProofLevel
literalFiveChannelUniformOverHistoryRegressionLevel =
  cmp109LiteralFiveChannelUniformOverHistoryLevel

------------------------------------------------------------------------
-- Machine-checked reused Agda compilers
------------------------------------------------------------------------

historyUniformAntiDoubleCountRegressionLevel : ProofLevel
historyUniformAntiDoubleCountRegressionLevel =
  historyUniformCurrentRemainderAntiDoubleCountLevel

positivePatchArithmeticRegressionLevel : ProofLevel
positivePatchArithmeticRegressionLevel = positivePatchArithmeticLevel

fiveChannelQuarticDebtReuseRegressionLevel : ProofLevel
fiveChannelQuarticDebtReuseRegressionLevel =
  cmp109FiveChannelQuarticDebtReuseLevel

------------------------------------------------------------------------
-- Conditional fallback if history-uniform five-channel control fails
------------------------------------------------------------------------

-- These remain available as a failure-closed fallback, but are no longer the
-- preferred final margin when the current betaInt is already history-uniform.
literalIrrelevantMemoryInfluenceFallbackLevel : ProofLevel
literalIrrelevantMemoryInfluenceFallbackLevel =
  cmp109LiteralLocalizedMemoryCurrentLevel

literalMarginalMemoryBoundFallbackLevel : ProofLevel
literalMarginalMemoryBoundFallbackLevel =
  cmp109LiteralMarginalMemoryBoundCurrentLevel

------------------------------------------------------------------------
-- Cross-prover-only theorem surfaces from the parallel Lean lane
------------------------------------------------------------------------

wilsonCubicCornerDisqualificationCrossProverRegressionLevel : ProofLevel
wilsonCubicCornerDisqualificationCrossProverRegressionLevel =
  cmp109WilsonCubicCornerDisqualificationCrossProverLevel

singleModeUniformFloorNoGoCrossProverRegressionLevel : ProofLevel
singleModeUniformFloorNoGoCrossProverRegressionLevel =
  cmp109SingleModeUniformFloorNoGoCrossProverLevel

quarterPatchLowerBoundCrossProverRegressionLevel : ProofLevel
quarterPatchLowerBoundCrossProverRegressionLevel =
  cmp109QuarterPatchLowerBoundCrossProverLevel

wqrInterferenceCrossProverRegressionLevel : ProofLevel
wqrInterferenceCrossProverRegressionLevel =
  cmp109WQRInterferenceCrossProverLevel

universalCoefficientCircularityCrossProverRegressionLevel : ProofLevel
universalCoefficientCircularityCrossProverRegressionLevel =
  cmp109UniversalCoefficientCircularityAuditCrossProverLevel

------------------------------------------------------------------------
-- Scoreboards
------------------------------------------------------------------------

round82HistoricalLeafCountRegression : Nat
round82HistoricalLeafCountRegression = round82ActualNewAnalyticLeafCount

-- Current frozen research scoreboard remains A/B/C/D = 4.
currentFrozenResearchCountRegression : Nat
currentFrozenResearchCountRegression = currentFrozenResearchCount
