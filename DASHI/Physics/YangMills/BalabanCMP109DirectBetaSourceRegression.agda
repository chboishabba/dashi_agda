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
--     -> one-entry/summability reduction
--     -> generic corner/Cauchy/history reduced margin
--     -> debt CROSS-POLLINATION:
--          five-channel quartic current-step remainder
--          + localized irrelevant-memory shell tail
--     -> Gaussian SOURCE CORRECTION:
--          differentiate the same CMP99/CMP98 constrained carrier as W/Q/R
--          + certify one mixed Lorentz/color positive-MEASURE momentum patch
--     -> corrected Lean cross-prover margin:
--          W patch lower bound must pay |Q|+|R|
--          + marginal memory is separately budgeted unless source-removed.
--
-- The corner q=(0,1/2,0,0) single-mode witness is no longer authoritative.
-- The parallel Lean lane now proves both obstructions: the relevant Wilson cubic
-- diagonal component vanishes at the Brillouin boundary, and a fixed-cardinality
-- Fourier set cannot provide a normalized volume-uniform floor.
--
-- Existing Agda debt compilers already give, once literally instantiated,
--
--   betaInt >= - C_beta gamma^4
--   irrelevantMemory <= C_H gamma / 2.
--
-- The current full physical margin is therefore
--
--   b_patch
--   - C_beta gamma^4
--   - (C_H gamma / 2 + H_marg) B > 0.
--
-- The zero-marginal, unit-budget expression
--
--   b_patch - C_beta gamma^4 - C_H gamma/2
--
-- is only a specialization.  H_marg may be deleted only by a source theorem
-- proving that the marginal contribution vanishes or is already included in the
-- current local remainder.  No global near/far estimate is required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)
open import DASHI.Physics.YangMills.BalabanCMP109SourceTranscriptionExact
open import DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceCutsetExact
open import DASHI.Physics.YangMills.BalabanCMP109SeagullHistorySourceRefinementExact
open import DASHI.Physics.YangMills.BalabanCMP109UniformFloorSummableHistoryRefinementExact
open import DASHI.Physics.YangMills.BalabanCMP109ReducedMarginSourceCutsetExact
open import DASHI.Physics.YangMills.BalabanCMP109A1CrossPollinatedDebtProducersExact
open import DASHI.Physics.YangMills.BalabanCMP109GaussianPositivePatchCorrectionExact
open import DASHI.Physics.YangMills.BalabanCMP109GaussianFirstVariationSourceDecompositionExact
open import DASHI.Physics.YangMills.BalabanCMP109CorrectedPatchMarginCrossProverExact
open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound82FiveAnalyticLeafExact

------------------------------------------------------------------------
-- Current shortest Row-A1 Gaussian source blockers
------------------------------------------------------------------------

literalWilsonHessianVariationRegressionLevel : ProofLevel
literalWilsonHessianVariationRegressionLevel =
  cmp109LiteralWilsonHessianVariationCurrentLevel

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
-- Current shortest Row-A1 debt / history source blockers
------------------------------------------------------------------------

literalFiveChannelTaylorInstantiationRegressionLevel : ProofLevel
literalFiveChannelTaylorInstantiationRegressionLevel =
  cmp109LiteralFiveChannelTaylorInstantiationLevel

literalFiveChannelQuotientMajorantRegressionLevel : ProofLevel
literalFiveChannelQuotientMajorantRegressionLevel =
  cmp109LiteralFiveChannelCurrentLevel

literalIrrelevantMemoryInfluenceRegressionLevel : ProofLevel
literalIrrelevantMemoryInfluenceRegressionLevel =
  cmp109LiteralLocalizedMemoryCurrentLevel

literalMarginalMemoryBoundRegressionLevel : ProofLevel
literalMarginalMemoryBoundRegressionLevel =
  cmp109LiteralMarginalMemoryBoundCurrentLevel

correctedPatchMarginSourcePackageRegressionLevel : ProofLevel
correctedPatchMarginSourcePackageRegressionLevel =
  cmp109CorrectedPatchMarginSourcePackageLevel

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

correctedMarginCompilerCrossProverRegressionLevel : ProofLevel
correctedMarginCompilerCrossProverRegressionLevel =
  cmp109CorrectedMarginCompilerCrossProverLevel

universalCoefficientCircularityCrossProverRegressionLevel : ProofLevel
universalCoefficientCircularityCrossProverRegressionLevel =
  cmp109UniversalCoefficientCircularityAuditCrossProverLevel

------------------------------------------------------------------------
-- Machine-checked reused Agda compilers
------------------------------------------------------------------------

positivePatchArithmeticRegressionLevel : ProofLevel
positivePatchArithmeticRegressionLevel = positivePatchArithmeticLevel

fiveChannelQuarticDebtReuseRegressionLevel : ProofLevel
fiveChannelQuarticDebtReuseRegressionLevel =
  cmp109FiveChannelQuarticDebtReuseLevel

localizedIrrelevantMemoryDebtReuseRegressionLevel : ProofLevel
localizedIrrelevantMemoryDebtReuseRegressionLevel =
  cmp109LocalizedIrrelevantMemoryDebtReuseLevel

------------------------------------------------------------------------
-- Historical / ancestry-visible older blockers
------------------------------------------------------------------------

-- The single-corner scalar remains a useful finite-data regression only.
literalCornerFirstVariationScalarHistoricalLevel : ProofLevel
literalCornerFirstVariationScalarHistoricalLevel =
  cmp109LiteralCornerFirstVariationScalarLevel

literalCauchyInteractionPairHistoricalLevel : ProofLevel
literalCauchyInteractionPairHistoricalLevel =
  cmp109LiteralCauchyInteractionPairLevel

literalUniformHistorySummabilityHistoricalLevel : ProofLevel
literalUniformHistorySummabilityHistoricalLevel =
  cmp109LiteralUniformHistorySummabilityLevel

literalParamagneticSeagullSignHistoricalLevel : ProofLevel
literalParamagneticSeagullSignHistoricalLevel =
  cmp109LiteralParamagneticSeagullSignLevel

------------------------------------------------------------------------
-- Scoreboards
------------------------------------------------------------------------

round82HistoricalLeafCountRegression : Nat
round82HistoricalLeafCountRegression = round82ActualNewAnalyticLeafCount

-- Current frozen research scoreboard remains A/B/C/D = 4.
currentFrozenResearchCountRegression : Nat
currentFrozenResearchCountRegression = currentFrozenResearchCount
