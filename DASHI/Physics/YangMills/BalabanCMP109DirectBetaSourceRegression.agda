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
--          + certify one mixed Lorentz/color positive-MEASURE momentum patch.
--
-- The corner q=(0,1/2,0,0) single-mode witness is no longer authoritative:
-- Wilson cubic-vertex sine factors can vanish at Brillouin-boundary momenta, and
-- one discrete mode cannot by itself provide a normalized volume-uniform floor.
-- The correct highest-alpha Gaussian target is ONE positive-volume box plus
-- complement nonnegativity, reusing the configured box infrastructure.
--
-- Existing Agda debt compilers already give, once literally instantiated,
--
--   betaInt >= - C_beta gamma^4
--   irrelevantMemory <= C_H gamma / 2.
--
-- Hence the shortest current physical margin is
--
--   b_patch - C_beta gamma^4 - C_H gamma/2 > 0,
--
-- where b_patch is the lower contribution of one source-coherent normalized
-- Gaussian momentum box.  No global near/far estimate is required.
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
open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound82FiveAnalyticLeafExact

------------------------------------------------------------------------
-- Current shortest Row-A1 Gaussian source blockers
------------------------------------------------------------------------

literalWilsonHessianVariationRegressionLevel : ProofLevel
literalWilsonHessianVariationRegressionLevel =
  cmp109LiteralWilsonHessianVariationLevel

literalAveragingConstraintVariationRegressionLevel : ProofLevel
literalAveragingConstraintVariationRegressionLevel =
  cmp109LiteralAveragingConstraintVariationLevel

literalGaugeProjectionVariationRegressionLevel : ProofLevel
literalGaugeProjectionVariationRegressionLevel =
  cmp109LiteralGaugeProjectionVariationLevel

literalWQRAssemblyRegressionLevel : ProofLevel
literalWQRAssemblyRegressionLevel = cmp109LiteralWQRAssemblyLevel

literalMixedVertexPositivePatchRegressionLevel : ProofLevel
literalMixedVertexPositivePatchRegressionLevel =
  cmp109LiteralMixedVertexPositivePatchLevel

------------------------------------------------------------------------
-- Current shortest Row-A1 debt source blockers
------------------------------------------------------------------------

literalFiveChannelTaylorInstantiationRegressionLevel : ProofLevel
literalFiveChannelTaylorInstantiationRegressionLevel =
  cmp109LiteralFiveChannelTaylorInstantiationLevel

literalFiveChannelQuotientMajorantRegressionLevel : ProofLevel
literalFiveChannelQuotientMajorantRegressionLevel =
  cmp109LiteralFiveChannelQuotientMajorantLevel

literalIrrelevantMemoryInfluenceRegressionLevel : ProofLevel
literalIrrelevantMemoryInfluenceRegressionLevel =
  cmp109LiteralIrrelevantMemoryInfluenceLevel

crossPollinatedA1DebtPackageRegressionLevel : ProofLevel
crossPollinatedA1DebtPackageRegressionLevel =
  cmp109CrossPollinatedA1DebtPackageLevel

------------------------------------------------------------------------
-- Machine-checked reused compilers
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
