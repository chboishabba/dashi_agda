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
-- Constrained-propagator source:
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355
--
-- Current Row-A1 dependency history:
--
--   source transcription
--     -> direct p=0 beta projection / trace-log route
--     -> seagull-sign + one-step history refinement
--     -> one bubble-entry + summable-history refinement
--     -> explicit corner V_00 scalar + generic Cauchy/history reduced margin
--     -> CROSS-POLLINATION:
--          reuse five-channel quartic current-step remainder
--          + reuse localized irrelevant-memory shell tail.
--
-- This last step deletes the generic A,K,rho,D parameterization from the
-- shortest physical route.  Once the literal physical channel/localization
-- inputs are instantiated, the existing Agda compilers already give
--
--   betaInt >= - C_beta gamma^4
--   irrelevantMemory <= C_H gamma / 2.
--
-- The remaining primary Gaussian source task is exact: CMP109 (1.5) delegates
-- its background-dependent quadratic operators to Sect. D of reference [13],
-- which is the CMP99 background-propagator paper.  The literal first-variation
-- corner datum must therefore be obtained by differentiating that SAME CMP99
-- Delta(U), including the averaging/gauge-fixing constraint dependence entering
-- CMP109's constrained Gaussian, then Fourier-evaluating the result at the
-- project corner q=(0,1/2,0,0).
--
-- Parallel Lean RequestProject returns prove additional downstream
-- finite-dimensional algebra.  Those results guide this Agda graph but do NOT
-- become Agda machineChecked merely because Lean built them.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)
open import DASHI.Physics.YangMills.BalabanCMP109SourceTranscriptionExact
open import DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceCutsetExact
open import DASHI.Physics.YangMills.BalabanCMP109SeagullHistorySourceRefinementExact
open import DASHI.Physics.YangMills.BalabanCMP109UniformFloorSummableHistoryRefinementExact
open import DASHI.Physics.YangMills.BalabanCMP109ReducedMarginSourceCutsetExact
open import DASHI.Physics.YangMills.BalabanCMP109A1CrossPollinatedDebtProducersExact
open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound82FiveAnalyticLeafExact

------------------------------------------------------------------------
-- Regression-visible dependency levels
------------------------------------------------------------------------

sourceTranscriptionRegressionLevel : ProofLevel
sourceTranscriptionRegressionLevel = cmp109SourceTranscriptionLevel

directBetaDependencyCutsetRegressionLevel : ProofLevel
directBetaDependencyCutsetRegressionLevel = cmp109DirectBetaCutsetLevel

seagullHistoryDependencyRefinementRegressionLevel : ProofLevel
seagullHistoryDependencyRefinementRegressionLevel =
  cmp109SeagullHistoryDependencyRefinementLevel

uniformFloorSummableHistoryDependencyRegressionLevel : ProofLevel
uniformFloorSummableHistoryDependencyRegressionLevel =
  cmp109UniformFloorSummableHistoryDependencyLevel

reducedMarginDependencyRefinementRegressionLevel : ProofLevel
reducedMarginDependencyRefinementRegressionLevel =
  cmp109ReducedMarginDependencyRefinementLevel

------------------------------------------------------------------------
-- Current shortest Row-A1 source blockers
------------------------------------------------------------------------

-- Gaussian: literal CMP99/CMP109 first background variation at the explicit
-- project corner; no global Brillouin lower bound is required.
literalCornerFirstVariationScalarRegressionLevel : ProofLevel
literalCornerFirstVariationScalarRegressionLevel =
  cmp109LiteralCornerFirstVariationScalarLevel

-- Current-step nonlinear debt: instantiate the existing five physical channels
-- through cubic cancellation and fourth-order quotient majorants.
literalFiveChannelTaylorInstantiationRegressionLevel : ProofLevel
literalFiveChannelTaylorInstantiationRegressionLevel =
  cmp109LiteralFiveChannelTaylorInstantiationLevel

literalFiveChannelQuotientMajorantRegressionLevel : ProofLevel
literalFiveChannelQuotientMajorantRegressionLevel =
  cmp109LiteralFiveChannelQuotientMajorantLevel

-- Historical debt: instantiate the existing localized/irrelevant-memory shell
-- influence.  Do not assign exponential forgetting to the marginal coupling.
literalIrrelevantMemoryInfluenceRegressionLevel : ProofLevel
literalIrrelevantMemoryInfluenceRegressionLevel =
  cmp109LiteralIrrelevantMemoryInfluenceLevel

crossPollinatedA1DebtPackageRegressionLevel : ProofLevel
crossPollinatedA1DebtPackageRegressionLevel =
  cmp109CrossPollinatedA1DebtPackageLevel

------------------------------------------------------------------------
-- Machine-checked reused debt compilers
------------------------------------------------------------------------

fiveChannelQuarticDebtReuseRegressionLevel : ProofLevel
fiveChannelQuarticDebtReuseRegressionLevel =
  cmp109FiveChannelQuarticDebtReuseLevel

localizedIrrelevantMemoryDebtReuseRegressionLevel : ProofLevel
localizedIrrelevantMemoryDebtReuseRegressionLevel =
  cmp109LocalizedIrrelevantMemoryDebtReuseLevel

------------------------------------------------------------------------
-- Historical / ancestry-visible older blockers
------------------------------------------------------------------------

literalCauchyInteractionPairHistoricalLevel : ProofLevel
literalCauchyInteractionPairHistoricalLevel =
  cmp109LiteralCauchyInteractionPairLevel

literalUniformHistorySummabilityHistoricalLevel : ProofLevel
literalUniformHistorySummabilityHistoricalLevel =
  cmp109LiteralUniformHistorySummabilityLevel

literalParamagneticSeagullSignHistoricalLevel : ProofLevel
literalParamagneticSeagullSignHistoricalLevel =
  cmp109LiteralParamagneticSeagullSignLevel

literalUniformBubbleEntryHistoricalLevel : ProofLevel
literalUniformBubbleEntryHistoricalLevel =
  cmp109LiteralUniformBubbleEntryLevel

------------------------------------------------------------------------
-- Scoreboards
------------------------------------------------------------------------

-- Historical Round82 cutset retained for ancestry/audit only.
round82HistoricalLeafCountRegression : Nat
round82HistoricalLeafCountRegression = round82ActualNewAnalyticLeafCount

-- Current frozen research scoreboard from the A/B/C/D recut.
currentFrozenResearchCountRegression : Nat
currentFrozenResearchCountRegression = currentFrozenResearchCount
