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
--     -> explicit corner V_00 scalar + Cauchy interaction pair + D-summability
--        reduced-margin cutset.
--
-- Parallel Lean RequestProject returns prove the downstream finite-dimensional
-- algebra and quantitative implications.  Those results guide this Agda graph
-- but do NOT become Agda machineChecked merely because Lean built them.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)
open import DASHI.Physics.YangMills.BalabanCMP109SourceTranscriptionExact
open import DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceCutsetExact
open import DASHI.Physics.YangMills.BalabanCMP109SeagullHistorySourceRefinementExact
open import DASHI.Physics.YangMills.BalabanCMP109UniformFloorSummableHistoryRefinementExact
open import DASHI.Physics.YangMills.BalabanCMP109ReducedMarginSourceCutsetExact
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
-- Current Row-A1 source blockers
------------------------------------------------------------------------

literalCornerFirstVariationScalarRegressionLevel : ProofLevel
literalCornerFirstVariationScalarRegressionLevel =
  cmp109LiteralCornerFirstVariationScalarLevel

literalCauchyInteractionPairRegressionLevel : ProofLevel
literalCauchyInteractionPairRegressionLevel =
  cmp109LiteralCauchyInteractionPairLevel

literalUniformHistorySummabilityRegressionLevel : ProofLevel
literalUniformHistorySummabilityRegressionLevel =
  cmp109LiteralUniformHistorySummabilityLevel

currentA1ResidualObligationRegressionLevel : ProofLevel
currentA1ResidualObligationRegressionLevel =
  cmp109A1ResidualObligationLevel

------------------------------------------------------------------------
-- Historical / ancestry-visible older blockers
------------------------------------------------------------------------

literalParamagneticSeagullSignRegressionLevel : ProofLevel
literalParamagneticSeagullSignRegressionLevel =
  cmp109LiteralParamagneticSeagullSignLevel

literalUniformBubbleEntryRegressionLevel : ProofLevel
literalUniformBubbleEntryRegressionLevel =
  cmp109LiteralUniformBubbleEntryLevel

literalUniformGaussianFloorRegressionLevel : ProofLevel
literalUniformGaussianFloorRegressionLevel =
  cmp109LiteralUniformGaussianFloorLevel

literalSummableHistoryKernelRegressionLevel : ProofLevel
literalSummableHistoryKernelRegressionLevel =
  cmp109LiteralSummableHistoryKernelLevel

literalFiniteGInteractionDebtRegressionLevel : ProofLevel
literalFiniteGInteractionDebtRegressionLevel = cmp109LiteralFiniteGInteractionDebtLevel

------------------------------------------------------------------------
-- Scoreboards
------------------------------------------------------------------------

-- Historical Round82 cutset retained for ancestry/audit only.
round82HistoricalLeafCountRegression : Nat
round82HistoricalLeafCountRegression = round82ActualNewAnalyticLeafCount

-- Current frozen research scoreboard from the A/B/C/D recut.
currentFrozenResearchCountRegression : Nat
currentFrozenResearchCountRegression = currentFrozenResearchCount
