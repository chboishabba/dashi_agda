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
-- This root deliberately keeps the current mathematical distinction visible:
--
--   source transcription / dependency recut
--       !=
--   literal source sign / source response data
--       !=
--   quantitative uniform Row-A1 closure.
--
-- Parallel Lean RequestProject returns have proved generic finite-dimensional
-- trace-log Hessian algebra, constrained-propagator annihilation/Ward
-- cancellation, third-order beta-projection annihilation, Fourier trace
-- reduction, paramagnetic-seagull positivity criteria, the obstruction for a
-- purely diamagnetic affine-Gram second variation, chain-rule generation of
-- geometric history-response decay, the separation of pointwise positivity
-- from a uniform Gaussian floor, a one-entry sufficient Gaussian-floor bound,
-- and the weaker criterion that uniform summability of the literal history
-- kernel is enough for the final debt.  Those results guide this Agda dependency
-- graph, but are NOT labelled Agda machineChecked here: cross-prover success is
-- not an Agda kernel receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)
open import DASHI.Physics.YangMills.BalabanCMP109SourceTranscriptionExact
open import DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceCutsetExact
open import DASHI.Physics.YangMills.BalabanCMP109SeagullHistorySourceRefinementExact
open import DASHI.Physics.YangMills.BalabanCMP109UniformFloorSummableHistoryRefinementExact
open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound82FiveAnalyticLeafExact

------------------------------------------------------------------------
-- Regression-visible status aliases
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

currentLiteralA1PackageRegressionLevel : ProofLevel
currentLiteralA1PackageRegressionLevel = cmp109CurrentLiteralA1SourcePackageLevel

------------------------------------------------------------------------
-- Scoreboards
------------------------------------------------------------------------

-- Historical Round82 cutset retained for ancestry/audit only.
round82HistoricalLeafCountRegression : Nat
round82HistoricalLeafCountRegression = round82ActualNewAnalyticLeafCount

-- Current frozen research scoreboard from the source-facing A/B/C/D recut.
currentFrozenResearchCountRegression : Nat
currentFrozenResearchCountRegression = frozenResearchCount
