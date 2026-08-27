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
--   literal constrained-operator evaluation / positive beta proof.
--
-- The parallel Lean RequestProject return proved generic finite-dimensional
-- trace-log Hessian algebra, constrained-propagator annihilation/Ward
-- cancellation, third-order beta-projection annihilation, Fourier trace
-- reduction, and geometric history-response summability.  Those results guide
-- this Agda dependency graph, but are NOT labelled Agda machineChecked here:
-- cross-prover success is not an Agda kernel receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)
open import DASHI.Physics.YangMills.BalabanCMP109SourceTranscriptionExact
open import DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceCutsetExact
open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound82FiveAnalyticLeafExact

------------------------------------------------------------------------
-- Regression-visible status aliases
------------------------------------------------------------------------

sourceTranscriptionRegressionLevel : ProofLevel
sourceTranscriptionRegressionLevel = cmp109SourceTranscriptionLevel

directBetaDependencyCutsetRegressionLevel : ProofLevel
directBetaDependencyCutsetRegressionLevel = cmp109DirectBetaCutsetLevel

literalGaussianBetaZRegressionLevel : ProofLevel
literalGaussianBetaZRegressionLevel = cmp109LiteralGaussianBetaZLevel

literalFiniteGInteractionDebtRegressionLevel : ProofLevel
literalFiniteGInteractionDebtRegressionLevel = cmp109LiteralFiniteGInteractionDebtLevel

literalHistoryResponseDecayRegressionLevel : ProofLevel
literalHistoryResponseDecayRegressionLevel = cmp109LiteralHistoryResponseDecayLevel

round82LeafCountRegression : Nat
round82LeafCountRegression = round82ActualNewAnalyticLeafCount
