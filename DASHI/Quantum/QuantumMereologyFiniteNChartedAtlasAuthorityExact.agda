{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyFiniteNChartedAtlasAuthorityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- CROSS-PROVER AUTHORITY: CHARTED FINITE-N SAME-GLOBAL-STATE ATLAS
--
-- Lean source owner:
--   RequestProject.QuantumMereologyFiniteNChartedAtlas
--
-- The Lean owner generalizes the finite information lane to a homogeneous
-- finite global basis Fin n -> Fin d, conditional on explicit coordinate-
-- faithful pair/environment charts for every distinct ordered factor pair.
-- It reindexes ONE global density matrix through each exact chart and applies
-- the already-written finite partial trace, so every pair marginal is again a
-- PSD trace-one density matrix and every pair mutual-information weight comes
-- from the same declared global state.
--
-- This does NOT pay:
-- * automatic construction of pair charts for a heterogeneous physical TPS;
-- * chart-independence / overlap coherence for unrelated supplied charts;
-- * selected-TPS attachment;
-- * metric, MDS, curvature, holography or spacetime.
------------------------------------------------------------------------

record FiniteNChartedAtlasStatus : Set where
  field
    ChartedFiniteNPairExtractionSourceWritten : Bool
    ChartedFiniteNPairExtractionSourceWrittenIsTrue :
      ChartedFiniteNPairExtractionSourceWritten ≡ true

    ChartedPairMarginalDensitySourceWritten : Bool
    ChartedPairMarginalDensitySourceWrittenIsTrue :
      ChartedPairMarginalDensitySourceWritten ≡ true

    EveryPairWeightSameDeclaredGlobalStateSourceWritten : Bool
    EveryPairWeightSameDeclaredGlobalStateSourceWrittenIsTrue :
      EveryPairWeightSameDeclaredGlobalStateSourceWritten ≡ true

    PairChartFamilyAutomaticallyExistsForPhysicalSelectedTPS : Bool
    PairChartFamilyAutomaticallyExistsForPhysicalSelectedTPSIsFalse :
      PairChartFamilyAutomaticallyExistsForPhysicalSelectedTPS ≡ false

    ChartIndependenceOverlapCoherencePaid : Bool
    ChartIndependenceOverlapCoherencePaidIsFalse :
      ChartIndependenceOverlapCoherencePaid ≡ false

    ChartedAtlasCreatesHeterogeneousSelectedTPSAtlas : Bool
    ChartedAtlasCreatesHeterogeneousSelectedTPSAtlasIsFalse :
      ChartedAtlasCreatesHeterogeneousSelectedTPSAtlas ≡ false

    ChartedAtlasCreatesMetric : Bool
    ChartedAtlasCreatesMetricIsFalse :
      ChartedAtlasCreatesMetric ≡ false

canonicalFiniteNChartedAtlasStatus : FiniteNChartedAtlasStatus
canonicalFiniteNChartedAtlasStatus = record
  { ChartedFiniteNPairExtractionSourceWritten = true
  ; ChartedFiniteNPairExtractionSourceWrittenIsTrue = refl
  ; ChartedPairMarginalDensitySourceWritten = true
  ; ChartedPairMarginalDensitySourceWrittenIsTrue = refl
  ; EveryPairWeightSameDeclaredGlobalStateSourceWritten = true
  ; EveryPairWeightSameDeclaredGlobalStateSourceWrittenIsTrue = refl
  ; PairChartFamilyAutomaticallyExistsForPhysicalSelectedTPS = false
  ; PairChartFamilyAutomaticallyExistsForPhysicalSelectedTPSIsFalse = refl
  ; ChartIndependenceOverlapCoherencePaid = false
  ; ChartIndependenceOverlapCoherencePaidIsFalse = refl
  ; ChartedAtlasCreatesHeterogeneousSelectedTPSAtlas = false
  ; ChartedAtlasCreatesHeterogeneousSelectedTPSAtlasIsFalse = refl
  ; ChartedAtlasCreatesMetric = false
  ; ChartedAtlasCreatesMetricIsFalse = refl
  }

leanFiniteNChartedAtlasSourceReceipt : Sources.AttributionReceipt
leanFiniteNChartedAtlasSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyFiniteNChartedAtlas"
    "Source-written charted finite-N compiler over a homogeneous global basis: exact pair/environment basis equivalences reindex the SAME global density matrix, and the existing finite partial-trace theorem returns a genuine density matrix and mutual-information weight for every charted pair. Cross-prover source lineage only; no exact-head Lean kernel receipt is imported here."

dashiFiniteNChartedAtlasCrossProverReceipt : Sources.AttributionReceipt
dashiFiniteNChartedAtlasCrossProverReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Records the Lean charted finite-N same-global-state theorem surface while keeping physical selected-TPS chart construction, chart-independence/overlap coherence, metricity and spatial realization explicit and unpaid."
