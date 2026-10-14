{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyTripartiteInformationAtlasAuthorityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- CROSS-PROVER AUTHORITY: SAME-GLOBAL-STATE TRIPARTITE INFORMATION ATLAS
--
-- Lean source owner:
--   RequestProject.QuantumMereologyTripartiteInformationAtlas
--
-- From one finite PSD trace-one state on (A x B) x C, the Lean owner defines
-- AB, AC and BC pair marginals by explicit partial traces, proves each is a
-- density matrix, proves overlapping A/B/C one-factor marginals agree, and
-- defines the three same-global-state mutual-information edge weights.
--
-- This is a three-factor theorem surface only.  It does not create a general
-- N-factor marginal recursion, a metric, MDS realization, curvature, spacetime,
-- or a physical TPS attachment.
------------------------------------------------------------------------

record TripartiteInformationAtlasStatus : Set where
  field
    SameGlobalStateThreePairMarginalsSourceWritten : Bool
    SameGlobalStateThreePairMarginalsSourceWrittenIsTrue :
      SameGlobalStateThreePairMarginalsSourceWritten ≡ true

    OverlappingOneFactorMarginalsAgreeSourceWritten : Bool
    OverlappingOneFactorMarginalsAgreeSourceWrittenIsTrue :
      OverlappingOneFactorMarginalsAgreeSourceWritten ≡ true

    ThreeSameObjectMutualInformationEdgesSourceWritten : Bool
    ThreeSameObjectMutualInformationEdgesSourceWrittenIsTrue :
      ThreeSameObjectMutualInformationEdgesSourceWritten ≡ true

    TripartiteAtlasCreatesGeneralNFactorAtlas : Bool
    TripartiteAtlasCreatesGeneralNFactorAtlasIsFalse :
      TripartiteAtlasCreatesGeneralNFactorAtlas ≡ false

    TripartiteAtlasCreatesMetric : Bool
    TripartiteAtlasCreatesMetricIsFalse :
      TripartiteAtlasCreatesMetric ≡ false

    TripartiteAtlasCreatesSpatialRealization : Bool
    TripartiteAtlasCreatesSpatialRealizationIsFalse :
      TripartiteAtlasCreatesSpatialRealization ≡ false

canonicalTripartiteInformationAtlasStatus : TripartiteInformationAtlasStatus
canonicalTripartiteInformationAtlasStatus = record
  { SameGlobalStateThreePairMarginalsSourceWritten = true
  ; SameGlobalStateThreePairMarginalsSourceWrittenIsTrue = refl
  ; OverlappingOneFactorMarginalsAgreeSourceWritten = true
  ; OverlappingOneFactorMarginalsAgreeSourceWrittenIsTrue = refl
  ; ThreeSameObjectMutualInformationEdgesSourceWritten = true
  ; ThreeSameObjectMutualInformationEdgesSourceWrittenIsTrue = refl
  ; TripartiteAtlasCreatesGeneralNFactorAtlas = false
  ; TripartiteAtlasCreatesGeneralNFactorAtlasIsFalse = refl
  ; TripartiteAtlasCreatesMetric = false
  ; TripartiteAtlasCreatesMetricIsFalse = refl
  ; TripartiteAtlasCreatesSpatialRealization = false
  ; TripartiteAtlasCreatesSpatialRealizationIsFalse = refl
  }

leanTripartiteInformationAtlasSourceReceipt : Sources.AttributionReceipt
leanTripartiteInformationAtlasSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyTripartiteInformationAtlas"
    "Source-written theorem surface constructing AB, AC and BC density-matrix marginals from one global (A x B) x C density matrix, proving overlap consistency of the A/B/C one-factor marginals, and defining all three same-global-state mutual-information edge weights. Source lineage only until exact-head Lean kernel evidence exists."

dashiTripartiteCrossProverReceipt : Sources.AttributionReceipt
dashiTripartiteCrossProverReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Records the Lean tripartite same-global-state marginal-consistency theorem without promoting it to a general N-factor atlas, metric, spatial realization, holographic dictionary or spacetime theorem."
