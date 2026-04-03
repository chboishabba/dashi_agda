module Ontology.Hecke.TriadIndexedDefectOrbitSummaryRefinement where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import Ontology.Hecke.CurrentSaturatedForcedStableCollapse
  using
    ( CurrentSaturatedGenerator
    ; saturatedForcedStableCountAt
    ; saturatedForcedStableCount≡15
    ; saturatedSummaryFieldAt
    ; saturatedSummaryField≡15
    )
open import Ontology.Hecke.DefectOrbitSummaryRefinement
  using
    ( DefectHistogram
    ; defectHistogram
    ; stableCount
    )

------------------------------------------------------------------------
-- Candidate triad-indexed refinement above the collapsed current orbit summary.
--
-- The current `DefectOrbitSummary` is already exhausted on the saturated
-- branch, so this module does not claim a discovered sector split.  It
-- packages the next structural hypothesis in the smallest reusable form:
--
--   15 = 3 × 5
--
-- read as three triadic sectors carrying the same five-count local summary.
-- This is a candidate factorization surface, not a proved separator.

data TriadSector : Set where
  sector0 : TriadSector
  sector1 : TriadSector
  sector2 : TriadSector

record TriadIndexedHistogram : Set where
  constructor triadIndexedHistogram
  field
    histogram0 : DefectHistogram
    histogram1 : DefectHistogram
    histogram2 : DefectHistogram

  totalStableCount : Nat
  totalStableCount =
      stableCount histogram0
    + stableCount histogram1
    + stableCount histogram2

open TriadIndexedHistogram public

candidateSectorHistogram : DefectHistogram
candidateSectorHistogram = defectHistogram 5 zero zero

candidateSectorStableCount≡5 :
  stableCount candidateSectorHistogram ≡ 5
candidateSectorStableCount≡5 = refl

candidateSaturatedTriadHistogram : TriadIndexedHistogram
candidateSaturatedTriadHistogram =
  triadIndexedHistogram
    candidateSectorHistogram
    candidateSectorHistogram
    candidateSectorHistogram

candidateSaturatedTriadTotal≡15 :
  totalStableCount candidateSaturatedTriadHistogram ≡ 15
candidateSaturatedTriadTotal≡15 = refl

currentSaturatedTriadHistogramAt :
  CurrentSaturatedGenerator → TriadIndexedHistogram
currentSaturatedTriadHistogramAt _ = candidateSaturatedTriadHistogram

currentSaturatedTriadTotalAt :
  CurrentSaturatedGenerator → Nat
currentSaturatedTriadTotalAt c =
  totalStableCount (currentSaturatedTriadHistogramAt c)

currentSaturatedTriadTotal≡15 :
  ∀ c →
  currentSaturatedTriadTotalAt c ≡ 15
currentSaturatedTriadTotal≡15 _ = candidateSaturatedTriadTotal≡15

currentSaturatedForcedStableCount-factors-through-triad :
  ∀ c →
  saturatedForcedStableCountAt c ≡ currentSaturatedTriadTotalAt c
currentSaturatedForcedStableCount-factors-through-triad c
  rewrite candidateSaturatedTriadTotal≡15 =
    saturatedForcedStableCount≡15 c

currentSaturatedSummaryField-factors-through-triad :
  ∀ c →
  saturatedSummaryFieldAt c ≡ currentSaturatedTriadTotalAt c
currentSaturatedSummaryField-factors-through-triad c
  rewrite candidateSaturatedTriadTotal≡15 =
    saturatedSummaryField≡15 c

record CurrentSaturatedTriadIndexedFactorization : Set₁ where
  field
    triadHistogram : CurrentSaturatedGenerator → TriadIndexedHistogram
    count-factor :
      ∀ c →
      saturatedForcedStableCountAt c ≡ totalStableCount (triadHistogram c)
    summary-factor :
      ∀ c →
      saturatedSummaryFieldAt c ≡ totalStableCount (triadHistogram c)

canonicalCurrentSaturatedTriadIndexedFactorization :
  CurrentSaturatedTriadIndexedFactorization
canonicalCurrentSaturatedTriadIndexedFactorization =
  record
    { triadHistogram = currentSaturatedTriadHistogramAt
    ; count-factor = currentSaturatedForcedStableCount-factors-through-triad
    ; summary-factor = currentSaturatedSummaryField-factors-through-triad
    }
