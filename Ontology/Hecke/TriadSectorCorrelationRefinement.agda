module Ontology.Hecke.TriadSectorCorrelationRefinement where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

open import Ontology.Hecke.CurrentSaturatedForcedStableCollapse
  using (CurrentSaturatedGenerator)
open import Ontology.Hecke.CurrentSaturatedSectorHistogramComputations
  using
    ( CurrentSaturatedSectorHistograms
    ; sectorHistogramsAt
    )
open import Ontology.Hecke.DefectOrbitSummaryRefinement
  using
    ( DefectHistogram
    ; illegalCount
    ; otherCount
    ; stableCount
    )

------------------------------------------------------------------------
-- Correlation refinement above the ordered triad histogram.
--
-- If the current triad-indexed histogram still collapses on the saturated
-- branch, the next smallest structured signal is not another total but the
-- relation between sector histograms themselves. This module packages that
-- fallback surface without claiming that it already separates the current
-- saturated classes.

dotHistogram : DefectHistogram → DefectHistogram → Nat
dotHistogram h₁ h₂ =
    stableCount h₁  * stableCount h₂
  + illegalCount h₁ * illegalCount h₂
  + otherCount h₁   * otherCount h₂

record SectorCorrelationSummary : Set where
  constructor sectorCorrelationSummary
  field
    corr01 : Nat
    corr12 : Nat
    corr20 : Nat

open SectorCorrelationSummary public

sectorCorrelationOf :
  CurrentSaturatedSectorHistograms → SectorCorrelationSummary
sectorCorrelationOf h = record
  { corr01 = dotHistogram
      (CurrentSaturatedSectorHistograms.hist0 h)
      (CurrentSaturatedSectorHistograms.hist1 h)
  ; corr12 = dotHistogram
      (CurrentSaturatedSectorHistograms.hist1 h)
      (CurrentSaturatedSectorHistograms.hist2 h)
  ; corr20 = dotHistogram
      (CurrentSaturatedSectorHistograms.hist2 h)
      (CurrentSaturatedSectorHistograms.hist0 h)
  }

currentSaturatedSectorCorrelationAt :
  CurrentSaturatedGenerator → SectorCorrelationSummary
currentSaturatedSectorCorrelationAt c =
  sectorCorrelationOf (sectorHistogramsAt c)

postulate
  ⊥ : Set

  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

  ∃₂ : {A B : Set} → (A → B → Set) → Set

------------------------------------------------------------------------
-- Fixed-domain theorem surfaces.

postulate
  currentSaturated-sectorCorrelation-separates :
    ∃₂ λ c₁ c₂ →
      currentSaturatedSectorCorrelationAt c₁
        ≢
      currentSaturatedSectorCorrelationAt c₂

  currentSaturated-sectorCorrelation-exhausted :
    ∀ c₁ c₂ →
      currentSaturatedSectorCorrelationAt c₁
        ≡
      currentSaturatedSectorCorrelationAt c₂
