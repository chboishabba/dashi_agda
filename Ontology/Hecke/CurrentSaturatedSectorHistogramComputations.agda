module Ontology.Hecke.CurrentSaturatedSectorHistogramComputations where

open import Agda.Builtin.Equality using (_≡_; refl)

open import Ontology.Hecke.CurrentSaturatedForcedStableCollapse
  using
    ( CurrentSaturatedGenerator
    ; saturatedAnchoredTrajectory
    ; saturatedBalancedComposed
    ; saturatedBalancedCycle
    ; saturatedDenseComposed
    ; saturatedExplicitWidth2
    ; saturatedExplicitWidth3
    ; saturatedFullSupportCascade
    ; saturatedSupportCascade
    )
open import Ontology.Hecke.DefectOrbitSummaryRefinement
  using (DefectHistogram)
open import Ontology.Hecke.TriadIndexedDefectOrbitSummaryRefinement
  using
    ( TriadIndexedHistogram
    ; currentSaturatedTriadHistogramAt
    )

------------------------------------------------------------------------
-- Explicit packaged sector histograms on the current saturated scope.
--
-- This keeps the domain fixed to the already-classified saturated generator
-- taxonomy and exposes the three candidate sector histograms directly. The
-- next proof step can now work with named packaged computations rather than
-- only abstract existential separator surfaces.

record CurrentSaturatedSectorHistograms : Set where
  constructor currentSaturatedSectorHistograms
  field
    hist0 : DefectHistogram
    hist1 : DefectHistogram
    hist2 : DefectHistogram

open CurrentSaturatedSectorHistograms public

sectorHistogramsAt :
  CurrentSaturatedGenerator → CurrentSaturatedSectorHistograms
sectorHistogramsAt c = record
  { hist0 = TriadIndexedHistogram.histogram0
              (currentSaturatedTriadHistogramAt c)
  ; hist1 = TriadIndexedHistogram.histogram1
              (currentSaturatedTriadHistogramAt c)
  ; hist2 = TriadIndexedHistogram.histogram2
              (currentSaturatedTriadHistogramAt c)
  }

------------------------------------------------------------------------
-- Individual sector accessors

sector0HistAt : CurrentSaturatedGenerator → DefectHistogram
sector0HistAt c = hist0 (sectorHistogramsAt c)

sector1HistAt : CurrentSaturatedGenerator → DefectHistogram
sector1HistAt c = hist1 (sectorHistogramsAt c)

sector2HistAt : CurrentSaturatedGenerator → DefectHistogram
sector2HistAt c = hist2 (sectorHistogramsAt c)

------------------------------------------------------------------------
-- Canonical packaged computations for each current saturated class

explicitWidth3-sectorHistograms : CurrentSaturatedSectorHistograms
explicitWidth3-sectorHistograms =
  sectorHistogramsAt saturatedExplicitWidth3

denseComposed-sectorHistograms : CurrentSaturatedSectorHistograms
denseComposed-sectorHistograms =
  sectorHistogramsAt saturatedDenseComposed

balancedCycle-sectorHistograms : CurrentSaturatedSectorHistograms
balancedCycle-sectorHistograms =
  sectorHistogramsAt saturatedBalancedCycle

balancedComposed-sectorHistograms : CurrentSaturatedSectorHistograms
balancedComposed-sectorHistograms =
  sectorHistogramsAt saturatedBalancedComposed

explicitWidth2-sectorHistograms : CurrentSaturatedSectorHistograms
explicitWidth2-sectorHistograms =
  sectorHistogramsAt saturatedExplicitWidth2

anchoredTrajectory-sectorHistograms : CurrentSaturatedSectorHistograms
anchoredTrajectory-sectorHistograms =
  sectorHistogramsAt saturatedAnchoredTrajectory

supportCascade-sectorHistograms : CurrentSaturatedSectorHistograms
supportCascade-sectorHistograms =
  sectorHistogramsAt saturatedSupportCascade

fullSupportCascade-sectorHistograms : CurrentSaturatedSectorHistograms
fullSupportCascade-sectorHistograms =
  sectorHistogramsAt saturatedFullSupportCascade

------------------------------------------------------------------------
-- Equality/inequality utilities

postulate
  ⊥ : Set

  _≢_ : {A : Set} → A → A → Set

  _⊎_ : Set → Set → Set
  ∃₂ : {A B : Set} → (A → B → Set) → Set

------------------------------------------------------------------------
-- First concrete theorem targets on explicit packaged computations

postulate
  some-current-sector0-separates :
    ∃₂ λ c₁ c₂ →
      sector0HistAt c₁ ≢ sector0HistAt c₂

  some-current-sector1-separates :
    ∃₂ λ c₁ c₂ →
      sector1HistAt c₁ ≢ sector1HistAt c₂

  some-current-sector2-separates :
    ∃₂ λ c₁ c₂ →
      sector2HistAt c₁ ≢ sector2HistAt c₂

------------------------------------------------------------------------
-- Weaker disjunctive theorem target:
-- some sector separates some current saturated pair.

postulate
  some-current-sector-separates :
    ∃₂ λ c₁ c₂ →
      ( sector0HistAt c₁ ≢ sector0HistAt c₂
      ⊎ sector1HistAt c₁ ≢ sector1HistAt c₂
      ⊎ sector2HistAt c₁ ≢ sector2HistAt c₂
      )

------------------------------------------------------------------------
-- Stronger target:
-- the whole triad-indexed histogram package separates some current pair.

postulate
  some-current-triad-package-separates :
    ∃₂ λ c₁ c₂ →
      sectorHistogramsAt c₁ ≢ sectorHistogramsAt c₂

------------------------------------------------------------------------
-- Negative fallback:
-- even the explicit packaged sector histograms collapse on the current scope.

postulate
  all-current-sector-histograms-collapse :
    ∀ c₁ c₂ →
      sectorHistogramsAt c₁ ≡ sectorHistogramsAt c₂
