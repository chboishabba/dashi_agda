module Ontology.Hecke.CurrentSaturatedTriadHistogramSeparation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

open import Ontology.Hecke.CurrentSaturatedForcedStableCollapse
  using
    ( CurrentSaturatedGenerator
    ; saturatedForcedStableCountAt
    ; saturatedForcedStableCount≡15
    )
open import Ontology.Hecke.TriadIndexedDefectOrbitSummaryRefinement
  using
    ( TriadIndexedHistogram
    ; TriadSector
    ; currentSaturatedTriadHistogramAt
    ; currentSaturatedTriadTotalAt
    ; currentSaturatedTriadTotal≡15
    ; sector0
    ; sector1
    ; sector2
    )

------------------------------------------------------------------------
-- Current saturated-scope specialization of the triad-indexed refinement.
--
-- The current question is fixed-domain:
-- does the already-classified saturated generator taxonomy split under the
-- next candidate triad-indexed histogram, or does that refinement collapse
-- too?

triadHistAt : CurrentSaturatedGenerator → TriadIndexedHistogram
triadHistAt = currentSaturatedTriadHistogramAt

triadStableTotalAt : CurrentSaturatedGenerator → Nat
triadStableTotalAt = currentSaturatedTriadTotalAt

triadStableTotal≡15 :
  ∀ c →
  triadStableTotalAt c ≡ 15
triadStableTotal≡15 = currentSaturatedTriadTotal≡15

currentSaturatedForcedStableCount-factors-through-triadHistogram :
  ∀ c →
  saturatedForcedStableCountAt c ≡ triadStableTotalAt c
currentSaturatedForcedStableCount-factors-through-triadHistogram c
  rewrite triadStableTotal≡15 c = saturatedForcedStableCount≡15 c

------------------------------------------------------------------------
-- Fixed-domain theorem surfaces.
--
-- These remain explicit targets only. The current triad-indexed module
-- packages the next structural hypothesis, but does not yet claim a
-- discovered separator on the saturated branch.

postulate
  ⊥ : Set

  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

  _⊎_ : Set → Set → Set
  ∃₂ : {A B : Set} → (A → B → Set) → Set

currentSaturated-triadHistogram-separates : Set
currentSaturated-triadHistogram-separates =
  ∃₂ λ c₁ c₂ →
    triadHistAt c₁ ≢ triadHistAt c₂

postulate
  sectorHistogramAt :
    CurrentSaturatedGenerator → TriadSector → Set

  currentSaturated-sector-separates :
    ∃₂ λ c₁ c₂ →
      ( sectorHistogramAt c₁ sector0 ≢ sectorHistogramAt c₂ sector0
      ⊎ sectorHistogramAt c₁ sector1 ≢ sectorHistogramAt c₂ sector1
      ⊎ sectorHistogramAt c₁ sector2 ≢ sectorHistogramAt c₂ sector2
      )

  currentSaturated-triadHistogram-exhausted :
    ∀ c₁ c₂ →
    triadHistAt c₁ ≡ triadHistAt c₂

------------------------------------------------------------------------
-- Current-scope structural hypothesis surface.
--
-- If the fixed-domain triad histogram does split, the next question is
-- whether the saturated `15` should be read as `3 × 5`.

postulate
  localCompositionClassCount :
    CurrentSaturatedGenerator → TriadSector → Nat

  fiveClassesPerSector-current :
    ∀ c k →
    localCompositionClassCount c k ≡ 5

  currentSaturated-3x5-candidate :
    ∀ c →
    saturatedForcedStableCountAt c ≡ 3 * 5

