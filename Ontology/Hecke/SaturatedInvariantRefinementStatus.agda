module Ontology.Hecke.SaturatedInvariantRefinementStatus where

open import Agda.Builtin.Equality using (_≡_)

open import Ontology.Hecke.CurrentGeneratorPersistenceRefinement
  using
    ( currentExactOrbitPressureAt
    ; currentOrbitPressureLaw
    ; currentStayRefinement
    )
open import Ontology.Hecke.CurrentSaturatedForcedStableCollapse
  using
    ( CurrentSaturatedGenerator
    ; saturatedForcedStableCountAt
    ; saturatedForcedStableCount≡15
    )
open import Ontology.Hecke.CurrentSaturatedOrbitSummaryCollapse
  using (saturatedOrbitSummary≡canonical)
open import Ontology.Hecke.CurrentSaturatedSectorHistogramComputations
  using
    ( CurrentSaturatedSectorHistograms
    ; all-current-sector-histograms-collapse
    ; sectorHistogramsAt
    ; some-current-sector-separates
    ; some-current-triad-package-separates
    )
open import Ontology.Hecke.CurrentSaturatedPredictedPairComparisons
  using
    ( PredictedLayer2ProofOrder
    ; predictedLayer2ProofOrder
    )
open import Ontology.Hecke.Layer2FiniteSearch
  using (FiniteLayer2Search; finiteLayer2Search)
open import Ontology.Hecke.Layer2FiniteSearchShell
  using (FiniteSearchShell; finiteLayer2SearchShell)

------------------------------------------------------------------------
-- Layer-status packaging for the current Hecke-side boundary.
--
-- Layer 1 is the already-landed coarse law on the current generator
-- taxonomy:
--
--   generator class
--     -> collapse class
--     -> stay refinement
--     -> exact p2 pressure
--
-- Layer 2 is the current open problem:
--
--   saturated branch
--     -> next separating invariant
--
-- This module does not claim the separator exists yet. It only makes the
-- finished-vs-open split explicit at the theorem-surface level.

record Layer1Closed : Set₁ where
  field
    stayRefinementLaw :
      _
    exactPressureLaw :
      _

record Layer2Open : Set₁ where
  field
    currentSaturatedSectorPackages :
      CurrentSaturatedGenerator → CurrentSaturatedSectorHistograms
    predictedProofOrder :
      PredictedLayer2ProofOrder
    finiteSearchShell :
      FiniteSearchShell
    finiteSearchProgram :
      FiniteLayer2Search
    sectorSeparatorTarget : Set
    triadSeparatorTarget : Set
    exhaustedFallback :
      _

layer1Closed : Layer1Closed
layer1Closed = record
  { stayRefinementLaw = currentStayRefinement
  ; exactPressureLaw = currentOrbitPressureLaw
  }

layer2Open : Layer2Open
layer2Open = record
  { currentSaturatedSectorPackages = sectorHistogramsAt
  ; predictedProofOrder = predictedLayer2ProofOrder
  ; finiteSearchShell = finiteLayer2SearchShell
  ; finiteSearchProgram = finiteLayer2Search
  ; sectorSeparatorTarget = some-current-sector-separates
  ; triadSeparatorTarget = some-current-triad-package-separates
  ; exhaustedFallback = all-current-sector-histograms-collapse
  }

------------------------------------------------------------------------
-- Current negative boundary carried explicitly.

saturatedForcedStable-collapsed :
  ∀ c →
  saturatedForcedStableCountAt c ≡ 15
saturatedForcedStable-collapsed = saturatedForcedStableCount≡15

saturatedCurrentOrbitSummary-collapsed :
  ∀ c →
  _
saturatedCurrentOrbitSummary-collapsed = saturatedOrbitSummary≡canonical
