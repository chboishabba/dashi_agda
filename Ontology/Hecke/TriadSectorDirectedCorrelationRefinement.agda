module Ontology.Hecke.TriadSectorDirectedCorrelationRefinement where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

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
-- Directed correlation refinement above the scalar dot-product summary.
--
-- `TriadSectorCorrelationRefinement` keeps only three symmetric dot products.
-- That is the smallest correlation scalar, but it identifies interactions such
-- as stable(i) × illegal(j) with illegal(i) × stable(j).  The present module
-- keeps the full ordered 3 × 3 cross-bucket matrix for each directed sector
-- pair.  It is therefore the next minimal refinement that can detect routing,
-- entry/exit asymmetry, and composition-versus-cascade directionality without
-- widening the current finite generator domain.

record DirectedHistogramInteraction : Set where
  constructor directedHistogramInteraction
  field
    stableStable   : Nat
    stableIllegal  : Nat
    stableOther    : Nat
    illegalStable  : Nat
    illegalIllegal : Nat
    illegalOther   : Nat
    otherStable    : Nat
    otherIllegal   : Nat
    otherOther     : Nat

open DirectedHistogramInteraction public

directedInteraction :
  DefectHistogram → DefectHistogram → DirectedHistogramInteraction
directedInteraction source target = record
  { stableStable = stableCount source * stableCount target
  ; stableIllegal = stableCount source * illegalCount target
  ; stableOther = stableCount source * otherCount target
  ; illegalStable = illegalCount source * stableCount target
  ; illegalIllegal = illegalCount source * illegalCount target
  ; illegalOther = illegalCount source * otherCount target
  ; otherStable = otherCount source * stableCount target
  ; otherIllegal = otherCount source * illegalCount target
  ; otherOther = otherCount source * otherCount target
  }

------------------------------------------------------------------------
-- Preserve the cyclic orientation 0 → 1 → 2 → 0.

record DirectedTriadCorrelationSummary : Set where
  constructor directedTriadCorrelationSummary
  field
    directed01 : DirectedHistogramInteraction
    directed12 : DirectedHistogramInteraction
    directed20 : DirectedHistogramInteraction

open DirectedTriadCorrelationSummary public

directedTriadCorrelationOf :
  CurrentSaturatedSectorHistograms → DirectedTriadCorrelationSummary
directedTriadCorrelationOf h = record
  { directed01 = directedInteraction
      (CurrentSaturatedSectorHistograms.hist0 h)
      (CurrentSaturatedSectorHistograms.hist1 h)
  ; directed12 = directedInteraction
      (CurrentSaturatedSectorHistograms.hist1 h)
      (CurrentSaturatedSectorHistograms.hist2 h)
  ; directed20 = directedInteraction
      (CurrentSaturatedSectorHistograms.hist2 h)
      (CurrentSaturatedSectorHistograms.hist0 h)
  }

currentSaturatedDirectedTriadCorrelationAt :
  CurrentSaturatedGenerator → DirectedTriadCorrelationSummary
currentSaturatedDirectedTriadCorrelationAt c =
  directedTriadCorrelationOf (sectorHistogramsAt c)

------------------------------------------------------------------------
-- Projection back to the already-landed symmetric dot-product coordinates.
-- This is stated as a structure-preserving surface rather than importing the
-- scalar module and creating a dependency cycle.

record SymmetricCorrelationProjection : Set where
  constructor symmetricCorrelationProjection
  field
    projected01 : Nat
    projected12 : Nat
    projected20 : Nat

open SymmetricCorrelationProjection public

interactionDiagonal : DirectedHistogramInteraction → Nat
interactionDiagonal i =
  stableStable i + illegalIllegal i + otherOther i
  where
  open import Agda.Builtin.Nat using (_+_)

forgetDirection :
  DirectedTriadCorrelationSummary → SymmetricCorrelationProjection
forgetDirection c = record
  { projected01 = interactionDiagonal (directed01 c)
  ; projected12 = interactionDiagonal (directed12 c)
  ; projected20 = interactionDiagonal (directed20 c)
  }

------------------------------------------------------------------------
-- Fixed-domain decision surfaces.

postulate
  ⊥ : Set

  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

  ∃₂ : {A B : Set} → (A → B → Set) → Set

  currentSaturated-directedCorrelation-separates :
    ∃₂ λ c₁ c₂ →
      currentSaturatedDirectedTriadCorrelationAt c₁
        ≢
      currentSaturatedDirectedTriadCorrelationAt c₂

  currentSaturated-directedCorrelation-exhausted :
    ∀ c₁ c₂ →
      currentSaturatedDirectedTriadCorrelationAt c₁
        ≡
      currentSaturatedDirectedTriadCorrelationAt c₂
