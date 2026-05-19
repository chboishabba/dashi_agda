module Ontology.Brain.BrainCoarseSummarySurface where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface

------------------------------------------------------------------------
-- Small coarse summary surface for the local brain lane.
-- This remains theorem-thin: it summarizes the existing vocabulary
-- boundary without claiming richer structure than width/layer/activity.

record BrainCoarseSummary : Set where
  constructor brainCoarseSummary
  field
    width : Nat
    layer : Nat
    activeFlag : Bool

summarizeState : ∀ {n} → BrainState n → BrainCoarseSummary
summarizeState st =
  brainCoarseSummary
    (BrainObservable.packetWidth (observeState st))
    (BrainObservable.layerTag (observeState st))
    (BrainObservable.activeFlag (observeState st))

summaryWidth : ∀ {n} (st : BrainState n) → BrainCoarseSummary.width (summarizeState st) ≡ n
summaryWidth st = refl

summaryLayer : ∀ {n} (st : BrainState n) → BrainCoarseSummary.layer (summarizeState st) ≡ BrainState.coarseLayer st
summaryLayer st = refl

summaryActive : ∀ {n} (st : BrainState n) → BrainCoarseSummary.activeFlag (summarizeState st) ≡ BrainState.active st
summaryActive st = refl

summaryStateOfLayer :
  ∀ {n} (xs : Vec Nat n) →
  BrainCoarseSummary.layer (summarizeState (stateOf xs)) ≡ n
summaryStateOfLayer xs = refl

summaryStateOfActive :
  ∀ {n} (xs : Vec Nat n) →
  BrainCoarseSummary.activeFlag (summarizeState (stateOf xs)) ≡ activeByWidth n
summaryStateOfActive xs = refl

record BrainCoarseSummarySurface : Set₁ where
  field
    Summary : Set
    summarize : ∀ {n} → BrainState n → Summary

brainCoarseSummarySurface : BrainCoarseSummarySurface
brainCoarseSummarySurface = record
  { Summary = BrainCoarseSummary
  ; summarize = summarizeState
  }
