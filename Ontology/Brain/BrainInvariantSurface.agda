module Ontology.Brain.BrainInvariantSurface where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using
  (BrainState; BrainObservable; activeByWidth; observeState; stateOf)
open import Ontology.Brain.BrainCoarseSummarySurface using
  (BrainCoarseSummary; summarizeState)
open import Ontology.Brain.BrainExtractionSurface using
  (BrainExtraction; extractState)

------------------------------------------------------------------------
-- Small invariant surface for the local brain lane.
-- This stays honest on the current carrier: it only packages exact
-- width/layer/activity equalities already exhibited by `stateOf`,
-- `summarizeState`, and `extractState`.

record BrainCarrierInvariant : Set where
  constructor brainCarrierInvariant
  field
    width : Nat
    layer : Nat
    activeFlag : Bool

invariantOfState : ∀ {n} → BrainState n → BrainCarrierInvariant
invariantOfState st =
  brainCarrierInvariant
    (BrainObservable.packetWidth (observeState st))
    (BrainObservable.layerTag (observeState st))
    (BrainObservable.activeFlag (observeState st))

invariantOfSummary : BrainCoarseSummary → BrainCarrierInvariant
invariantOfSummary summary =
  brainCarrierInvariant
    (BrainCoarseSummary.width summary)
    (BrainCoarseSummary.layer summary)
    (BrainCoarseSummary.activeFlag summary)

invariantOfExtraction : BrainExtraction → BrainCarrierInvariant
invariantOfExtraction extraction =
  brainCarrierInvariant
    (BrainExtraction.width extraction)
    (BrainExtraction.layer extraction)
    (BrainExtraction.activeFlag extraction)

summaryInvariant-exact :
  ∀ {n} (st : BrainState n) →
  invariantOfState st ≡ invariantOfSummary (summarizeState st)
summaryInvariant-exact st = refl

extractionInvariant-exact :
  ∀ {n} (st : BrainState n) →
  invariantOfState st ≡ invariantOfExtraction (extractState st)
extractionInvariant-exact st = refl

stateOf-width≡layer :
  ∀ {n} (xs : Vec Nat n) →
  BrainCarrierInvariant.width (invariantOfState (stateOf xs))
    ≡
  BrainCarrierInvariant.layer (invariantOfState (stateOf xs))
stateOf-width≡layer xs = refl

stateOf-active-by-width :
  ∀ {n} (xs : Vec Nat n) →
  BrainCarrierInvariant.activeFlag (invariantOfState (stateOf xs))
    ≡
  activeByWidth (BrainCarrierInvariant.width (invariantOfState (stateOf xs)))
stateOf-active-by-width xs = refl

record BrainInvariantSurface : Set₁ where
  field
    Invariant : Set
    summarizeInvariant : ∀ {n} → BrainState n → Invariant

brainInvariantSurface : BrainInvariantSurface
brainInvariantSurface = record
  { Invariant = BrainCarrierInvariant
  ; summarizeInvariant = invariantOfState
  }
