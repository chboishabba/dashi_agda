module Ontology.Brain.BrainInvariantDepth where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using
  (BrainState; stateOf)
open import Ontology.Brain.BrainCoarseSummarySurface using
  (BrainCoarseSummary; summarizeState)
open import Ontology.Brain.BrainExtractionSurface using
  (BrainExtraction; extractState)
open import Ontology.Brain.BrainInvariantSurface using
  (BrainCarrierInvariant; invariantOfState; invariantOfSummary; invariantOfExtraction)

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

------------------------------------------------------------------------
-- Bounded depth surface for the local brain lane.
-- This is intentionally coarse and non-claiming: it only classifies the
-- current local carrier into quiescent depth 0 vs active depth 1.

invariantDepth : BrainCarrierInvariant → Nat
invariantDepth inv with BrainCarrierInvariant.activeFlag inv
... | false = zero
... | true = suc zero

summaryDepth : BrainCoarseSummary → Nat
summaryDepth summary = invariantDepth (invariantOfSummary summary)

extractionDepth : BrainExtraction → Nat
extractionDepth extraction = invariantDepth (invariantOfExtraction extraction)

stateDepth : ∀ {n} → BrainState n → Nat
stateDepth st = invariantDepth (invariantOfState st)

state-summary-depth-exact :
  ∀ {n} (st : BrainState n) →
  stateDepth st ≡ summaryDepth (summarizeState st)
state-summary-depth-exact st = refl

state-extraction-depth-exact :
  ∀ {n} (st : BrainState n) →
  stateDepth st ≡ extractionDepth (extractState st)
state-extraction-depth-exact st = refl

stateOf-zero-depth :
  ∀ (xs : Vec Nat zero) →
  stateDepth (stateOf xs) ≡ zero
stateOf-zero-depth xs = refl

stateOf-suc-depth :
  ∀ {n} (xs : Vec Nat (suc n)) →
  stateDepth (stateOf xs) ≡ suc zero
stateOf-suc-depth xs = refl

record BrainInvariantDepthSurface : Set₁ where
  field
    depth : BrainCarrierInvariant → Nat
    bounded : ∀ inv → (depth inv ≡ zero) ⊎ (depth inv ≡ suc zero)

invariantDepth-bounded :
  ∀ inv → (invariantDepth inv ≡ zero) ⊎ (invariantDepth inv ≡ suc zero)
invariantDepth-bounded inv with BrainCarrierInvariant.activeFlag inv
... | false = inj₁ refl
... | true = inj₂ refl

brainInvariantDepthSurface : BrainInvariantDepthSurface
brainInvariantDepthSurface = record
  { depth = invariantDepth
  ; bounded = invariantDepth-bounded
  }
