module Ontology.Brain.BrainLearningEigenbasisSurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using
  (BrainState; stateOf)
open import Ontology.Brain.BrainCoarseSummarySurface using
  (BrainCoarseSummary; summarizeState)
open import Ontology.Brain.BrainExtractionSurface using
  (BrainExtraction; extractState)
open import Ontology.Brain.BrainInvariantSurface using
  (BrainCarrierInvariant; invariantOfState; invariantOfSummary;
   invariantOfExtraction)
open import Ontology.Brain.BrainInvariantDepth using
  (_⊎_; inj₁; inj₂; BrainInvariantDepthSurface; brainInvariantDepthSurface;
   invariantDepth; stateDepth)

------------------------------------------------------------------------
-- Local theorem-thin owner surface for a bounded representation phase
-- profile.
--
-- This is intentionally static and non-claiming. It does not assert any
-- gradient-descent dynamics, optimization theorem, or proved learning
-- transition. It only packages a small local phase classifier and exact
-- coherence witnesses over the existing local brain carriers.

data BrainRepresentationPhase : Set where
  interferenceField : BrainRepresentationPhase
  eigenbasisAligned : BrainRepresentationPhase

phaseThreshold : Nat
phaseThreshold = suc zero

phaseOfInvariant : BrainCarrierInvariant → BrainRepresentationPhase
phaseOfInvariant inv with invariantDepth inv
... | zero = interferenceField
... | suc _ = eigenbasisAligned

phaseOfSummary : BrainCoarseSummary → BrainRepresentationPhase
phaseOfSummary summary = phaseOfInvariant (invariantOfSummary summary)

phaseOfExtraction : BrainExtraction → BrainRepresentationPhase
phaseOfExtraction extraction = phaseOfInvariant (invariantOfExtraction extraction)

phaseOfState : ∀ {n} → BrainState n → BrainRepresentationPhase
phaseOfState st = phaseOfInvariant (invariantOfState st)

state-summary-phase-exact :
  ∀ {n} (st : BrainState n) →
  phaseOfState st ≡ phaseOfSummary (summarizeState st)
state-summary-phase-exact st = refl

state-extraction-phase-exact :
  ∀ {n} (st : BrainState n) →
  phaseOfState st ≡ phaseOfExtraction (extractState st)
state-extraction-phase-exact st = refl

stateOf-zero-phase :
  ∀ (xs : Vec Nat zero) →
  phaseOfState (stateOf xs) ≡ interferenceField
stateOf-zero-phase xs = refl

stateOf-suc-phase :
  ∀ {n} (xs : Vec Nat (suc n)) →
  phaseOfState (stateOf xs) ≡ eigenbasisAligned
stateOf-suc-phase xs = refl

stateOf-depth-phase-coherent :
  ∀ {n} (xs : Vec Nat n) →
  (Σ (stateDepth (stateOf xs) ≡ zero)
     (λ _ → phaseOfState (stateOf xs) ≡ interferenceField))
  ⊎
  (Σ (stateDepth (stateOf xs) ≡ suc zero)
     (λ _ → phaseOfState (stateOf xs) ≡ eigenbasisAligned))
stateOf-depth-phase-coherent {zero} xs =
  inj₁ (refl , refl)
stateOf-depth-phase-coherent {suc n} xs =
  inj₂ (refl , refl)

record BrainLearningEigenbasisProfile : Set where
  constructor brainLearningEigenbasisProfile
  field
    threshold : Nat
    phase : BrainRepresentationPhase
    width : Nat
    layer : Nat
    activeFlag : Bool

profileOfState : ∀ {n} → BrainState n → BrainLearningEigenbasisProfile
profileOfState st =
  brainLearningEigenbasisProfile
    phaseThreshold
    (phaseOfState st)
    (BrainCarrierInvariant.width (invariantOfState st))
    (BrainCarrierInvariant.layer (invariantOfState st))
    (BrainCarrierInvariant.activeFlag (invariantOfState st))

profile-threshold-exact :
  ∀ {n} (st : BrainState n) →
  BrainLearningEigenbasisProfile.threshold (profileOfState st) ≡ phaseThreshold
profile-threshold-exact st = refl

profile-phase-exact :
  ∀ {n} (st : BrainState n) →
  BrainLearningEigenbasisProfile.phase (profileOfState st) ≡ phaseOfState st
profile-phase-exact st = refl

profile-width-exact :
  ∀ {n} (st : BrainState n) →
  BrainLearningEigenbasisProfile.width (profileOfState st) ≡ n
profile-width-exact st = refl

profile-stateOf-width-layer-coherent :
  ∀ {n} (xs : Vec Nat n) →
  BrainLearningEigenbasisProfile.width (profileOfState (stateOf xs))
    ≡
  BrainLearningEigenbasisProfile.layer (profileOfState (stateOf xs))
profile-stateOf-width-layer-coherent xs = refl

record BrainLearningEigenbasisSurface : Set₂ where
  field
    invariantDepthSurface : BrainInvariantDepthSurface
    Phase : Set
    threshold : Nat
    classify : ∀ {n} → BrainState n → Phase
    profile : ∀ {n} → BrainState n → BrainLearningEigenbasisProfile

brainLearningEigenbasisSurface : BrainLearningEigenbasisSurface
brainLearningEigenbasisSurface = record
  { invariantDepthSurface = brainInvariantDepthSurface
  ; Phase = BrainRepresentationPhase
  ; threshold = phaseThreshold
  ; classify = phaseOfState
  ; profile = profileOfState
  }
