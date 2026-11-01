module Ontology.Brain.BrainInvariantSemanticLaws where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using
  (BrainState; stateOf)
open import Ontology.Brain.BrainInvariantSurface using
  (BrainCarrierInvariant; invariantOfState)
open import Ontology.Brain.BrainInvariantDepth using
  (invariantDepth; stateDepth)

------------------------------------------------------------------------
-- Bounded invariant-semantics surface for the local brain lane.
-- This remains adjacent and non-claiming: it does not infer neuroscience
-- content, only a coarse semantic reading of the existing `0/1` depth.

data BrainInvariantSemantic : Set where
  quiescent engaged : BrainInvariantSemantic

semanticOfInvariant : BrainCarrierInvariant → BrainInvariantSemantic
semanticOfInvariant inv with invariantDepth inv
... | zero = quiescent
... | suc _ = engaged

semanticOfState : ∀ {n} → BrainState n → BrainInvariantSemantic
semanticOfState st = semanticOfInvariant (invariantOfState st)

quiescent-active-false :
  ∀ inv →
  invariantDepth inv ≡ zero →
  BrainCarrierInvariant.activeFlag inv ≡ false
quiescent-active-false inv depth≡0 with BrainCarrierInvariant.activeFlag inv
... | false = refl
... | true with depth≡0
... | ()

engaged-active-true :
  ∀ inv →
  invariantDepth inv ≡ suc zero →
  BrainCarrierInvariant.activeFlag inv ≡ true
engaged-active-true inv depth≡1 with BrainCarrierInvariant.activeFlag inv
... | true = refl
... | false with depth≡1
... | ()

semantic-quiescent-depth0 :
  ∀ inv →
  semanticOfInvariant inv ≡ quiescent →
  invariantDepth inv ≡ zero
semantic-quiescent-depth0 inv sem≡ with invariantDepth inv | sem≡
... | zero | _ = refl
... | suc _ | ()

semantic-engaged-depth1 :
  ∀ inv →
  semanticOfInvariant inv ≡ engaged →
  invariantDepth inv ≡ suc zero
semantic-engaged-depth1 inv sem≡ with BrainCarrierInvariant.activeFlag inv | sem≡
... | false | ()
... | true | _ = refl

stateOf-zero-semantic :
  ∀ (xs : Vec Nat zero) →
  semanticOfState (stateOf xs) ≡ quiescent
stateOf-zero-semantic xs = refl

stateOf-suc-semantic :
  ∀ {n} (xs : Vec Nat (suc n)) →
  semanticOfState (stateOf xs) ≡ engaged
stateOf-suc-semantic xs = refl

state-semantic-depth-exact :
  ∀ {n} (st : BrainState n) →
  semanticOfState st ≡ quiescent → stateDepth st ≡ zero
state-semantic-depth-exact st = semantic-quiescent-depth0 (invariantOfState st)

record BrainInvariantSemanticLawsSurface : Set₁ where
  field
    classify : BrainCarrierInvariant → BrainInvariantSemantic
    quiescentLaw : ∀ inv → classify inv ≡ quiescent → invariantDepth inv ≡ zero
    engagedLaw : ∀ inv → classify inv ≡ engaged → invariantDepth inv ≡ suc zero

brainInvariantSemanticLawsSurface : BrainInvariantSemanticLawsSurface
brainInvariantSemanticLawsSurface = record
  { classify = semanticOfInvariant
  ; quiescentLaw = semantic-quiescent-depth0
  ; engagedLaw = semantic-engaged-depth1
  }
