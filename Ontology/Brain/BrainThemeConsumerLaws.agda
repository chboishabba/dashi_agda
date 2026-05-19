module Ontology.Brain.BrainThemeConsumerLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using
  (BrainState; stateOf)
open import Ontology.Brain.BrainExtractionSurface using
  (BrainExtraction; BrainExtractionSurface; brainExtractionSurface;
   extractState)
open import Ontology.Brain.BrainInvariantSurface using
  (BrainCarrierInvariant; invariantOfState; invariantOfExtraction)
open import Ontology.Brain.BrainInvariantDepth using
  (BrainInvariantDepthSurface; brainInvariantDepthSurface;
   invariantDepth; stateDepth; extractionDepth; state-extraction-depth-exact)
open import Ontology.Brain.BrainInvariantSemanticLaws using
  (BrainInvariantSemantic; BrainInvariantSemanticLawsSurface;
   brainInvariantSemanticLawsSurface; semanticOfInvariant; semanticOfState;
   stateOf-zero-semantic; stateOf-suc-semantic)
open import Ontology.Brain.BrainMorphospaceGapJunctionSurface using
  (BrainMorphospaceGapJunctionSurface; brainMorphospaceGapJunctionSurface;
   BrainMorphospacePoint; morphospaceOfState; stabilizeMorphospace;
   recursiveCorrectMorphospace; gapJunctionCarrier; gapJunctionCoherence;
   state-morphospace-depth-exact; state-morphospace-semantic-exact;
   stabilize-idempotent; recursive-correct-stable)

------------------------------------------------------------------------
-- Bounded downstream consumer/law surface for the local brain theme lane.
--
-- This stays theorem-thin and non-claiming. It does not add biological
-- completeness. It only consumes the current extraction, invariant-depth,
-- invariant-semantics, and morphospace/gap-junction owners in one exact
-- downstream surface.

record BrainThemeConsumer : Set where
  constructor brainThemeConsumer
  field
    extractionRank : Nat
    semantic : BrainInvariantSemantic
    morphospaceDepth : Nat
    coherenceWithSelf : Nat

consumeStateTheme : ∀ {n} → BrainState n → BrainThemeConsumer
consumeStateTheme st =
  brainThemeConsumer
    (extractionDepth (extractState st))
    (semanticOfState st)
    (BrainMorphospacePoint.depth (morphospaceOfState st))
    (gapJunctionCoherence (morphospaceOfState st) (morphospaceOfState st))

consumer-extraction-depth-exact :
  ∀ {n} (st : BrainState n) →
  BrainThemeConsumer.extractionRank (consumeStateTheme st)
    ≡
  stateDepth st
consumer-extraction-depth-exact st = state-extraction-depth-exact st

consumer-semantic-exact :
  ∀ {n} (st : BrainState n) →
  BrainThemeConsumer.semantic (consumeStateTheme st) ≡ semanticOfState st
consumer-semantic-exact st = refl

consumer-morphospace-depth-exact :
  ∀ {n} (st : BrainState n) →
  BrainThemeConsumer.morphospaceDepth (consumeStateTheme st)
    ≡
  stateDepth st
consumer-morphospace-depth-exact st = state-morphospace-depth-exact st

consumer-self-coherence-exact :
  ∀ {n} (st : BrainState n) →
  BrainThemeConsumer.coherenceWithSelf (consumeStateTheme st)
    ≡
  stateDepth st + stateDepth st
consumer-self-coherence-exact st = refl

consumer-stabilize-idempotent :
  ∀ {n} (st : BrainState n) →
  stabilizeMorphospace (stabilizeMorphospace (morphospaceOfState st))
    ≡
  stabilizeMorphospace (morphospaceOfState st)
consumer-stabilize-idempotent st = stabilize-idempotent (morphospaceOfState st)

consumer-recursive-correct-stable :
  ∀ {n} (st : BrainState n) →
  recursiveCorrectMorphospace
    (recursiveCorrectMorphospace (morphospaceOfState st))
    ≡
  recursiveCorrectMorphospace (morphospaceOfState st)
consumer-recursive-correct-stable st =
  recursive-correct-stable (morphospaceOfState st)

consumer-zero-state-quiescent :
  ∀ (xs : Vec Nat zero) →
  BrainThemeConsumer.semantic (consumeStateTheme (stateOf xs))
    ≡
  semanticOfState (stateOf xs)
consumer-zero-state-quiescent xs = refl

consumer-suc-state-engaged :
  ∀ {n} (xs : Vec Nat (suc n)) →
  BrainThemeConsumer.semantic (consumeStateTheme (stateOf xs))
    ≡
  semanticOfState (stateOf xs)
consumer-suc-state-engaged xs = refl

record BrainThemeConsumerLawSurface : Set₂ where
  field
    extractionSurface : BrainExtractionSurface
    depthSurface : BrainInvariantDepthSurface
    semanticSurface : BrainInvariantSemanticLawsSurface
    morphospaceSurface : BrainMorphospaceGapJunctionSurface

    ThemeConsumer : Set
    consume : ∀ {n} → BrainState n → ThemeConsumer

brainThemeConsumerLawSurface : BrainThemeConsumerLawSurface
brainThemeConsumerLawSurface = record
  { extractionSurface = brainExtractionSurface
  ; depthSurface = brainInvariantDepthSurface
  ; semanticSurface = brainInvariantSemanticLawsSurface
  ; morphospaceSurface = brainMorphospaceGapJunctionSurface
  ; ThemeConsumer = BrainThemeConsumer
  ; consume = consumeStateTheme
  }
