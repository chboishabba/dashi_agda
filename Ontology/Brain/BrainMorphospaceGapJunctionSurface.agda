module Ontology.Brain.BrainMorphospaceGapJunctionSurface where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using
  (BrainState; stateOf)
open import Ontology.Brain.BrainCoarseSummarySurface using
  (BrainCoarseSummary; summarizeState)
open import Ontology.Brain.BrainExtractionSurface using
  (BrainExtraction; BrainExtractionSurface; brainExtractionSurface;
   extractState)
open import Ontology.Brain.BrainInvariantSurface using
  (BrainCarrierInvariant; BrainInvariantSurface; brainInvariantSurface;
   invariantOfState; invariantOfExtraction)
open import Ontology.Brain.BrainInvariantDepth using
  (BrainInvariantDepthSurface; brainInvariantDepthSurface;
   invariantDepth; stateDepth; extractionDepth)
open import Ontology.Brain.BrainInvariantSemanticLaws using
  (BrainInvariantSemantic; BrainInvariantSemanticLawsSurface;
   brainInvariantSemanticLawsSurface; semanticOfInvariant; semanticOfState;
   stateOf-zero-semantic; stateOf-suc-semantic)

------------------------------------------------------------------------
-- Bounded morphospace / gap-junction packaging for the local brain lane.
--
-- This stays theorem-thin and non-claiming. It does not model biological
-- gap junctions or complete morphospace dynamics. It only packages the
-- current extraction/invariant/depth/semantic owners into one local
-- coherence and stabilization surface.

record BrainMorphospacePoint : Set where
  constructor brainMorphospacePoint
  field
    width : Nat
    layer : Nat
    depth : Nat
    semantic : BrainInvariantSemantic

morphospaceOfExtraction : BrainExtraction → BrainMorphospacePoint
morphospaceOfExtraction extraction =
  brainMorphospacePoint
    (BrainExtraction.width extraction)
    (BrainExtraction.layer extraction)
    (extractionDepth extraction)
    (semanticOfInvariant (invariantOfExtraction extraction))

morphospaceOfState : ∀ {n} → BrainState n → BrainMorphospacePoint
morphospaceOfState st = morphospaceOfExtraction (extractState st)

stabilizeMorphospace : BrainMorphospacePoint → BrainMorphospacePoint
stabilizeMorphospace point = point

recursiveCorrectMorphospace : BrainMorphospacePoint → BrainMorphospacePoint
recursiveCorrectMorphospace point = stabilizeMorphospace point

gapJunctionCarrier : BrainMorphospacePoint → Nat
gapJunctionCarrier point = BrainMorphospacePoint.depth point

gapJunctionCoherence : BrainMorphospacePoint → BrainMorphospacePoint → Nat
gapJunctionCoherence left right =
  gapJunctionCarrier left + gapJunctionCarrier right

state-morphospace-width-exact :
  ∀ {n} (st : BrainState n) →
  BrainMorphospacePoint.width (morphospaceOfState st) ≡ n
state-morphospace-width-exact st = refl

state-morphospace-layer-exact :
  ∀ {n} (st : BrainState n) →
  BrainMorphospacePoint.layer (morphospaceOfState st)
    ≡
  BrainCoarseSummary.layer (summarizeState st)
state-morphospace-layer-exact st = refl

state-morphospace-depth-exact :
  ∀ {n} (st : BrainState n) →
  BrainMorphospacePoint.depth (morphospaceOfState st) ≡ stateDepth st
state-morphospace-depth-exact st = refl

state-morphospace-semantic-exact :
  ∀ {n} (st : BrainState n) →
  BrainMorphospacePoint.semantic (morphospaceOfState st) ≡ semanticOfState st
state-morphospace-semantic-exact st = refl

stabilize-idempotent :
  ∀ point →
  stabilizeMorphospace (stabilizeMorphospace point) ≡ stabilizeMorphospace point
stabilize-idempotent point = refl

recursive-correct-stable :
  ∀ point →
  recursiveCorrectMorphospace (recursiveCorrectMorphospace point)
    ≡
  recursiveCorrectMorphospace point
recursive-correct-stable point = refl

gap-junction-self-coherent :
  ∀ point →
  gapJunctionCoherence point point ≡ gapJunctionCarrier point + gapJunctionCarrier point
gap-junction-self-coherent point = refl

stateOf-zero-morphospace-quiescent :
  ∀ (xs : Vec Nat zero) →
  BrainMorphospacePoint.semantic (morphospaceOfState (stateOf xs))
    ≡
  semanticOfState (stateOf xs)
stateOf-zero-morphospace-quiescent xs = refl

stateOf-suc-morphospace-engaged :
  ∀ {n} (xs : Vec Nat (suc n)) →
  BrainMorphospacePoint.semantic (morphospaceOfState (stateOf xs))
    ≡
  semanticOfState (stateOf xs)
stateOf-suc-morphospace-engaged xs = refl

record BrainMorphospaceGapJunctionSurface : Set₂ where
  field
    extractionSurface : BrainExtractionSurface
    invariantSurface : BrainInvariantSurface
    depthSurface : BrainInvariantDepthSurface
    semanticSurface : BrainInvariantSemanticLawsSurface

    MorphospacePoint : Set
    morphospaceOf : ∀ {n} → BrainState n → MorphospacePoint
    stabilize : MorphospacePoint → MorphospacePoint
    recursiveCorrect : MorphospacePoint → MorphospacePoint
    coherence : MorphospacePoint → MorphospacePoint → Nat

brainMorphospaceGapJunctionSurface : BrainMorphospaceGapJunctionSurface
brainMorphospaceGapJunctionSurface = record
  { extractionSurface = brainExtractionSurface
  ; invariantSurface = brainInvariantSurface
  ; depthSurface = brainInvariantDepthSurface
  ; semanticSurface = brainInvariantSemanticLawsSurface
  ; MorphospacePoint = BrainMorphospacePoint
  ; morphospaceOf = morphospaceOfState
  ; stabilize = stabilizeMorphospace
  ; recursiveCorrect = recursiveCorrectMorphospace
  ; coherence = gapJunctionCoherence
  }
