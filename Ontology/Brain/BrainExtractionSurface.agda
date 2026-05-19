module Ontology.Brain.BrainExtractionSurface where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using
  (BrainPacket; BrainState; BrainObservable; BrainVocabularySurface;
   brainVocabularySurface; activeByWidth; observeState; stateOf)
open import Ontology.Brain.BrainCoarseSummarySurface using
  (BrainCoarseSummary; BrainCoarseSummarySurface; brainCoarseSummarySurface;
   summarizeState)

------------------------------------------------------------------------
-- Local extraction/coarse-graining surface for the brain lane.
--
-- This remains theorem-thin and non-claiming: it does not infer latent
-- neuroscience structure. It only packages the metadata already exposed
-- by the local vocabulary and coarse-summary owners into an explicit
-- coarse-grained extraction object.

record BrainExtraction : Set where
  constructor brainExtraction
  field
    width : Nat
    layer : Nat
    activeFlag : Bool

extractSummary : BrainCoarseSummary → BrainExtraction
extractSummary summary =
  brainExtraction
    (BrainCoarseSummary.width summary)
    (BrainCoarseSummary.layer summary)
    (BrainCoarseSummary.activeFlag summary)

extractObservable : BrainObservable → BrainExtraction
extractObservable obs =
  brainExtraction
    (BrainObservable.packetWidth obs)
    (BrainObservable.layerTag obs)
    (BrainObservable.activeFlag obs)

extractState : ∀ {n} → BrainState n → BrainExtraction
extractState st = extractSummary (summarizeState st)

extractSummary-exact :
  ∀ {n} (st : BrainState n) →
  extractState st ≡ extractSummary (summarizeState st)
extractSummary-exact st = refl

extractObservable-exact :
  ∀ {n} (st : BrainState n) →
  extractState st ≡ extractObservable (observeState st)
extractObservable-exact st = refl

extractWidth-compatible :
  ∀ {n} (st : BrainState n) →
  BrainExtraction.width (extractState st)
    ≡
  BrainObservable.packetWidth (observeState st)
extractWidth-compatible st = refl

extractLayer-compatible :
  ∀ {n} (st : BrainState n) →
  BrainExtraction.layer (extractState st)
    ≡
  BrainObservable.layerTag (observeState st)
extractLayer-compatible st = refl

extractActive-compatible :
  ∀ {n} (st : BrainState n) →
  BrainExtraction.activeFlag (extractState st)
    ≡
  BrainObservable.activeFlag (observeState st)
extractActive-compatible st = refl

extractStateOf-layer :
  ∀ {n} (xs : Vec Nat n) →
  BrainExtraction.layer (extractState (stateOf xs)) ≡ n
extractStateOf-layer xs = refl

extractStateOf-active :
  ∀ {n} (xs : Vec Nat n) →
  BrainExtraction.activeFlag (extractState (stateOf xs)) ≡ activeByWidth n
extractStateOf-active xs = refl

record BrainExtractionSurface : Set₂ where
  field
    vocabularySurface : BrainVocabularySurface
    coarseSummarySurface : BrainCoarseSummarySurface
    Extraction : Set
    extract : ∀ {n} → BrainState n → Extraction
    extractFromSummary : BrainCoarseSummary → Extraction
    extractFromObservable : BrainObservable → Extraction

brainExtractionSurface : BrainExtractionSurface
brainExtractionSurface = record
  { vocabularySurface = brainVocabularySurface
  ; coarseSummarySurface = brainCoarseSummarySurface
  ; Extraction = BrainExtraction
  ; extract = extractState
  ; extractFromSummary = extractSummary
  ; extractFromObservable = extractObservable
  }
