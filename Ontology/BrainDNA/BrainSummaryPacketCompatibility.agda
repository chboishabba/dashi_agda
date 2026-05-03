module Ontology.BrainDNA.BrainSummaryPacketCompatibility where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface as Brain using
  (BrainState; BrainObservable; observeState)
open import Ontology.Brain.BrainCoarseSummarySurface as Summary using
  (BrainCoarseSummary; BrainCoarseSummarySurface; brainCoarseSummarySurface;
   summarizeState)
open import Ontology.BrainDNA.PacketCodecBridge as Bridge using
  (BrainPacket; packetScanOrder; encodePacket; packetEmit)
open import Ontology.BrainDNA.BrainVocabularyPacketCompatibility as Compat using
  (BrainVocabularyPacketCompatibilitySurface;
   brainVocabularyPacketCompatibilitySurface; stateToBridge)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)
open import Ontology.DNA.Supervoxel4Adic using (Base)

------------------------------------------------------------------------
-- Summary-level compatibility surface between the local brain coarse
-- summaries and the local brain-DNA packet/encoding boundary.
--
-- This remains theorem-thin and honest on the current carrier:
-- a coarse summary does not determine packet payload, but it does
-- determine summary-side metadata that can be checked exactly against
-- the packet boundary induced by the existing state map.

record BrainSummaryPacketView : Set where
  constructor brainSummaryPacketView
  field
    width : Nat
    layer : Nat
    activeFlag : Bool
    order : ScanOrder

summaryPacketView : BrainCoarseSummary → BrainSummaryPacketView
summaryPacketView summary =
  brainSummaryPacketView
    (BrainCoarseSummary.width summary)
    (BrainCoarseSummary.layer summary)
    (BrainCoarseSummary.activeFlag summary)
    lineMajor

summaryStatePacketView : ∀ {n} → BrainState n → BrainSummaryPacketView
summaryStatePacketView st = summaryPacketView (summarizeState st)

summaryWidth-compatible :
  ∀ {n} (st : BrainState n) →
  BrainSummaryPacketView.width (summaryStatePacketView st)
    ≡
  BrainObservable.packetWidth (observeState st)
summaryWidth-compatible st = refl

summaryLayer-compatible :
  ∀ {n} (st : BrainState n) →
  BrainSummaryPacketView.layer (summaryStatePacketView st)
    ≡
  BrainObservable.layerTag (observeState st)
summaryLayer-compatible st = refl

summaryActive-compatible :
  ∀ {n} (st : BrainState n) →
  BrainSummaryPacketView.activeFlag (summaryStatePacketView st)
    ≡
  BrainObservable.activeFlag (observeState st)
summaryActive-compatible st = refl

summaryOrder-lineMajor :
  ∀ {n} (st : BrainState n) →
  BrainSummaryPacketView.order (summaryStatePacketView st)
    ≡
  packetScanOrder (stateToBridge st)
summaryOrder-lineMajor st = refl

summaryEmit-width-compatible :
  ∀ {n} (st : BrainState n) →
  packetEmit (stateToBridge st)
    ≡
  (BrainSummaryPacketView.width (summaryStatePacketView st) , encodePacket (stateToBridge st))
summaryEmit-width-compatible st = refl

record BrainSummaryPacketCompatibilitySurface : Set₂ where
  field
    summarySurface : BrainCoarseSummarySurface
    vocabularyPacketSurface : BrainVocabularyPacketCompatibilitySurface
    packetView : BrainCoarseSummary → BrainSummaryPacketView
    packetOrder : BrainCoarseSummary → ScanOrder
    emittedWidthAndBases :
      ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)

brainSummaryPacketCompatibilitySurface :
  BrainSummaryPacketCompatibilitySurface
brainSummaryPacketCompatibilitySurface = record
  { summarySurface = brainCoarseSummarySurface
  ; vocabularyPacketSurface = brainVocabularyPacketCompatibilitySurface
  ; packetView = summaryPacketView
  ; packetOrder = BrainSummaryPacketView.order ∘ summaryPacketView
  ; emittedWidthAndBases = packetEmit ∘ stateToBridge
  }
  where
  infixr 9 _∘_
  _∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
        (B → C) → (A → B) → A → C
  (f ∘ g) x = f (g x)
