module Ontology.BrainDNA.BrainStateCrossoverLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; fst; snd)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface as Brain using (BrainState)
open import Ontology.BrainDNA.BrainVocabularyPacketCompatibility as Compat using
  (BrainVocabularyPacketCompatibilitySurface;
   brainVocabularyPacketCompatibilitySurface;
   stateToBridge;
   statePacketOrder-lineMajor;
   stateEmit-width-consistent)
open import Ontology.BrainDNA.PacketCodecBridge as Bridge using
  (packetAdmissibility; packetAdmissibility-consistent; packetEmit; encodePacket)
open import Ontology.DNA.ChannelCodingSurface as CCS using
  (genericAdmissibilityFlag)
open import Ontology.DNA.CrossoverAttachmentLaws as CAL using
  (CrossoverAttachmentLawSurface; crossoverAttachmentLawSurface)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)
open import Ontology.DNA.Supervoxel4Adic using (Base)

------------------------------------------------------------------------
-- Minimal state-origin law surface for the local brain-DNA crossover.
-- This lifts exact DNA-side emit/admissibility/length coherence to the
-- boundary where local brain states are mapped into the packet bridge.

record BrainStateCrossoverLawSurface : Set₂ where
  field
    compatibility : BrainVocabularyPacketCompatibilitySurface
    dnaLaws : CrossoverAttachmentLawSurface

    stateOrderLineMajor :
      ∀ {n} → BrainState n → ScanOrder

    stateEncodedBases :
      ∀ {n} → BrainState n → Vec Base n

    stateEmittedBases :
      ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)

    statePacketAdmissibilityExact :
      ∀ {n} (st : BrainState n) →
      packetAdmissibility (stateToBridge st)
        ≡ genericAdmissibilityFlag (stateEncodedBases st)

    stateEmitOutputGenericAdmissibility :
      ∀ {n} (st : BrainState n) →
      genericAdmissibilityFlag (snd (stateEmittedBases st))
        ≡ genericAdmissibilityFlag (stateEncodedBases st)

    stateEmitOutputLengthExact :
      ∀ {n} (st : BrainState n) →
      fst (stateEmittedBases st) ≡ n

statePacketAdmissibilityExact :
  ∀ {n} (st : BrainState n) →
  packetAdmissibility (stateToBridge st)
    ≡
  genericAdmissibilityFlag (encodePacket (stateToBridge st))
statePacketAdmissibilityExact st = packetAdmissibility-consistent (stateToBridge st)

stateEmitOutputGenericAdmissibility :
  ∀ {n} (st : BrainState n) →
  genericAdmissibilityFlag (snd (packetEmit (stateToBridge st)))
    ≡
  genericAdmissibilityFlag (encodePacket (stateToBridge st))
stateEmitOutputGenericAdmissibility st = refl

stateEmitOutputLengthExact :
  ∀ {n} (st : BrainState n) →
  fst (packetEmit (stateToBridge st)) ≡ n
stateEmitOutputLengthExact st = refl

brainStateCrossoverLawSurface : BrainStateCrossoverLawSurface
brainStateCrossoverLawSurface = record
  { compatibility = brainVocabularyPacketCompatibilitySurface
  ; dnaLaws = crossoverAttachmentLawSurface
  ; stateOrderLineMajor = λ st → lineMajor
  ; stateEncodedBases = encodePacket ∘ stateToBridge
  ; stateEmittedBases = packetEmit ∘ stateToBridge
  ; statePacketAdmissibilityExact = statePacketAdmissibilityExact
  ; stateEmitOutputGenericAdmissibility = stateEmitOutputGenericAdmissibility
  ; stateEmitOutputLengthExact = stateEmitOutputLengthExact
  }
  where
  infixr 9 _∘_
  _∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
        (B → C) → (A → B) → A → C
  (f ∘ g) x = f (g x)
