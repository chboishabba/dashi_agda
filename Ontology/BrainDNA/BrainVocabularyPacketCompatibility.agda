module Ontology.BrainDNA.BrainVocabularyPacketCompatibility where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Vec using (Vec; map)

open import Ontology.Brain.BrainVocabularySurface as Brain using
  (BrainPacket; BrainState; BrainObservable; BrainChannel;
   BrainVocabularySurface; brainVocabularySurface; observeState;
   defaultBrainChannel)
open import Ontology.BrainDNA.PacketCodecBridge as Bridge using
  (BrainToken; quiet; edge; core; burst; BrainPacket; brainPacket;
   packetScanOrder; encodePacket; packetEmit; BrainDNACrossoverSurface;
   brainDNACrossoverSurface)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)
open import Ontology.DNA.Supervoxel4Adic using (Base)

infixr 9 _∘_
_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
      (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

------------------------------------------------------------------------
-- Compatibility surface between the local brain vocabulary and the
-- local brain-DNA packet codec bridge.

tokenOfNat : Nat → BrainToken
tokenOfNat zero = quiet
tokenOfNat (suc zero) = edge
tokenOfNat (suc (suc zero)) = core
tokenOfNat (suc (suc (suc _))) = burst

packetToBridge : ∀ {n} → Brain.BrainPacket n → Bridge.BrainPacket n
packetToBridge pkt = brainPacket (map tokenOfNat (BrainPacket.payload pkt))

stateToBridge : ∀ {n} → BrainState n → Bridge.BrainPacket n
stateToBridge st = packetToBridge (BrainState.packet st)

observeWidth-consistent :
  ∀ {n} (st : BrainState n) →
  BrainObservable.packetWidth (observeState st) ≡ n
observeWidth-consistent st = refl

statePacketOrder-lineMajor :
  ∀ {n} (st : BrainState n) →
  packetScanOrder (stateToBridge st) ≡ lineMajor
statePacketOrder-lineMajor st = refl

stateEmit-width-consistent :
  ∀ {n} (st : BrainState n) →
  packetEmit (stateToBridge st) ≡ (n , encodePacket (stateToBridge st))
stateEmit-width-consistent st = refl

record BrainVocabularyPacketCompatibilitySurface : Set₂ where
  field
    brainSurface : BrainVocabularySurface
    crossoverSurface : BrainDNACrossoverSurface
    packetMap : ∀ {n} → Brain.BrainPacket n → Bridge.BrainPacket n
    stateMap : ∀ {n} → BrainState n → Bridge.BrainPacket n
    packetOrderCompatible : ∀ {n} → BrainState n → ScanOrder
    encodedBases : ∀ {n} → BrainState n → Vec Base n
    emittedBases : ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)

brainVocabularyPacketCompatibilitySurface :
  BrainVocabularyPacketCompatibilitySurface
brainVocabularyPacketCompatibilitySurface = record
  { brainSurface = brainVocabularySurface
  ; crossoverSurface = brainDNACrossoverSurface
  ; packetMap = packetToBridge
  ; stateMap = stateToBridge
  ; packetOrderCompatible = packetScanOrder ∘ stateToBridge
  ; encodedBases = encodePacket ∘ stateToBridge
  ; emittedBases = packetEmit ∘ stateToBridge
  }
