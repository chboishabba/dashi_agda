module Ontology.BrainDNA.BrainCodecDepthLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Sigma using (Σ; _,_; snd)
open import Data.Vec using (Vec; [])

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.BrainDNA.BrainCodecAdmissibilityBridge as Bridge using
  (BrainCodecAdmissibilityBridgeSurface; brainCodecAdmissibilityBridgeSurface;
   stateEncodedBases; stateEmittedBases; statePacketizedEmission;
   stateRecoveredEmission; stateRecoveryBoundary;
   statePacketizedEmissionShape; stateRecoveredEmissionShape)
open import Ontology.BrainDNA.BrainStateCrossoverLaws as StateLaw using
  (BrainStateCrossoverLawSurface; brainStateCrossoverLawSurface)
open import Ontology.BrainDNA.BrainVocabularyPacketCompatibility using
  (stateToBridge)
open import Ontology.BrainDNA.PacketCodecBridge using
  (packetEmit; packetEmit-identity)
open import Ontology.DNA.ChannelCodingSurface as CCS using
  (OuterRecoveryCode; IntegratedChannelSurface)
open import Ontology.DNA.CrossoverAttachmentLaws as CAL using
  (CrossoverAttachmentLawSurface; crossoverAttachmentLawSurface)
open import Ontology.DNA.CrossoverAttachmentSurface as CAS using
  (CrossoverAttachmentSurface)
open import Ontology.DNA.Supervoxel4Adic using (Base)

------------------------------------------------------------------------
-- Narrow codec-depth law surface for the local brain-DNA lane.
--
-- This stays theorem-thin and non-claiming. It does not add realistic
-- decoding claims. It only packages exact local laws about how the current
-- emitted/packetized/recovered boundary normalizes on the live owner
-- surfaces.

attachmentSurface : CrossoverAttachmentSurface
attachmentSurface =
  CAL.CrossoverAttachmentLawSurface.attachment CAL.crossoverAttachmentLawSurface

channelSurface : CCS.IntegratedChannelSurface
channelSurface = CAS.CrossoverAttachmentSurface.channel attachmentSurface

outerRecovery : OuterRecoveryCode
outerRecovery = IntegratedChannelSurface.outerCode channelSurface

stateEmitExact :
  ∀ {n} (st : BrainState n) →
  stateEmittedBases st ≡ (n , stateEncodedBases st)
stateEmitExact st = packetEmit-identity (stateToBridge st)

statePacketizedEmissionCanonical :
  ∀ {n} (st : BrainState n) →
  statePacketizedEmission st ≡ (zero , [])
statePacketizedEmissionCanonical st = refl

stateRecoveredEmissionCanonical :
  ∀ {n} (st : BrainState n) →
  stateRecoveredEmission st ≡ (zero , [])
stateRecoveredEmissionCanonical st = refl

stateRecoveredEmissionConstant :
  ∀ {n m} (st₁ : BrainState n) (st₂ : BrainState m) →
  stateRecoveredEmission st₁ ≡ stateRecoveredEmission st₂
stateRecoveredEmissionConstant st₁ st₂ = refl

stateRecoveredPacketizeRecoverStable :
  ∀ {n} (st : BrainState n) →
  CCS.OuterRecoveryCode.recover outerRecovery
    (snd (CCS.OuterRecoveryCode.packetize outerRecovery
      (snd (stateRecoveredEmission st))))
    ≡
  stateRecoveredEmission st
stateRecoveredPacketizeRecoverStable st = refl

stateRecoveryBoundaryExact : stateRecoveryBoundary ≡ 3
stateRecoveryBoundaryExact = refl

record BrainCodecDepthLawSurface : Set₂ where
  field
    codecBridge : BrainCodecAdmissibilityBridgeSurface
    stateLaws : BrainStateCrossoverLawSurface
    dnaLaws : CrossoverAttachmentLawSurface

    encoded : ∀ {n} → BrainState n → Vec Base n
    emitted : ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
    packetized : ∀ {n} → BrainState n → Σ Nat (λ k → Vec Nat k)
    recovered : ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
    recoveryBoundary : Nat

brainCodecDepthLawSurface : BrainCodecDepthLawSurface
brainCodecDepthLawSurface = record
  { codecBridge = brainCodecAdmissibilityBridgeSurface
  ; stateLaws = brainStateCrossoverLawSurface
  ; dnaLaws = crossoverAttachmentLawSurface
  ; encoded = stateEncodedBases
  ; emitted = stateEmittedBases
  ; packetized = statePacketizedEmission
  ; recovered = stateRecoveredEmission
  ; recoveryBoundary = stateRecoveryBoundary
  }
