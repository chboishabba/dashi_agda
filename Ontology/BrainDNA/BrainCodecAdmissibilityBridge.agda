module Ontology.BrainDNA.BrainCodecAdmissibilityBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; fst; snd)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.BrainDNA.BrainStateCrossoverLaws as StateLaws using
  (BrainStateCrossoverLawSurface; brainStateCrossoverLawSurface;
   statePacketAdmissibilityExact; stateEmitOutputGenericAdmissibility;
   stateEmitOutputLengthExact)
open import Ontology.BrainDNA.BrainVocabularyPacketCompatibility using
  (stateToBridge; stateEmit-width-consistent)
open import Ontology.BrainDNA.PacketCodecBridge using
  (packetEmit; encodePacket)
open import Ontology.DNA.ChannelCodingSurface as CCS using
  (IntegratedChannelSurface; OuterRecoveryCode; genericAdmissibilityFlag)
open import Ontology.DNA.CrossoverAttachmentLaws as CAL using
  (CrossoverAttachmentLawSurface; crossoverAttachmentLawSurface)
open import Ontology.DNA.CrossoverAttachmentSurface as CAS using
  (CrossoverAttachmentSurface)
open import Ontology.DNA.Supervoxel4Adic using (Base)

------------------------------------------------------------------------
-- Narrow local codec bridge surface for the brain-DNA lane.
--
-- This module stays theorem-thin and non-claiming. It does not claim
-- realistic decoding or biological recovery semantics. It only packages
-- the current admissibility-preserving emission boundary together with the
-- attached packetize/recover shape owned by the local DNA channel surface.

attachmentSurface : CrossoverAttachmentSurface
attachmentSurface =
  CAL.CrossoverAttachmentLawSurface.attachment CAL.crossoverAttachmentLawSurface

channelSurface : IntegratedChannelSurface
channelSurface = CAS.CrossoverAttachmentSurface.channel attachmentSurface

outerRecovery : OuterRecoveryCode
outerRecovery = IntegratedChannelSurface.outerCode channelSurface

stateEncodedBases : ∀ {n} → BrainState n → Vec Base n
stateEncodedBases st = encodePacket (stateToBridge st)

stateEmittedBases : ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
stateEmittedBases st = packetEmit (stateToBridge st)

statePacketizedEmission : ∀ {n} → BrainState n → Σ Nat (λ k → Vec Nat k)
statePacketizedEmission st =
  CCS.OuterRecoveryCode.packetize outerRecovery (snd (stateEmittedBases st))

stateRecoveredEmission : ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
stateRecoveredEmission st =
  CCS.OuterRecoveryCode.recover outerRecovery (snd (statePacketizedEmission st))

stateRecoveryBoundary : Nat
stateRecoveryBoundary = IntegratedChannelSurface.recoveryBoundary channelSurface

stateEmitPacketAdmissibilityExact :
  ∀ {n} (st : BrainState n) →
  genericAdmissibilityFlag (snd (stateEmittedBases st))
    ≡
  genericAdmissibilityFlag (stateEncodedBases st)
stateEmitPacketAdmissibilityExact st =
  StateLaws.stateEmitOutputGenericAdmissibility st

statePacketizedEmissionShape :
  ∀ {n} (st : BrainState n) →
  statePacketizedEmission st
    ≡
  CCS.OuterRecoveryCode.packetize outerRecovery (stateEncodedBases st)
statePacketizedEmissionShape st
  rewrite stateEmit-width-consistent st = refl

stateRecoveredEmissionShape :
  ∀ {n} (st : BrainState n) →
  stateRecoveredEmission st
    ≡
  CCS.OuterRecoveryCode.recover outerRecovery
    (snd (CCS.OuterRecoveryCode.packetize outerRecovery (stateEncodedBases st)))
stateRecoveredEmissionShape st
  rewrite statePacketizedEmissionShape st = refl

stateEmitLengthRecoveryInputCoherent :
  ∀ {n} (st : BrainState n) →
  fst (stateEmittedBases st) ≡ n
stateEmitLengthRecoveryInputCoherent st =
  StateLaws.stateEmitOutputLengthExact st

record BrainCodecAdmissibilityBridgeSurface : Set₂ where
  field
    stateLaws : BrainStateCrossoverLawSurface
    dnaLaws : CrossoverAttachmentLawSurface

    encoded : ∀ {n} → BrainState n → Vec Base n
    emitted : ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
    packetized : ∀ {n} → BrainState n → Σ Nat (λ k → Vec Nat k)
    recovered : ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
    recoveryBoundary : Nat

brainCodecAdmissibilityBridgeSurface :
  BrainCodecAdmissibilityBridgeSurface
brainCodecAdmissibilityBridgeSurface = record
  { stateLaws = brainStateCrossoverLawSurface
  ; dnaLaws = crossoverAttachmentLawSurface
  ; encoded = stateEncodedBases
  ; emitted = stateEmittedBases
  ; packetized = statePacketizedEmission
  ; recovered = stateRecoveredEmission
  ; recoveryBoundary = stateRecoveryBoundary
  }
