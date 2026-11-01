module Ontology.BrainDNA.BrainChemistryCodecConsumer where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (fst; snd)
open import Data.Vec using ([])

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.BrainDNA.BrainCodecPayloadRecoveryBridge as Payload using
  (BrainCodecPayloadRecoveryBridgeSurface; brainCodecPayloadRecoveryBridgeSurface;
   BrainCodecPayloadRecoveryProfile; codecPayloadRecoveryProfileOf;
   payloadRecoveredCanonicalEmpty; payloadRecoveryBoundaryStable)
open import Ontology.BrainDNA.BrainStructuralConsumerSemantics as Structural using
  (BrainStructuralConsumerSemanticsSurface; brainStructuralConsumerSemanticsSurface;
   BrainStructuralConsumerSemanticProfile; brainStructuralConsumerSemanticProfile;
   brainStructuralConsumerSemanticInvariantBounded;
   brainStructuralConsumerSemanticOrderLineMajor;
   brainStructuralConsumerSemanticAdmissibilityMatchesExtraction;
   brainStructuralConsumerSemanticRecoveryBoundaryExact)
open import Ontology.DNA.CrossoverSemanticChecksumLaws as Checksum using
  (CrossoverSemanticChecksumLawSurface; crossoverSemanticChecksumLawSurface;
   emitThermoChecksumCanonicalWitness;
   emitHamiltonianChecksumCanonicalWitness;
   emitSemanticChecksumPairCanonicalWitness)
open import Ontology.DNA.SupervoxelChemistryLongWindowLaws as Chem using
  (SupervoxelChemistryLongWindowLawSurface; supervoxelChemistryLongWindowLawSurface)
open import Ontology.DNA.ChannelCodingSurface using (genericAdmissibilityFlag)
open import Ontology.DNA.EigenclassSurface using (ScanOrder)
open import Ontology.DNA.StreamingEncoderSurface as SES using
  (stateOf; EncoderState)

------------------------------------------------------------------------
-- Bounded codec/chemistry consumer surface for the local brain-DNA lane.
-- This is intentionally theorem-thin and non-claiming: it only composes
-- already-local payload recovery, structural consumer, semantic checksum,
-- and long-window chemistry surfaces into one exact consumer boundary.

record BrainChemistryCodecConsumerProfile : Set where
  constructor mkBrainChemistryCodecConsumerProfile
  field
    recoveryBoundary : Nat
    invariantDepth : Nat
    structuralOrder : ScanOrder
    emittedAdmissibility : Bool
    recoveredWidth : Nat
    thermoChecksum : Nat
    hamiltonianChecksum : Nat

brainChemistryCodecConsumerProfile :
  ∀ {n} → BrainState n → BrainChemistryCodecConsumerProfile
brainChemistryCodecConsumerProfile st =
  mkBrainChemistryCodecConsumerProfile
    (BrainCodecPayloadRecoveryProfile.recoveryBoundary
      (codecPayloadRecoveryProfileOf st))
    (BrainStructuralConsumerSemanticProfile.invariantDepth
      (brainStructuralConsumerSemanticProfile st))
    (BrainStructuralConsumerSemanticProfile.order
      (brainStructuralConsumerSemanticProfile st))
    (BrainStructuralConsumerSemanticProfile.emittedAdmissibility
      (brainStructuralConsumerSemanticProfile st))
    (BrainCodecPayloadRecoveryProfile.recoveredWidth
      (codecPayloadRecoveryProfileOf st))
    (SES.EncoderState.thermoState
      (SES.stateOf
        (Payload.BrainCodecPayloadRecoveryProfile.sourcePayload
          (codecPayloadRecoveryProfileOf st))))
    (SES.EncoderState.hamiltonianState
      (SES.stateOf
        (Payload.BrainCodecPayloadRecoveryProfile.sourcePayload
          (codecPayloadRecoveryProfileOf st))))

consumerRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) →
  BrainChemistryCodecConsumerProfile.recoveryBoundary
    (brainChemistryCodecConsumerProfile st)
    ≡
  3
consumerRecoveryBoundaryExact st = payloadRecoveryBoundaryStable st

consumerStructuralRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) →
  BrainChemistryCodecConsumerProfile.recoveryBoundary
    (brainChemistryCodecConsumerProfile st)
    ≡
  BrainStructuralConsumerSemanticProfile.recoveryBoundary
    (brainStructuralConsumerSemanticProfile st)
consumerStructuralRecoveryBoundaryExact st =
  brainStructuralConsumerSemanticRecoveryBoundaryExact st

consumerRecoveredWidthCanonical :
  ∀ {n} (st : BrainState n) →
  BrainChemistryCodecConsumerProfile.recoveredWidth
    (brainChemistryCodecConsumerProfile st)
    ≡
  0
consumerRecoveredWidthCanonical st = refl

consumerRecoveredPayloadCanonical :
  ∀ {n} (st : BrainState n) →
  BrainCodecPayloadRecoveryProfile.recoveredPayload
    (codecPayloadRecoveryProfileOf st)
    ≡
  []
consumerRecoveredPayloadCanonical st = refl

consumerEmittedAdmissibilityTrue :
  ∀ {n} (st : BrainState n) →
  BrainChemistryCodecConsumerProfile.emittedAdmissibility
    (brainChemistryCodecConsumerProfile st)
    ≡
  genericAdmissibilityFlag
    (Payload.BrainCodecPayloadRecoveryProfile.sourcePayload
      (codecPayloadRecoveryProfileOf st))
consumerEmittedAdmissibilityTrue st =
  brainStructuralConsumerSemanticAdmissibilityMatchesExtraction st

consumerThermoChecksumCanonical :
  ∀ {n} (st : BrainState n) →
  BrainChemistryCodecConsumerProfile.thermoChecksum
    (brainChemistryCodecConsumerProfile st)
    ≡
  SES.EncoderState.thermoState
    (SES.stateOf
      (Payload.BrainCodecPayloadRecoveryProfile.sourcePayload
        (codecPayloadRecoveryProfileOf st)))
consumerThermoChecksumCanonical st = refl

consumerHamiltonianChecksumCanonical :
  ∀ {n} (st : BrainState n) →
  BrainChemistryCodecConsumerProfile.hamiltonianChecksum
    (brainChemistryCodecConsumerProfile st)
    ≡
  SES.EncoderState.hamiltonianState
    (SES.stateOf
      (Payload.BrainCodecPayloadRecoveryProfile.sourcePayload
        (codecPayloadRecoveryProfileOf st)))
consumerHamiltonianChecksumCanonical st = refl

record BrainChemistryCodecConsumerSurface : Set₂ where
  field
    payloadBridge : BrainCodecPayloadRecoveryBridgeSurface
    structuralSemantics : BrainStructuralConsumerSemanticsSurface
    checksumLaws : CrossoverSemanticChecksumLawSurface
    chemistryLaws : SupervoxelChemistryLongWindowLawSurface
    consumerProfile : ∀ {n} → BrainState n → BrainChemistryCodecConsumerProfile

brainChemistryCodecConsumerSurface : BrainChemistryCodecConsumerSurface
brainChemistryCodecConsumerSurface = record
  { payloadBridge = brainCodecPayloadRecoveryBridgeSurface
  ; structuralSemantics = brainStructuralConsumerSemanticsSurface
  ; checksumLaws = crossoverSemanticChecksumLawSurface
  ; chemistryLaws = supervoxelChemistryLongWindowLawSurface
  ; consumerProfile = brainChemistryCodecConsumerProfile
  }
