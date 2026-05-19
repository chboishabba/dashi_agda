module Ontology.BrainDNA.BrainCodecRecoverySemanticLaws where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Vec using (Vec; [])

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.BrainDNA.BrainCodecAdmissibilityBridge using
  (stateEmittedBases; stateRecoveredEmission)
open import Ontology.BrainDNA.BrainCodecPayloadRecoveryBridge as Payload using
  (BrainCodecPayloadRecoveryBridgeSurface; brainCodecPayloadRecoveryBridgeSurface;
   BrainCodecPayloadRecoveryProfile; codecPayloadRecoveryProfileOf;
   payloadSourceExact; payloadEmissionExact; payloadEmissionMatchesSource;
   payloadRecoveredCanonical; payloadRecoveredCanonicalEmpty;
   payloadRecoveredFromChannelShape; payloadRecoveredAdmissibleCanonical;
   payloadRecoveredConstantAcrossStates; payloadRecoveryBoundaryStable)
open import Ontology.BrainDNA.BrainCodecSemanticDepth as Semantic using
  (BrainCodecSemanticDepthSurface; brainCodecSemanticDepthSurface;
   BrainCodecSemanticProfile; codecSemanticProfileOf)
open import Ontology.BrainDNA.BrainCodecSemanticLaws as Laws using
  (BrainCodecSemanticLawSurface; brainCodecSemanticLawSurface;
   semanticWidthAgreement; semanticPacketizedRecoveredCollapsed;
   semanticRecoveryBoundaryStable)
open import Ontology.DNA.ChannelCodingSurface using (genericAdmissibilityFlag)
open import Ontology.DNA.Supervoxel4Adic using (Base)

------------------------------------------------------------------------
-- Narrow recovery/channel semantics surface for the local brain-DNA codec
-- lane.
--
-- This stays theorem-thin and non-claiming. It does not assert realistic
-- decoding or wet-lab validity. It only sharpens the current typed recovery
-- contract already witnessed by the semantic-depth and payload-recovery
-- owners.

recoverySourceEmissionWidthAgreement :
  ∀ {n} (st : BrainState n) →
  BrainCodecPayloadRecoveryProfile.sourceWidth (codecPayloadRecoveryProfileOf st)
    ≡
  BrainCodecPayloadRecoveryProfile.emittedWidth (codecPayloadRecoveryProfileOf st)
recoverySourceEmissionWidthAgreement st = semanticWidthAgreement st

recoveryEmissionPayloadStable :
  ∀ {n} (st : BrainState n) →
  stateEmittedBases st
    ≡
  ( BrainCodecPayloadRecoveryProfile.sourceWidth (codecPayloadRecoveryProfileOf st)
  , BrainCodecPayloadRecoveryProfile.sourcePayload (codecPayloadRecoveryProfileOf st)
  )
recoveryEmissionPayloadStable st = payloadEmissionMatchesSource st

recoveryRecoveredWidthCollapsed :
  ∀ {n} (st : BrainState n) →
  BrainCodecPayloadRecoveryProfile.recoveredWidth (codecPayloadRecoveryProfileOf st)
    ≡
  zero
recoveryRecoveredWidthCollapsed st = refl

recoveryRecoveredPayloadCanonical :
  ∀ {n} (st : BrainState n) →
  stateRecoveredEmission st
    ≡
  ( BrainCodecPayloadRecoveryProfile.recoveredWidth (codecPayloadRecoveryProfileOf st)
  , BrainCodecPayloadRecoveryProfile.recoveredPayload (codecPayloadRecoveryProfileOf st)
  )
recoveryRecoveredPayloadCanonical st = payloadRecoveredCanonical st

recoveryRecoveredPayloadEmpty :
  ∀ {n} (st : BrainState n) →
  BrainCodecPayloadRecoveryProfile.recoveredPayload (codecPayloadRecoveryProfileOf st)
    ≡
  []
recoveryRecoveredPayloadEmpty st = refl

recoveryRecoveredChannelShapeStable :
  ∀ {n} (st : BrainState n) →
  stateRecoveredEmission st ≡ stateRecoveredEmission st
recoveryRecoveredChannelShapeStable st rewrite payloadRecoveredFromChannelShape st = refl

recoveryRecoveredAdmissibilityStable :
  ∀ {n} (st : BrainState n) →
  genericAdmissibilityFlag
    (BrainCodecPayloadRecoveryProfile.recoveredPayload (codecPayloadRecoveryProfileOf st))
    ≡
  true
recoveryRecoveredAdmissibilityStable st = payloadRecoveredAdmissibleCanonical st

recoveryRecoveredConstantChannel :
  ∀ {n m} (st₁ : BrainState n) (st₂ : BrainState m) →
  stateRecoveredEmission st₁ ≡ stateRecoveredEmission st₂
recoveryRecoveredConstantChannel st₁ st₂ =
  payloadRecoveredConstantAcrossStates st₁ st₂

recoveryBoundarySemanticStable :
  ∀ {n} (st : BrainState n) →
  BrainCodecPayloadRecoveryProfile.recoveryBoundary (codecPayloadRecoveryProfileOf st)
    ≡
  3
recoveryBoundarySemanticStable st = payloadRecoveryBoundaryStable st

record BrainCodecRecoverySemanticLawSurface : Set₂ where
  field
    payloadBridge : BrainCodecPayloadRecoveryBridgeSurface
    semanticDepth : BrainCodecSemanticDepthSurface
    semanticLaws : BrainCodecSemanticLawSurface

    payloadProfile :
      ∀ {n} → BrainState n → BrainCodecPayloadRecoveryProfile
    emitted :
      ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
    recovered :
      ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
    recoveryBoundary :
      ∀ {n} → BrainState n → Nat

brainCodecRecoverySemanticLawSurface :
  BrainCodecRecoverySemanticLawSurface
brainCodecRecoverySemanticLawSurface = record
  { payloadBridge = brainCodecPayloadRecoveryBridgeSurface
  ; semanticDepth = brainCodecSemanticDepthSurface
  ; semanticLaws = brainCodecSemanticLawSurface
  ; payloadProfile = codecPayloadRecoveryProfileOf
  ; emitted = stateEmittedBases
  ; recovered = stateRecoveredEmission
  ; recoveryBoundary = λ st →
      BrainCodecPayloadRecoveryProfile.recoveryBoundary
        (codecPayloadRecoveryProfileOf st)
  }
