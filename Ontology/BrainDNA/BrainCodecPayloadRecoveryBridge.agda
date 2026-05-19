module Ontology.BrainDNA.BrainCodecPayloadRecoveryBridge where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Sigma using (Σ; fst; snd; _,_)
open import Data.Vec using (Vec; [])

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.BrainDNA.BrainCodecAdmissibilityBridge as Bridge using
  (BrainCodecAdmissibilityBridgeSurface; brainCodecAdmissibilityBridgeSurface;
   stateEncodedBases; stateEmittedBases; stateRecoveredEmission;
   stateRecoveredEmissionShape; stateRecoveryBoundary; outerRecovery)
open import Ontology.BrainDNA.BrainCodecDepthLaws as Depth using
  (BrainCodecDepthLawSurface; brainCodecDepthLawSurface;
   stateRecoveryBoundaryExact)
open import Ontology.BrainDNA.BrainCodecSemanticDepth as Semantic using
  (BrainCodecSemanticDepthSurface; brainCodecSemanticDepthSurface;
   BrainCodecSemanticProfile; codecSemanticProfileOf)
open import Ontology.BrainDNA.BrainCodecSemanticLaws as Laws using
  (BrainCodecSemanticLawSurface; brainCodecSemanticLawSurface;
   semanticEmissionSemanticExact; semanticRecoveredSemanticCanonical;
   semanticRecoveredConstantSemantic; semanticRecoveryBoundaryStable)
open import Ontology.DNA.ChannelCodingSurface as CCS using
  (genericAdmissibilityFlag; OuterRecoveryCode)
open import Ontology.DNA.Supervoxel4Adic using (Base)

------------------------------------------------------------------------
-- Narrow payload-recovery/channel contract surface for the local brain-DNA
-- codec lane.
--
-- This stays theorem-thin and non-claiming. It does not claim realistic
-- decoding or wet-lab recovery. It only sharpens the typed contract between
-- source payload, emitted payload, recovered payload, and the current local
-- recovery/channel boundary.

record BrainCodecPayloadRecoveryProfile : Set where
  constructor codecPayloadRecoveryProfile
  field
    sourceWidth : Nat
    sourcePayload : Vec Base sourceWidth
    emittedWidth : Nat
    emittedPayload : Vec Base emittedWidth
    recoveredWidth : Nat
    recoveredPayload : Vec Base recoveredWidth
    recoveryBoundary : Nat

codecPayloadRecoveryProfileOf :
  ∀ {n} → BrainState n → BrainCodecPayloadRecoveryProfile
codecPayloadRecoveryProfileOf {n} st = codecPayloadRecoveryProfile
  n
  (stateEncodedBases st)
  (fst (stateEmittedBases st))
  (snd (stateEmittedBases st))
  (fst (stateRecoveredEmission st))
  (snd (stateRecoveredEmission st))
  stateRecoveryBoundary

payloadSourceExact :
  ∀ {n} (st : BrainState n) →
  BrainCodecPayloadRecoveryProfile.sourcePayload
    (codecPayloadRecoveryProfileOf st)
    ≡
  stateEncodedBases st
payloadSourceExact st = refl

payloadEmissionExact :
  ∀ {n} (st : BrainState n) →
  stateEmittedBases st
    ≡
  ( BrainCodecPayloadRecoveryProfile.emittedWidth
      (codecPayloadRecoveryProfileOf st)
  , BrainCodecPayloadRecoveryProfile.emittedPayload
      (codecPayloadRecoveryProfileOf st)
  )
payloadEmissionExact st = refl

payloadEmissionMatchesSource :
  ∀ {n} (st : BrainState n) →
  stateEmittedBases st
    ≡
  ( BrainCodecPayloadRecoveryProfile.sourceWidth
      (codecPayloadRecoveryProfileOf st)
  , BrainCodecPayloadRecoveryProfile.sourcePayload
      (codecPayloadRecoveryProfileOf st)
  )
payloadEmissionMatchesSource st = Laws.semanticEmissionSemanticExact st

payloadRecoveredCanonical :
  ∀ {n} (st : BrainState n) →
  stateRecoveredEmission st
    ≡
  ( BrainCodecPayloadRecoveryProfile.recoveredWidth
      (codecPayloadRecoveryProfileOf st)
  , BrainCodecPayloadRecoveryProfile.recoveredPayload
      (codecPayloadRecoveryProfileOf st)
  )
payloadRecoveredCanonical st = refl

payloadRecoveredCanonicalEmpty :
  ∀ {n} (st : BrainState n) →
  stateRecoveredEmission st ≡ (zero , [])
payloadRecoveredCanonicalEmpty st =
  Laws.semanticRecoveredSemanticCanonical st

payloadRecoveredFromChannelShape :
  ∀ {n} (st : BrainState n) →
  stateRecoveredEmission st
    ≡
  CCS.OuterRecoveryCode.recover outerRecovery
    (snd (CCS.OuterRecoveryCode.packetize outerRecovery (stateEncodedBases st)))
payloadRecoveredFromChannelShape st = stateRecoveredEmissionShape st

payloadRecoveredAdmissibleCanonical :
  ∀ {n} (st : BrainState n) →
  genericAdmissibilityFlag
    (BrainCodecPayloadRecoveryProfile.recoveredPayload
      (codecPayloadRecoveryProfileOf st))
    ≡
  true
payloadRecoveredAdmissibleCanonical st = refl

payloadRecoveredConstantAcrossStates :
  ∀ {n m} (st₁ : BrainState n) (st₂ : BrainState m) →
  stateRecoveredEmission st₁ ≡ stateRecoveredEmission st₂
payloadRecoveredConstantAcrossStates st₁ st₂ =
  Laws.semanticRecoveredConstantSemantic st₁ st₂

payloadRecoveryBoundaryStable :
  ∀ {n} (st : BrainState n) →
  BrainCodecPayloadRecoveryProfile.recoveryBoundary
    (codecPayloadRecoveryProfileOf st)
    ≡
  3
payloadRecoveryBoundaryStable st = Laws.semanticRecoveryBoundaryStable st

record BrainCodecPayloadRecoveryBridgeSurface : Set₂ where
  field
    admissibilityBridge : BrainCodecAdmissibilityBridgeSurface
    depthLaws : BrainCodecDepthLawSurface
    semanticDepth : BrainCodecSemanticDepthSurface
    semanticLaws : BrainCodecSemanticLawSurface

    payloadProfile :
      ∀ {n} → BrainState n → BrainCodecPayloadRecoveryProfile
    source :
      ∀ {n} → BrainState n → Vec Base n
    emitted :
      ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
    recovered :
      ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
    recoveryBoundary :
      ∀ {n} → BrainState n → Nat

brainCodecPayloadRecoveryBridgeSurface :
  BrainCodecPayloadRecoveryBridgeSurface
brainCodecPayloadRecoveryBridgeSurface = record
  { admissibilityBridge = brainCodecAdmissibilityBridgeSurface
  ; depthLaws = brainCodecDepthLawSurface
  ; semanticDepth = brainCodecSemanticDepthSurface
  ; semanticLaws = brainCodecSemanticLawSurface
  ; payloadProfile = codecPayloadRecoveryProfileOf
  ; source = stateEncodedBases
  ; emitted = stateEmittedBases
  ; recovered = stateRecoveredEmission
  ; recoveryBoundary = λ st →
      BrainCodecPayloadRecoveryProfile.recoveryBoundary
        (codecPayloadRecoveryProfileOf st)
  }
