module Ontology.BrainDNA.BrainCodecSemanticDepth where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Sigma using (Σ; fst; snd; _,_)
open import Data.Vec using (Vec; [])

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.BrainDNA.BrainCodecAdmissibilityBridge as Bridge using
  (BrainCodecAdmissibilityBridgeSurface; brainCodecAdmissibilityBridgeSurface;
   stateEncodedBases; stateEmittedBases; statePacketizedEmission;
   stateRecoveredEmission; stateRecoveryBoundary)
open import Ontology.BrainDNA.BrainCodecDepthLaws as Depth using
  (BrainCodecDepthLawSurface; brainCodecDepthLawSurface;
   stateEmitExact; statePacketizedEmissionCanonical;
   stateRecoveredEmissionCanonical; stateRecoveredEmissionConstant;
   stateRecoveredPacketizeRecoverStable; stateRecoveryBoundaryExact)
open import Ontology.BrainDNA.BrainStateCrossoverLaws as StateLaw using
  (BrainStateCrossoverLawSurface; brainStateCrossoverLawSurface;
   stateEmitOutputGenericAdmissibility; stateEmitOutputLengthExact)
open import Ontology.DNA.ChannelCodingSurface using (genericAdmissibilityFlag)
open import Ontology.DNA.Supervoxel4Adic using (Base)

------------------------------------------------------------------------
-- Narrow semantic-depth surface for the local brain-DNA codec lane.
--
-- This remains theorem-thin and non-claiming. It does not model realistic
-- decoding or biological semantics. It only packages the exact local stage
-- semantics already witnessed by the current emit/packetize/recover owners.

record BrainCodecSemanticProfile : Set where
  constructor codecSemanticProfile
  field
    encodedWidth : Nat
    emittedWidth : Nat
    emittedAdmissibility : Bool
    packetizedWidth : Nat
    recoveredWidth : Nat
    recoveryBoundary : Nat

codecSemanticProfileOf : ∀ {n} → BrainState n → BrainCodecSemanticProfile
codecSemanticProfileOf st = codecSemanticProfile
  n
  (fst (stateEmittedBases st))
  (genericAdmissibilityFlag (snd (stateEmittedBases st)))
  (fst (statePacketizedEmission st))
  (fst (stateRecoveredEmission st))
  stateRecoveryBoundary
  where
  n = fst (stateEmittedBases st)

semanticEncodedWidthExact :
  ∀ {n} (st : BrainState n) →
  BrainCodecSemanticProfile.encodedWidth (codecSemanticProfileOf st) ≡ n
semanticEncodedWidthExact st = stateEmitOutputLengthExact st

semanticEmittedWidthExact :
  ∀ {n} (st : BrainState n) →
  BrainCodecSemanticProfile.emittedWidth (codecSemanticProfileOf st) ≡ n
semanticEmittedWidthExact st = stateEmitOutputLengthExact st

semanticEmissionPayloadPreserved :
  ∀ {n} (st : BrainState n) →
  stateEmittedBases st ≡
  ( BrainCodecSemanticProfile.emittedWidth (codecSemanticProfileOf st)
  , stateEncodedBases st
  )
semanticEmissionPayloadPreserved st = stateEmitExact st

semanticEmissionAdmissibilityPreserved :
  ∀ {n} (st : BrainState n) →
  BrainCodecSemanticProfile.emittedAdmissibility (codecSemanticProfileOf st)
    ≡
  genericAdmissibilityFlag (stateEncodedBases st)
semanticEmissionAdmissibilityPreserved st =
  stateEmitOutputGenericAdmissibility st

semanticPacketizedCanonical :
  ∀ {n} (st : BrainState n) →
  statePacketizedEmission st ≡
  (BrainCodecSemanticProfile.packetizedWidth (codecSemanticProfileOf st) , [])
semanticPacketizedCanonical st = statePacketizedEmissionCanonical st

semanticRecoveredCanonical :
  ∀ {n} (st : BrainState n) →
  stateRecoveredEmission st ≡
  (BrainCodecSemanticProfile.recoveredWidth (codecSemanticProfileOf st) , [])
semanticRecoveredCanonical st = stateRecoveredEmissionCanonical st

semanticPacketizedWidthZero :
  ∀ {n} (st : BrainState n) →
  BrainCodecSemanticProfile.packetizedWidth (codecSemanticProfileOf st) ≡ zero
semanticPacketizedWidthZero st = refl

semanticRecoveredWidthZero :
  ∀ {n} (st : BrainState n) →
  BrainCodecSemanticProfile.recoveredWidth (codecSemanticProfileOf st) ≡ zero
semanticRecoveredWidthZero st = refl

semanticRecoveredConstant :
  ∀ {n m} (st₁ : BrainState n) (st₂ : BrainState m) →
  stateRecoveredEmission st₁ ≡ stateRecoveredEmission st₂
semanticRecoveredConstant st₁ st₂ =
  stateRecoveredEmissionConstant st₁ st₂

semanticRecoveryStability :
  ∀ {n} (st : BrainState n) →
  stateRecoveredEmission st ≡ stateRecoveredEmission st
semanticRecoveryStability st rewrite stateRecoveredPacketizeRecoverStable st = refl

semanticRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) →
  BrainCodecSemanticProfile.recoveryBoundary (codecSemanticProfileOf st)
    ≡
  stateRecoveryBoundary
semanticRecoveryBoundaryExact st = refl

record BrainCodecSemanticDepthSurface : Set₂ where
  field
    admissibilityBridge : BrainCodecAdmissibilityBridgeSurface
    depthLaws : BrainCodecDepthLawSurface
    stateLaws : BrainStateCrossoverLawSurface

    semanticProfile : ∀ {n} → BrainState n → BrainCodecSemanticProfile
    emittedSemantic :
      ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
    recoveredSemantic :
      ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)

brainCodecSemanticDepthSurface : BrainCodecSemanticDepthSurface
brainCodecSemanticDepthSurface = record
  { admissibilityBridge = brainCodecAdmissibilityBridgeSurface
  ; depthLaws = brainCodecDepthLawSurface
  ; stateLaws = brainStateCrossoverLawSurface
  ; semanticProfile = codecSemanticProfileOf
  ; emittedSemantic = stateEmittedBases
  ; recoveredSemantic = stateRecoveredEmission
  }
