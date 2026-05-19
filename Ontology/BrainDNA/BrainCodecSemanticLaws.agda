module Ontology.BrainDNA.BrainCodecSemanticLaws where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Sigma using (Σ; fst; snd; _,_)
open import Data.Vec using (Vec; [])

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.BrainDNA.BrainCodecAdmissibilityBridge using
  (stateEncodedBases; stateEmittedBases; stateRecoveredEmission)
open import Ontology.BrainDNA.BrainCodecDepthLaws as Depth using
  (BrainCodecDepthLawSurface; brainCodecDepthLawSurface;
   stateRecoveredEmissionConstant; stateRecoveryBoundaryExact)
open import Ontology.BrainDNA.BrainCodecSemanticDepth as Semantic using
  (BrainCodecSemanticDepthSurface; brainCodecSemanticDepthSurface;
   BrainCodecSemanticProfile; codecSemanticProfileOf;
   semanticEncodedWidthExact; semanticEmittedWidthExact;
   semanticEmissionPayloadPreserved; semanticEmissionAdmissibilityPreserved;
   semanticPacketizedWidthZero; semanticRecoveredWidthZero;
   semanticRecoveredCanonical; semanticRecoveredConstant;
   semanticRecoveryBoundaryExact)
open import Ontology.DNA.ChannelCodingSurface using (genericAdmissibilityFlag)
open import Ontology.DNA.Supervoxel4Adic using (Base)

------------------------------------------------------------------------
-- Narrow semantic-law surface for the local brain-DNA codec lane.
--
-- This stays theorem-thin and non-claiming. It does not add realistic
-- decoding or biological semantics. It only packages exact local laws over
-- the already-landed semantic-depth and codec-depth owners.

semanticWidthAgreement :
  ∀ {n} (st : BrainState n) →
  BrainCodecSemanticProfile.encodedWidth (codecSemanticProfileOf st)
    ≡
  BrainCodecSemanticProfile.emittedWidth (codecSemanticProfileOf st)
semanticWidthAgreement st
  rewrite semanticEncodedWidthExact st
        | semanticEmittedWidthExact st = refl

semanticEmissionSemanticExact :
  ∀ {n} (st : BrainState n) →
  stateEmittedBases st
    ≡
  ( BrainCodecSemanticProfile.encodedWidth (codecSemanticProfileOf st)
  , stateEncodedBases st
  )
semanticEmissionSemanticExact st
  rewrite semanticWidthAgreement st = semanticEmissionPayloadPreserved st

semanticEmissionAdmissibilityExact :
  ∀ {n} (st : BrainState n) →
  BrainCodecSemanticProfile.emittedAdmissibility (codecSemanticProfileOf st)
    ≡
  genericAdmissibilityFlag (snd (stateEmittedBases st))
semanticEmissionAdmissibilityExact st
  rewrite semanticEmissionSemanticExact st =
  semanticEmissionAdmissibilityPreserved st

semanticPacketizedRecoveredCollapsed :
  ∀ {n} (st : BrainState n) →
  BrainCodecSemanticProfile.packetizedWidth (codecSemanticProfileOf st)
    ≡
  BrainCodecSemanticProfile.recoveredWidth (codecSemanticProfileOf st)
semanticPacketizedRecoveredCollapsed st
  rewrite semanticPacketizedWidthZero st
        | semanticRecoveredWidthZero st = refl

semanticRecoveredSemanticCanonical :
  ∀ {n} (st : BrainState n) →
  stateRecoveredEmission st
    ≡
  ( BrainCodecSemanticProfile.recoveredWidth (codecSemanticProfileOf st)
  , []
  )
semanticRecoveredSemanticCanonical st = semanticRecoveredCanonical st

semanticRecoveredConstantSemantic :
  ∀ {n m} (st₁ : BrainState n) (st₂ : BrainState m) →
  stateRecoveredEmission st₁ ≡ stateRecoveredEmission st₂
semanticRecoveredConstantSemantic st₁ st₂ =
  semanticRecoveredConstant st₁ st₂

semanticRecoveryBoundaryStable :
  ∀ {n} (st : BrainState n) →
  BrainCodecSemanticProfile.recoveryBoundary (codecSemanticProfileOf st) ≡ 3
semanticRecoveryBoundaryStable st
  rewrite semanticRecoveryBoundaryExact st
        | stateRecoveryBoundaryExact = refl

record BrainCodecSemanticLawSurface : Set₂ where
  field
    semanticDepth : BrainCodecSemanticDepthSurface
    depthLaws : BrainCodecDepthLawSurface

    semanticProfile : ∀ {n} → BrainState n → BrainCodecSemanticProfile
    emittedSemantic : ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
    recoveredSemantic : ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
    recoveryBoundary : ∀ {n} → BrainState n → Nat

brainCodecSemanticLawSurface : BrainCodecSemanticLawSurface
brainCodecSemanticLawSurface = record
  { semanticDepth = brainCodecSemanticDepthSurface
  ; depthLaws = brainCodecDepthLawSurface
  ; semanticProfile = codecSemanticProfileOf
  ; emittedSemantic = stateEmittedBases
  ; recoveredSemantic = stateRecoveredEmission
  ; recoveryBoundary = λ st →
      BrainCodecSemanticProfile.recoveryBoundary (codecSemanticProfileOf st)
  }
