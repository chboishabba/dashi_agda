module Ontology.DNA.SynthesisSequencingConsumerLaws where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Vec using (Vec)

open import Ontology.DNA.Supervoxel4Adic using (Base)

import Ontology.DNA.ChannelCodingSurface as CCS
import Ontology.DNA.StreamingEncoderSurface as SES
import Ontology.DNA.CrossoverSemanticChecksumLaws as CSCL
import Ontology.DNA.SynthesisSequencingRealismLaws as SSRL
import Ontology.DNA.SynthesisSequencingRealismDepth as SSRD
import Ontology.DNA.SynthesisSequencingRealismSemantics as SSRSem
import Ontology.DNA.SynthesisSequencingRealismConsumer as SSRC

------------------------------------------------------------------------
-- Bounded downstream law surface over the localized synthesis/sequencing
-- consumer semantics layer.
--
-- This remains theorem-thin and non-claiming. It does not add calibration,
-- empirical validity, or wet-lab realism. It only packages exact agreement
-- between the current downstream consumer profile and the already-landed
-- realism, depth, and semantics layers.

record SynthesisSequencingConsumerLawProfile : Set where
  constructor synthesisSequencingConsumerLawProfile
  field
    emittedWidth : Nat
    emittedPayload : Σ Nat (λ m → Vec Base m)
    recoveryBoundary : Nat
    checksumPair : Σ Nat (λ _ → Nat)
    emittedAdmissibility : Bool

consumerLawProfile :
  ∀ {n} → Vec Base n → SynthesisSequencingConsumerLawProfile
consumerLawProfile xs =
  synthesisSequencingConsumerLawProfile
    (SSRC.SynthesisSequencingRealismConsumerProfile.emittedWidth
      (SSRC.realismConsumerProfile xs))
    (SSRC.SynthesisSequencingRealismConsumerProfile.emittedPayload
      (SSRC.realismConsumerProfile xs))
    (SSRC.SynthesisSequencingRealismConsumerProfile.recoveryBoundary
      (SSRC.realismConsumerProfile xs))
    (SSRC.SynthesisSequencingRealismConsumerProfile.checksumPair
      (SSRC.realismConsumerProfile xs))
    (SSRC.SynthesisSequencingRealismConsumerProfile.emittedAdmissibility
      (SSRC.realismConsumerProfile xs))

record SynthesisSequencingConsumerLawSurface : Set₁ where
  field
    realismSurface : SSRL.SynthesisSequencingRealismSurface
    depthSurface : SSRD.SynthesisSequencingRealismDepthSurface
    semanticsSurface : SSRSem.SynthesisSequencingRealismSemanticsSurface
    consumerSurface : SSRC.SynthesisSequencingRealismConsumerSurface
    channelSurface : CCS.IntegratedChannelSurface
    checksumSurface : CSCL.CrossoverSemanticChecksumLawSurface

    lawProfile :
      ∀ {n} → Vec Base n → SynthesisSequencingConsumerLawProfile

    consumerLawWidthExact :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingConsumerLawProfile.emittedWidth
        (lawProfile xs)
      ≡ n

    consumerLawPayloadMatchesConsumer :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingConsumerLawProfile.emittedPayload
        (lawProfile xs)
      ≡
      SSRC.SynthesisSequencingRealismConsumerProfile.emittedPayload
        (SSRC.SynthesisSequencingRealismConsumerSurface.consumerProfile
          consumerSurface xs)

    consumerLawPayloadCanonical :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingConsumerLawProfile.emittedPayload
        (lawProfile xs)
      ≡
      CCS.IntegratedChannelSurface.emit channelSurface xs

    consumerLawRecoveryBoundaryStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingConsumerLawProfile.recoveryBoundary
        (lawProfile xs)
      ≡
      SSRSem.SynthesisSequencingRealismSemanticProfile.recoveryBoundary
        (SSRSem.SynthesisSequencingRealismSemanticsSurface.semanticProfile
          semanticsSurface xs)

    consumerLawRecoveryBoundaryCanonical :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingConsumerLawProfile.recoveryBoundary
        (lawProfile xs)
      ≡
      CCS.IntegratedChannelSurface.recoveryBoundary channelSurface

    consumerLawChecksumStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingConsumerLawProfile.checksumPair
        (lawProfile xs)
      ≡
      SES.StreamingEncoderSurface.checksumSurface
        SES.streamingEncoderSurface
        (SES.stateOf xs)

    consumerLawChecksumMatchesSemantics :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingConsumerLawProfile.checksumPair
        (lawProfile xs)
      ≡
      SSRSem.SynthesisSequencingRealismSemanticProfile.checksumPair
        (SSRSem.SynthesisSequencingRealismSemanticsSurface.semanticProfile
          semanticsSurface xs)

    consumerLawAdmissibilityStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingConsumerLawProfile.emittedAdmissibility
        (lawProfile xs)
      ≡
      SES.stepAdmissible (SES.stateOf xs) Ontology.DNA.Supervoxel4Adic.A

consumerLawWidthExactWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingConsumerLawProfile.emittedWidth
    (consumerLawProfile xs)
  ≡ n
consumerLawWidthExactWitness xs = refl

consumerLawPayloadMatchesConsumerWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingConsumerLawProfile.emittedPayload
    (consumerLawProfile xs)
  ≡
  SSRC.SynthesisSequencingRealismConsumerProfile.emittedPayload
    (SSRC.realismConsumerProfile xs)
consumerLawPayloadMatchesConsumerWitness xs = refl

consumerLawPayloadCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingConsumerLawProfile.emittedPayload
    (consumerLawProfile xs)
  ≡
  CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs
consumerLawPayloadCanonicalWitness xs = refl

consumerLawRecoveryBoundaryStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingConsumerLawProfile.recoveryBoundary
    (consumerLawProfile xs)
  ≡
  SSRSem.SynthesisSequencingRealismSemanticProfile.recoveryBoundary
    (SSRSem.realismSemanticProfile xs)
consumerLawRecoveryBoundaryStableWitness xs = refl

consumerLawRecoveryBoundaryCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingConsumerLawProfile.recoveryBoundary
    (consumerLawProfile xs)
  ≡
  CCS.IntegratedChannelSurface.recoveryBoundary CCS.integratedChannelSurface
consumerLawRecoveryBoundaryCanonicalWitness xs = refl

consumerLawChecksumStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingConsumerLawProfile.checksumPair
    (consumerLawProfile xs)
  ≡
  SES.StreamingEncoderSurface.checksumSurface
    SES.streamingEncoderSurface
    (SES.stateOf xs)
consumerLawChecksumStableWitness xs = refl

consumerLawChecksumMatchesSemanticsWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingConsumerLawProfile.checksumPair
    (consumerLawProfile xs)
  ≡
  SSRSem.SynthesisSequencingRealismSemanticProfile.checksumPair
    (SSRSem.realismSemanticProfile xs)
consumerLawChecksumMatchesSemanticsWitness xs = refl

consumerLawAdmissibilityStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingConsumerLawProfile.emittedAdmissibility
    (consumerLawProfile xs)
  ≡
  SES.stepAdmissible (SES.stateOf xs) Ontology.DNA.Supervoxel4Adic.A
consumerLawAdmissibilityStableWitness xs = refl

synthesisSequencingConsumerLawSurface :
  SynthesisSequencingConsumerLawSurface
synthesisSequencingConsumerLawSurface = record
  { realismSurface = SSRL.synthesisSequencingRealismSurface
  ; depthSurface = SSRD.synthesisSequencingRealismDepthSurface
  ; semanticsSurface = SSRSem.synthesisSequencingRealismSemanticsSurface
  ; consumerSurface = SSRC.synthesisSequencingRealismConsumerSurface
  ; channelSurface = CCS.integratedChannelSurface
  ; checksumSurface = CSCL.crossoverSemanticChecksumLawSurface
  ; lawProfile = consumerLawProfile
  ; consumerLawWidthExact = consumerLawWidthExactWitness
  ; consumerLawPayloadMatchesConsumer = consumerLawPayloadMatchesConsumerWitness
  ; consumerLawPayloadCanonical = consumerLawPayloadCanonicalWitness
  ; consumerLawRecoveryBoundaryStable = consumerLawRecoveryBoundaryStableWitness
  ; consumerLawRecoveryBoundaryCanonical =
      consumerLawRecoveryBoundaryCanonicalWitness
  ; consumerLawChecksumStable = consumerLawChecksumStableWitness
  ; consumerLawChecksumMatchesSemantics =
      consumerLawChecksumMatchesSemanticsWitness
  ; consumerLawAdmissibilityStable = consumerLawAdmissibilityStableWitness
  }
