module Ontology.DNA.SynthesisSequencingRealismConsumer where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Vec using (Vec)

open import Ontology.DNA.Supervoxel4Adic using (Base)

import Ontology.DNA.ChannelCodingSurface as CCS
import Ontology.DNA.StreamingEncoderSurface as SES
import Ontology.DNA.CrossoverSemanticChecksumLaws as CSCL
import Ontology.DNA.SynthesisSequencingRiskSurface as SSRS
import Ontology.DNA.SynthesisSequencingRealismLaws as SSRL
import Ontology.DNA.SynthesisSequencingRealismDepth as SSRD
import Ontology.DNA.SynthesisSequencingRealismSemantics as SSRSem

------------------------------------------------------------------------
-- Bounded downstream consumer/semantic surface for the localized
-- synthesis/sequencing realism lane.
--
-- This remains theorem-thin and non-claiming. It does not add calibration,
-- empirical validity, or wet-lab realism. It only packages one more
-- downstream consumer profile over the already-landed risk/law/depth/
-- semantics alignment.

record SynthesisSequencingRealismConsumerProfile : Set where
  constructor synthesisSequencingRealismConsumerProfile
  field
    emittedWidth : Nat
    emittedPayload : Σ Nat (λ m → Vec Base m)
    riskLevel : SSRS.RiskLevel
    recoveryBoundary : Nat
    checksumPair : Σ Nat (λ _ → Nat)
    emittedAdmissibility : Bool

realismConsumerProfile :
  ∀ {n} → Vec Base n → SynthesisSequencingRealismConsumerProfile
realismConsumerProfile xs =
  synthesisSequencingRealismConsumerProfile
    (SSRSem.SynthesisSequencingRealismSemanticProfile.emittedWidth
      (SSRSem.realismSemanticProfile xs))
    (SSRSem.SynthesisSequencingRealismSemanticProfile.emittedPayload
      (SSRSem.realismSemanticProfile xs))
    (SSRSem.SynthesisSequencingRealismSemanticProfile.substitutionLevel
      (SSRSem.realismSemanticProfile xs))
    (SSRSem.SynthesisSequencingRealismSemanticProfile.recoveryBoundary
      (SSRSem.realismSemanticProfile xs))
    (SSRSem.SynthesisSequencingRealismSemanticProfile.checksumPair
      (SSRSem.realismSemanticProfile xs))
    (SSRSem.SynthesisSequencingRealismSemanticProfile.nextStepAdmissibility
      (SSRSem.realismSemanticProfile xs))

record SynthesisSequencingRealismConsumerSurface : Set₁ where
  field
    riskSurface : SSRS.SynthesisSequencingRiskSurface
    realismSurface : SSRL.SynthesisSequencingRealismSurface
    depthSurface : SSRD.SynthesisSequencingRealismDepthSurface
    semanticsSurface : SSRSem.SynthesisSequencingRealismSemanticsSurface
    channelSurface : CCS.IntegratedChannelSurface
    checksumSurface : CSCL.CrossoverSemanticChecksumLawSurface

    consumerProfile :
      ∀ {n} → Vec Base n → SynthesisSequencingRealismConsumerProfile

    consumerWidthExact :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismConsumerProfile.emittedWidth
        (consumerProfile xs)
      ≡ n

    consumerPayloadCanonical :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismConsumerProfile.emittedPayload
        (consumerProfile xs)
      ≡
      CCS.IntegratedChannelSurface.emit channelSurface xs

    consumerRiskStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismConsumerProfile.riskLevel
        (consumerProfile xs)
      ≡
      SSRS.SynthesisSequencingRiskProfile.substitutionLevel
        (SSRS.SynthesisSequencingRiskSurface.profile riskSurface)

    consumerRecoveryBoundaryStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismConsumerProfile.recoveryBoundary
        (consumerProfile xs)
      ≡
      CCS.IntegratedChannelSurface.recoveryBoundary channelSurface

    consumerChecksumStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismConsumerProfile.checksumPair
        (consumerProfile xs)
      ≡
      SES.StreamingEncoderSurface.checksumSurface
        SES.streamingEncoderSurface
        (SES.stateOf xs)

    consumerChecksumMatchesSemantics :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismConsumerProfile.checksumPair
        (consumerProfile xs)
      ≡
      SSRSem.SynthesisSequencingRealismSemanticProfile.checksumPair
        (SSRSem.SynthesisSequencingRealismSemanticsSurface.semanticProfile
          semanticsSurface xs)

    consumerAdmissibilityStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismConsumerProfile.emittedAdmissibility
        (consumerProfile xs)
      ≡
      SES.stepAdmissible (SES.stateOf xs) Ontology.DNA.Supervoxel4Adic.A

consumerWidthExactWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismConsumerProfile.emittedWidth
    (realismConsumerProfile xs)
  ≡ n
consumerWidthExactWitness xs = refl

consumerPayloadCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismConsumerProfile.emittedPayload
    (realismConsumerProfile xs)
  ≡
  CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs
consumerPayloadCanonicalWitness xs = refl

consumerRiskStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismConsumerProfile.riskLevel
    (realismConsumerProfile xs)
  ≡
  SSRS.SynthesisSequencingRiskProfile.substitutionLevel
    (SSRS.SynthesisSequencingRiskSurface.profile
      SSRS.synthesisSequencingRiskSurface)
consumerRiskStableWitness xs = refl

consumerRecoveryBoundaryStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismConsumerProfile.recoveryBoundary
    (realismConsumerProfile xs)
  ≡
  CCS.IntegratedChannelSurface.recoveryBoundary CCS.integratedChannelSurface
consumerRecoveryBoundaryStableWitness xs = refl

consumerChecksumStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismConsumerProfile.checksumPair
    (realismConsumerProfile xs)
  ≡
  SES.StreamingEncoderSurface.checksumSurface
    SES.streamingEncoderSurface
    (SES.stateOf xs)
consumerChecksumStableWitness xs = refl

consumerChecksumMatchesSemanticsWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismConsumerProfile.checksumPair
    (realismConsumerProfile xs)
  ≡
  SSRSem.SynthesisSequencingRealismSemanticProfile.checksumPair
    (SSRSem.realismSemanticProfile xs)
consumerChecksumMatchesSemanticsWitness xs = refl

consumerAdmissibilityStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismConsumerProfile.emittedAdmissibility
    (realismConsumerProfile xs)
  ≡
  SES.stepAdmissible (SES.stateOf xs) Ontology.DNA.Supervoxel4Adic.A
consumerAdmissibilityStableWitness xs = refl

synthesisSequencingRealismConsumerSurface :
  SynthesisSequencingRealismConsumerSurface
synthesisSequencingRealismConsumerSurface = record
  { riskSurface = SSRS.synthesisSequencingRiskSurface
  ; realismSurface = SSRL.synthesisSequencingRealismSurface
  ; depthSurface = SSRD.synthesisSequencingRealismDepthSurface
  ; semanticsSurface = SSRSem.synthesisSequencingRealismSemanticsSurface
  ; channelSurface = CCS.integratedChannelSurface
  ; checksumSurface = CSCL.crossoverSemanticChecksumLawSurface
  ; consumerProfile = realismConsumerProfile
  ; consumerWidthExact = consumerWidthExactWitness
  ; consumerPayloadCanonical = consumerPayloadCanonicalWitness
  ; consumerRiskStable = consumerRiskStableWitness
  ; consumerRecoveryBoundaryStable = consumerRecoveryBoundaryStableWitness
  ; consumerChecksumStable = consumerChecksumStableWitness
  ; consumerChecksumMatchesSemantics = consumerChecksumMatchesSemanticsWitness
  ; consumerAdmissibilityStable = consumerAdmissibilityStableWitness
  }
