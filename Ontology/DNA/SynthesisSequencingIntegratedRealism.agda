module Ontology.DNA.SynthesisSequencingIntegratedRealism where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Vec using (Vec)

open import Ontology.DNA.Supervoxel4Adic using (Base)

import Ontology.DNA.ChannelCodingSurface as CCS
import Ontology.DNA.StreamingEncoderSurface as SES
import Ontology.DNA.CrossoverSemanticChecksumLaws as CSCL
import Ontology.DNA.SynthesisSequencingRealismSemantics as SSRSem
import Ontology.DNA.SynthesisSequencingConsumerLaws as SSCL

------------------------------------------------------------------------
-- Bounded downstream integration surface over the localized
-- synthesis/sequencing realism stack.
--
-- This remains theorem-thin and non-claiming. It does not add calibration,
-- empirical validity, or wet-lab realism. It only packages one sharper
-- downstream integration profile over the already-landed semantics and
-- consumer-law layers.

record SynthesisSequencingIntegratedRealismProfile : Set where
  constructor synthesisSequencingIntegratedRealismProfile
  field
    emittedWidth : Nat
    emittedPayload : Σ Nat (λ m → Vec Base m)
    recoveryBoundary : Nat
    checksumPair : Σ Nat (λ _ → Nat)
    emittedAdmissibility : Bool

integratedRealismProfile :
  ∀ {n} → Vec Base n → SynthesisSequencingIntegratedRealismProfile
integratedRealismProfile xs =
  synthesisSequencingIntegratedRealismProfile
    (SSCL.SynthesisSequencingConsumerLawProfile.emittedWidth
      (SSCL.consumerLawProfile xs))
    (SSCL.SynthesisSequencingConsumerLawProfile.emittedPayload
      (SSCL.consumerLawProfile xs))
    (SSCL.SynthesisSequencingConsumerLawProfile.recoveryBoundary
      (SSCL.consumerLawProfile xs))
    (SSCL.SynthesisSequencingConsumerLawProfile.checksumPair
      (SSCL.consumerLawProfile xs))
    (SSCL.SynthesisSequencingConsumerLawProfile.emittedAdmissibility
      (SSCL.consumerLawProfile xs))

record SynthesisSequencingIntegratedRealismSurface : Set₁ where
  field
    semanticsSurface : SSRSem.SynthesisSequencingRealismSemanticsSurface
    consumerLawSurface : SSCL.SynthesisSequencingConsumerLawSurface
    channelSurface : CCS.IntegratedChannelSurface
    checksumSurface : CSCL.CrossoverSemanticChecksumLawSurface

    integratedProfile :
      ∀ {n} → Vec Base n → SynthesisSequencingIntegratedRealismProfile

    integratedWidthExact :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismProfile.emittedWidth
        (integratedProfile xs)
      ≡ n

    integratedPayloadMatchesConsumer :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismProfile.emittedPayload
        (integratedProfile xs)
      ≡
      SSCL.SynthesisSequencingConsumerLawProfile.emittedPayload
        (SSCL.SynthesisSequencingConsumerLawSurface.lawProfile
          consumerLawSurface xs)

    integratedPayloadMatchesSemantics :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismProfile.emittedPayload
        (integratedProfile xs)
      ≡
      SSRSem.SynthesisSequencingRealismSemanticProfile.emittedPayload
        (SSRSem.SynthesisSequencingRealismSemanticsSurface.semanticProfile
          semanticsSurface xs)

    integratedPayloadCanonical :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismProfile.emittedPayload
        (integratedProfile xs)
      ≡
      CCS.IntegratedChannelSurface.emit channelSurface xs

    integratedRecoveryBoundaryStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismProfile.recoveryBoundary
        (integratedProfile xs)
      ≡
      CCS.IntegratedChannelSurface.recoveryBoundary channelSurface

    integratedChecksumStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismProfile.checksumPair
        (integratedProfile xs)
      ≡
      SES.StreamingEncoderSurface.checksumSurface
        SES.streamingEncoderSurface
        (SES.stateOf xs)

    integratedChecksumMatchesSemantics :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismProfile.checksumPair
        (integratedProfile xs)
      ≡
      SSRSem.SynthesisSequencingRealismSemanticProfile.checksumPair
        (SSRSem.SynthesisSequencingRealismSemanticsSurface.semanticProfile
          semanticsSurface xs)

    integratedAdmissibilityStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismProfile.emittedAdmissibility
        (integratedProfile xs)
      ≡
      SES.stepAdmissible (SES.stateOf xs) Ontology.DNA.Supervoxel4Adic.A

integratedWidthExactWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismProfile.emittedWidth
    (integratedRealismProfile xs)
  ≡ n
integratedWidthExactWitness xs = refl

integratedPayloadMatchesConsumerWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismProfile.emittedPayload
    (integratedRealismProfile xs)
  ≡
  SSCL.SynthesisSequencingConsumerLawProfile.emittedPayload
    (SSCL.consumerLawProfile xs)
integratedPayloadMatchesConsumerWitness xs = refl

integratedPayloadMatchesSemanticsWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismProfile.emittedPayload
    (integratedRealismProfile xs)
  ≡
  SSRSem.SynthesisSequencingRealismSemanticProfile.emittedPayload
    (SSRSem.realismSemanticProfile xs)
integratedPayloadMatchesSemanticsWitness xs = refl

integratedPayloadCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismProfile.emittedPayload
    (integratedRealismProfile xs)
  ≡
  CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs
integratedPayloadCanonicalWitness xs = refl

integratedRecoveryBoundaryStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismProfile.recoveryBoundary
    (integratedRealismProfile xs)
  ≡
  CCS.IntegratedChannelSurface.recoveryBoundary CCS.integratedChannelSurface
integratedRecoveryBoundaryStableWitness xs = refl

integratedChecksumStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismProfile.checksumPair
    (integratedRealismProfile xs)
  ≡
  SES.StreamingEncoderSurface.checksumSurface
    SES.streamingEncoderSurface
    (SES.stateOf xs)
integratedChecksumStableWitness xs = refl

integratedChecksumMatchesSemanticsWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismProfile.checksumPair
    (integratedRealismProfile xs)
  ≡
  SSRSem.SynthesisSequencingRealismSemanticProfile.checksumPair
    (SSRSem.realismSemanticProfile xs)
integratedChecksumMatchesSemanticsWitness xs = refl

integratedAdmissibilityStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismProfile.emittedAdmissibility
    (integratedRealismProfile xs)
  ≡
  SES.stepAdmissible (SES.stateOf xs) Ontology.DNA.Supervoxel4Adic.A
integratedAdmissibilityStableWitness xs = refl

synthesisSequencingIntegratedRealismSurface :
  SynthesisSequencingIntegratedRealismSurface
synthesisSequencingIntegratedRealismSurface = record
  { semanticsSurface = SSRSem.synthesisSequencingRealismSemanticsSurface
  ; consumerLawSurface = SSCL.synthesisSequencingConsumerLawSurface
  ; channelSurface = CCS.integratedChannelSurface
  ; checksumSurface = CSCL.crossoverSemanticChecksumLawSurface
  ; integratedProfile = integratedRealismProfile
  ; integratedWidthExact = integratedWidthExactWitness
  ; integratedPayloadMatchesConsumer = integratedPayloadMatchesConsumerWitness
  ; integratedPayloadMatchesSemantics = integratedPayloadMatchesSemanticsWitness
  ; integratedPayloadCanonical = integratedPayloadCanonicalWitness
  ; integratedRecoveryBoundaryStable = integratedRecoveryBoundaryStableWitness
  ; integratedChecksumStable = integratedChecksumStableWitness
  ; integratedChecksumMatchesSemantics =
      integratedChecksumMatchesSemanticsWitness
  ; integratedAdmissibilityStable = integratedAdmissibilityStableWitness
  }
