module Ontology.DNA.SynthesisSequencingIntegratedRealismLaws where

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
import Ontology.DNA.SynthesisSequencingIntegratedRealism as SSIR

------------------------------------------------------------------------
-- Bounded downstream law surface over the localized integrated realism
-- layer.
--
-- This remains theorem-thin and non-claiming. It does not add calibration,
-- empirical validity, or wet-lab realism. It only packages exact agreement
-- between the current integrated realism profile and the already-landed
-- semantics, consumer-law, channel, and checksum layers.

record SynthesisSequencingIntegratedRealismLawProfile : Set where
  constructor synthesisSequencingIntegratedRealismLawProfile
  field
    emittedWidth : Nat
    emittedPayload : Σ Nat (λ m → Vec Base m)
    recoveryBoundary : Nat
    checksumPair : Σ Nat (λ _ → Nat)
    emittedAdmissibility : Bool

integratedLawProfile :
  ∀ {n} → Vec Base n → SynthesisSequencingIntegratedRealismLawProfile
integratedLawProfile xs =
  synthesisSequencingIntegratedRealismLawProfile
    (SSIR.SynthesisSequencingIntegratedRealismProfile.emittedWidth
      (SSIR.integratedRealismProfile xs))
    (SSIR.SynthesisSequencingIntegratedRealismProfile.emittedPayload
      (SSIR.integratedRealismProfile xs))
    (SSIR.SynthesisSequencingIntegratedRealismProfile.recoveryBoundary
      (SSIR.integratedRealismProfile xs))
    (SSIR.SynthesisSequencingIntegratedRealismProfile.checksumPair
      (SSIR.integratedRealismProfile xs))
    (SSIR.SynthesisSequencingIntegratedRealismProfile.emittedAdmissibility
      (SSIR.integratedRealismProfile xs))

record SynthesisSequencingIntegratedRealismLawSurface : Set₁ where
  field
    semanticsSurface : SSRSem.SynthesisSequencingRealismSemanticsSurface
    consumerLawSurface : SSCL.SynthesisSequencingConsumerLawSurface
    integratedSurface : SSIR.SynthesisSequencingIntegratedRealismSurface
    channelSurface : CCS.IntegratedChannelSurface
    checksumSurface : CSCL.CrossoverSemanticChecksumLawSurface

    lawProfile :
      ∀ {n} → Vec Base n → SynthesisSequencingIntegratedRealismLawProfile

    lawWidthExact :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismLawProfile.emittedWidth
        (lawProfile xs)
      ≡ n

    lawPayloadMatchesIntegrated :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismLawProfile.emittedPayload
        (lawProfile xs)
      ≡
      SSIR.SynthesisSequencingIntegratedRealismProfile.emittedPayload
        (SSIR.SynthesisSequencingIntegratedRealismSurface.integratedProfile
          integratedSurface xs)

    lawPayloadMatchesConsumer :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismLawProfile.emittedPayload
        (lawProfile xs)
      ≡
      SSCL.SynthesisSequencingConsumerLawProfile.emittedPayload
        (SSCL.SynthesisSequencingConsumerLawSurface.lawProfile
          consumerLawSurface xs)

    lawPayloadCanonical :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismLawProfile.emittedPayload
        (lawProfile xs)
      ≡
      CCS.IntegratedChannelSurface.emit channelSurface xs

    lawRecoveryBoundaryStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismLawProfile.recoveryBoundary
        (lawProfile xs)
      ≡
      CCS.IntegratedChannelSurface.recoveryBoundary channelSurface

    lawChecksumStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismLawProfile.checksumPair
        (lawProfile xs)
      ≡
      SES.StreamingEncoderSurface.checksumSurface
        SES.streamingEncoderSurface
        (SES.stateOf xs)

    lawChecksumMatchesSemantics :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismLawProfile.checksumPair
        (lawProfile xs)
      ≡
      SSRSem.SynthesisSequencingRealismSemanticProfile.checksumPair
        (SSRSem.SynthesisSequencingRealismSemanticsSurface.semanticProfile
          semanticsSurface xs)

    lawAdmissibilityStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingIntegratedRealismLawProfile.emittedAdmissibility
        (lawProfile xs)
      ≡
      SES.stepAdmissible (SES.stateOf xs) Ontology.DNA.Supervoxel4Adic.A

lawWidthExactWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismLawProfile.emittedWidth
    (integratedLawProfile xs)
  ≡ n
lawWidthExactWitness xs = refl

lawPayloadMatchesIntegratedWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismLawProfile.emittedPayload
    (integratedLawProfile xs)
  ≡
  SSIR.SynthesisSequencingIntegratedRealismProfile.emittedPayload
    (SSIR.integratedRealismProfile xs)
lawPayloadMatchesIntegratedWitness xs = refl

lawPayloadMatchesConsumerWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismLawProfile.emittedPayload
    (integratedLawProfile xs)
  ≡
  SSCL.SynthesisSequencingConsumerLawProfile.emittedPayload
    (SSCL.consumerLawProfile xs)
lawPayloadMatchesConsumerWitness xs = refl

lawPayloadCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismLawProfile.emittedPayload
    (integratedLawProfile xs)
  ≡
  CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs
lawPayloadCanonicalWitness xs = refl

lawRecoveryBoundaryStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismLawProfile.recoveryBoundary
    (integratedLawProfile xs)
  ≡
  CCS.IntegratedChannelSurface.recoveryBoundary CCS.integratedChannelSurface
lawRecoveryBoundaryStableWitness xs = refl

lawChecksumStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismLawProfile.checksumPair
    (integratedLawProfile xs)
  ≡
  SES.StreamingEncoderSurface.checksumSurface
    SES.streamingEncoderSurface
    (SES.stateOf xs)
lawChecksumStableWitness xs = refl

lawChecksumMatchesSemanticsWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismLawProfile.checksumPair
    (integratedLawProfile xs)
  ≡
  SSRSem.SynthesisSequencingRealismSemanticProfile.checksumPair
    (SSRSem.realismSemanticProfile xs)
lawChecksumMatchesSemanticsWitness xs = refl

lawAdmissibilityStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingIntegratedRealismLawProfile.emittedAdmissibility
    (integratedLawProfile xs)
  ≡
  SES.stepAdmissible (SES.stateOf xs) Ontology.DNA.Supervoxel4Adic.A
lawAdmissibilityStableWitness xs = refl

synthesisSequencingIntegratedRealismLawSurface :
  SynthesisSequencingIntegratedRealismLawSurface
synthesisSequencingIntegratedRealismLawSurface = record
  { semanticsSurface = SSRSem.synthesisSequencingRealismSemanticsSurface
  ; consumerLawSurface = SSCL.synthesisSequencingConsumerLawSurface
  ; integratedSurface = SSIR.synthesisSequencingIntegratedRealismSurface
  ; channelSurface = CCS.integratedChannelSurface
  ; checksumSurface = CSCL.crossoverSemanticChecksumLawSurface
  ; lawProfile = integratedLawProfile
  ; lawWidthExact = lawWidthExactWitness
  ; lawPayloadMatchesIntegrated = lawPayloadMatchesIntegratedWitness
  ; lawPayloadMatchesConsumer = lawPayloadMatchesConsumerWitness
  ; lawPayloadCanonical = lawPayloadCanonicalWitness
  ; lawRecoveryBoundaryStable = lawRecoveryBoundaryStableWitness
  ; lawChecksumStable = lawChecksumStableWitness
  ; lawChecksumMatchesSemantics = lawChecksumMatchesSemanticsWitness
  ; lawAdmissibilityStable = lawAdmissibilityStableWitness
  }
