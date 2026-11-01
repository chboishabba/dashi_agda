module Ontology.DNA.SynthesisSequencingRealismSemantics where

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

------------------------------------------------------------------------
-- Bounded semantics surface over the localized synthesis/sequencing realism
-- stack.
--
-- This remains theorem-thin and non-claiming. It does not add calibration,
-- empirical validity, or wet-lab realism. It only packages a sharper
-- semantics-facing profile over the current risk/read-write/checksum/recovery
-- owners and their already-landed depth alignment.

record SynthesisSequencingRealismSemanticProfile : Set where
  constructor synthesisSequencingRealismSemanticProfile
  field
    emittedWidth : Nat
    emittedPayload : Σ Nat (λ m → Vec Base m)
    substitutionLevel : SSRS.RiskLevel
    indelLevel : SSRS.RiskLevel
    dropoutLevel : SSRS.RiskLevel
    recoveryBoundary : Nat
    checksumPair : Σ Nat (λ _ → Nat)
    nextStepAdmissibility : Bool

realismSemanticProfile :
  ∀ {n} → Vec Base n → SynthesisSequencingRealismSemanticProfile
realismSemanticProfile xs =
  synthesisSequencingRealismSemanticProfile
    n
    (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs)
    (SSRD.SynthesisSequencingRealismDepthProfile.substitutionLevel
      (SSRD.realismDepthProfile xs))
    (SSRD.SynthesisSequencingRealismDepthProfile.indelLevel
      (SSRD.realismDepthProfile xs))
    (SSRD.SynthesisSequencingRealismDepthProfile.dropoutLevel
      (SSRD.realismDepthProfile xs))
    (SSRD.SynthesisSequencingRealismDepthProfile.recoveryBoundary
      (SSRD.realismDepthProfile xs))
    (SES.StreamingEncoderSurface.checksumSurface
      SES.streamingEncoderSurface
      (SES.stateOf xs))
    (SES.stepAdmissible (SES.stateOf xs) defaultProbe)
  where
  n = fst (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs)
  defaultProbe = Ontology.DNA.Supervoxel4Adic.A

record SynthesisSequencingRealismSemanticsSurface : Set₁ where
  field
    riskSurface : SSRS.SynthesisSequencingRiskSurface
    realismSurface : SSRL.SynthesisSequencingRealismSurface
    depthSurface : SSRD.SynthesisSequencingRealismDepthSurface
    channelSurface : CCS.IntegratedChannelSurface
    checksumSurface : CSCL.CrossoverSemanticChecksumLawSurface

    semanticProfile :
      ∀ {n} → Vec Base n → SynthesisSequencingRealismSemanticProfile

    semanticWidthExact :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismSemanticProfile.emittedWidth
        (semanticProfile xs)
      ≡ n

    semanticPayloadCanonical :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismSemanticProfile.emittedPayload
        (semanticProfile xs)
      ≡
      CCS.IntegratedChannelSurface.emit channelSurface xs

    semanticRiskRecoveryBoundaryStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismSemanticProfile.recoveryBoundary
        (semanticProfile xs)
      ≡
      SSRS.SynthesisSequencingRiskProfile.recoveryBoundary
        (SSRS.SynthesisSequencingRiskSurface.profile riskSurface)

    semanticDepthRecoveryBoundaryStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismSemanticProfile.recoveryBoundary
        (semanticProfile xs)
      ≡
      SSRD.SynthesisSequencingRealismDepthProfile.recoveryBoundary
        (SSRD.SynthesisSequencingRealismDepthSurface.depthProfile
          depthSurface xs)

    semanticChecksumPairStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismSemanticProfile.checksumPair
        (semanticProfile xs)
      ≡
      SES.StreamingEncoderSurface.checksumSurface
        SES.streamingEncoderSurface
        (SES.stateOf xs)

    semanticChecksumMatchesDepth :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismSemanticProfile.checksumPair
        (semanticProfile xs)
      ≡
      ( SSRD.SynthesisSequencingRealismDepthProfile.thermoChecksum
          (SSRD.SynthesisSequencingRealismDepthSurface.depthProfile
            depthSurface xs)
      , SSRD.SynthesisSequencingRealismDepthProfile.hamiltonianChecksum
          (SSRD.SynthesisSequencingRealismDepthSurface.depthProfile
            depthSurface xs)
      )

    semanticNextStepAdmissibilityStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismSemanticProfile.nextStepAdmissibility
        (semanticProfile xs)
      ≡
      SES.stepAdmissible (SES.stateOf xs) Ontology.DNA.Supervoxel4Adic.A

semanticWidthExactWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismSemanticProfile.emittedWidth
    (realismSemanticProfile xs)
  ≡ n
semanticWidthExactWitness xs = refl

semanticPayloadCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismSemanticProfile.emittedPayload
    (realismSemanticProfile xs)
  ≡
  CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs
semanticPayloadCanonicalWitness xs = refl

semanticRiskRecoveryBoundaryStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismSemanticProfile.recoveryBoundary
    (realismSemanticProfile xs)
  ≡
  SSRS.SynthesisSequencingRiskProfile.recoveryBoundary
    (SSRS.SynthesisSequencingRiskSurface.profile
      SSRS.synthesisSequencingRiskSurface)
semanticRiskRecoveryBoundaryStableWitness xs = refl

semanticDepthRecoveryBoundaryStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismSemanticProfile.recoveryBoundary
    (realismSemanticProfile xs)
  ≡
  SSRD.SynthesisSequencingRealismDepthProfile.recoveryBoundary
    (SSRD.realismDepthProfile xs)
semanticDepthRecoveryBoundaryStableWitness xs = refl

semanticChecksumPairStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismSemanticProfile.checksumPair
    (realismSemanticProfile xs)
  ≡
  SES.StreamingEncoderSurface.checksumSurface
    SES.streamingEncoderSurface
    (SES.stateOf xs)
semanticChecksumPairStableWitness xs = refl

semanticChecksumMatchesDepthWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismSemanticProfile.checksumPair
    (realismSemanticProfile xs)
  ≡
  ( SSRD.SynthesisSequencingRealismDepthProfile.thermoChecksum
      (SSRD.realismDepthProfile xs)
  , SSRD.SynthesisSequencingRealismDepthProfile.hamiltonianChecksum
      (SSRD.realismDepthProfile xs)
  )
semanticChecksumMatchesDepthWitness xs = refl

semanticNextStepAdmissibilityStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismSemanticProfile.nextStepAdmissibility
    (realismSemanticProfile xs)
  ≡
  SES.stepAdmissible (SES.stateOf xs) Ontology.DNA.Supervoxel4Adic.A
semanticNextStepAdmissibilityStableWitness xs = refl

synthesisSequencingRealismSemanticsSurface :
  SynthesisSequencingRealismSemanticsSurface
synthesisSequencingRealismSemanticsSurface = record
  { riskSurface = SSRS.synthesisSequencingRiskSurface
  ; realismSurface = SSRL.synthesisSequencingRealismSurface
  ; depthSurface = SSRD.synthesisSequencingRealismDepthSurface
  ; channelSurface = CCS.integratedChannelSurface
  ; checksumSurface = CSCL.crossoverSemanticChecksumLawSurface
  ; semanticProfile = realismSemanticProfile
  ; semanticWidthExact = semanticWidthExactWitness
  ; semanticPayloadCanonical = semanticPayloadCanonicalWitness
  ; semanticRiskRecoveryBoundaryStable =
      semanticRiskRecoveryBoundaryStableWitness
  ; semanticDepthRecoveryBoundaryStable =
      semanticDepthRecoveryBoundaryStableWitness
  ; semanticChecksumPairStable = semanticChecksumPairStableWitness
  ; semanticChecksumMatchesDepth = semanticChecksumMatchesDepthWitness
  ; semanticNextStepAdmissibilityStable =
      semanticNextStepAdmissibilityStableWitness
  }
