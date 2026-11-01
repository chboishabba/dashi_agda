module Ontology.DNA.SynthesisSequencingRealismDepth where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Data.Vec using (Vec)

open import Ontology.DNA.Supervoxel4Adic using (Base; A)

import Ontology.DNA.ChannelCodingSurface as CCS
import Ontology.DNA.StreamingEncoderSurface as SES
import Ontology.DNA.CrossoverSemanticChecksumLaws as CSCL
import Ontology.DNA.SynthesisSequencingRiskSurface as SSRS
import Ontology.DNA.SynthesisSequencingRealismLaws as SSRL

------------------------------------------------------------------------
-- Bounded depth/consumer surface over the localized synthesis/sequencing
-- realism owner.
--
-- This remains theorem-thin and non-claiming. It does not add empirical
-- calibration or wet-lab realism. It only packages one sharper alignment
-- object over the current risk, read/write, checksum, and recovery surfaces.

record SynthesisSequencingRealismDepthProfile : Set where
  constructor synthesisSequencingRealismDepthProfile
  field
    emittedWidth : Nat
    substitutionLevel : SSRS.RiskLevel
    indelLevel : SSRS.RiskLevel
    dropoutLevel : SSRS.RiskLevel
    recoveryBoundary : Nat
    thermoChecksum : Nat
    hamiltonianChecksum : Nat
    emittedAdmissibility : Bool

realismDepthProfile :
  ∀ {n} → Vec Base n → SynthesisSequencingRealismDepthProfile
realismDepthProfile xs =
  synthesisSequencingRealismDepthProfile
    n
    (SSRS.SynthesisSequencingRiskProfile.substitutionLevel
      (SSRS.SynthesisSequencingRiskSurface.profile
        SSRS.synthesisSequencingRiskSurface))
    (SSRS.SynthesisSequencingRiskProfile.indelLevel
      (SSRS.SynthesisSequencingRiskSurface.profile
        SSRS.synthesisSequencingRiskSurface))
    (SSRS.SynthesisSequencingRiskProfile.dropoutLevel
      (SSRS.SynthesisSequencingRiskSurface.profile
        SSRS.synthesisSequencingRiskSurface))
    (SSRS.SynthesisSequencingRiskProfile.recoveryBoundary
      (SSRS.SynthesisSequencingRiskSurface.profile
        SSRS.synthesisSequencingRiskSurface))
    (fst
      (SES.StreamingEncoderSurface.checksumSurface
        SES.streamingEncoderSurface
        (SES.stateOf xs)))
    (snd
      (SES.StreamingEncoderSurface.checksumSurface
        SES.streamingEncoderSurface
        (SES.stateOf xs)))
    (SES.stepAdmissible (SES.stateOf xs) A)
  where
  n = fst (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs)

record SynthesisSequencingRealismDepthSurface : Set₁ where
  field
    riskSurface : SSRS.SynthesisSequencingRiskSurface
    realismSurface : SSRL.SynthesisSequencingRealismSurface
    channelSurface : CCS.IntegratedChannelSurface
    checksumSurface : CSCL.CrossoverSemanticChecksumLawSurface

    depthProfile : ∀ {n} → Vec Base n → SynthesisSequencingRealismDepthProfile

    emittedWidthExact :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismDepthProfile.emittedWidth
        (depthProfile xs)
      ≡ n

    substitutionLevelStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismDepthProfile.substitutionLevel
        (depthProfile xs)
      ≡
      SSRS.classifyRiskLevel
        (CCS.PhysicalChannelModel.substitutionRisk
          (CCS.IntegratedChannelSurface.channel channelSurface))

    recoveryBoundaryStable :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismDepthProfile.recoveryBoundary
        (depthProfile xs)
      ≡
      CCS.IntegratedChannelSurface.recoveryBoundary channelSurface

    thermoChecksumExact :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismDepthProfile.thermoChecksum
        (depthProfile xs)
      ≡
      SES.EncoderState.thermoState (SES.stateOf xs)

    hamiltonianChecksumExact :
      ∀ {n} (xs : Vec Base n) →
      SynthesisSequencingRealismDepthProfile.hamiltonianChecksum
        (depthProfile xs)
      ≡
      SES.EncoderState.hamiltonianState (SES.stateOf xs)

    emittedChecksumPairStable :
      ∀ {n} (xs : Vec Base n) →
      SES.StreamingEncoderSurface.checksumSurface
        SES.streamingEncoderSurface
        (SES.stateOf xs)
      ≡
      ( SynthesisSequencingRealismDepthProfile.thermoChecksum
          (depthProfile xs)
      , SynthesisSequencingRealismDepthProfile.hamiltonianChecksum
          (depthProfile xs)
      )

    nextStepAdmissibilityStable :
      ∀ {n} (xs : Vec Base n) (b : Base) →
      SES.stepAdmissible
        (SES.stateOf
          (snd
            (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs)))
        b
      ≡
      SES.stepAdmissible (SES.stateOf xs) b

emittedWidthExactWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismDepthProfile.emittedWidth
    (realismDepthProfile xs)
  ≡ n
emittedWidthExactWitness xs = refl

substitutionLevelStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismDepthProfile.substitutionLevel
    (realismDepthProfile xs)
  ≡
  SSRS.classifyRiskLevel
    (CCS.PhysicalChannelModel.substitutionRisk
      (CCS.IntegratedChannelSurface.channel CCS.integratedChannelSurface))
substitutionLevelStableWitness xs = refl

recoveryBoundaryStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismDepthProfile.recoveryBoundary
    (realismDepthProfile xs)
  ≡
  CCS.IntegratedChannelSurface.recoveryBoundary CCS.integratedChannelSurface
recoveryBoundaryStableWitness xs =
  SSRL.SynthesisSequencingRealismSurface.writeReadRiskRecoveryBoundaryExact
    SSRL.synthesisSequencingRealismSurface

thermoChecksumExactWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismDepthProfile.thermoChecksum
    (realismDepthProfile xs)
  ≡
  SES.EncoderState.thermoState (SES.stateOf xs)
thermoChecksumExactWitness xs = refl

hamiltonianChecksumExactWitness :
  ∀ {n} (xs : Vec Base n) →
  SynthesisSequencingRealismDepthProfile.hamiltonianChecksum
    (realismDepthProfile xs)
  ≡
  SES.EncoderState.hamiltonianState (SES.stateOf xs)
hamiltonianChecksumExactWitness xs = refl

emittedChecksumPairStableWitness :
  ∀ {n} (xs : Vec Base n) →
  SES.StreamingEncoderSurface.checksumSurface
    SES.streamingEncoderSurface
    (SES.stateOf xs)
  ≡
  ( SynthesisSequencingRealismDepthProfile.thermoChecksum
      (realismDepthProfile xs)
  , SynthesisSequencingRealismDepthProfile.hamiltonianChecksum
      (realismDepthProfile xs)
  )
emittedChecksumPairStableWitness xs = refl

nextStepAdmissibilityStableWitness :
  ∀ {n} (xs : Vec Base n) (b : Base) →
  SES.stepAdmissible
    (SES.stateOf
      (snd
        (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs)))
    b
  ≡
  SES.stepAdmissible (SES.stateOf xs) b
nextStepAdmissibilityStableWitness =
  CSCL.emitNextStepAdmissibilityCanonicalWitness

synthesisSequencingRealismDepthSurface :
  SynthesisSequencingRealismDepthSurface
synthesisSequencingRealismDepthSurface = record
  { riskSurface = SSRS.synthesisSequencingRiskSurface
  ; realismSurface = SSRL.synthesisSequencingRealismSurface
  ; channelSurface = CCS.integratedChannelSurface
  ; checksumSurface = CSCL.crossoverSemanticChecksumLawSurface
  ; depthProfile = realismDepthProfile
  ; emittedWidthExact = emittedWidthExactWitness
  ; substitutionLevelStable = substitutionLevelStableWitness
  ; recoveryBoundaryStable = recoveryBoundaryStableWitness
  ; thermoChecksumExact = thermoChecksumExactWitness
  ; hamiltonianChecksumExact = hamiltonianChecksumExactWitness
  ; emittedChecksumPairStable = emittedChecksumPairStableWitness
  ; nextStepAdmissibilityStable = nextStepAdmissibilityStableWitness
  }
