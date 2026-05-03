module Ontology.DNA.SynthesisSequencingRealismLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (fst; snd)
open import Data.Vec using (Vec)

open import Ontology.DNA.Supervoxel4Adic using (Base)

import Ontology.DNA.ChannelCodingSurface as CCS
import Ontology.DNA.StreamingEncoderSurface as SES
import Ontology.DNA.CrossoverSemanticChecksumLaws as CSCL
import Ontology.DNA.SynthesisSequencingRiskSurface as SSRS

------------------------------------------------------------------------
-- Bounded consumer/law surface over the current synthesis/sequencing risk
-- owner and the localized DNA streaming/channel/checksum owners.
--
-- This remains theorem-thin and interface-like. It does not claim wet-lab
-- realism, calibration, or empirical validity. It only packages exact
-- read/write/channel/checksum coherence over the current carrier.

record SynthesisSequencingRealismSurface : Set₁ where
  field
    riskSurface : SSRS.SynthesisSequencingRiskSurface
    channelSurface : CCS.IntegratedChannelSurface
    checksumSurface : CSCL.CrossoverSemanticChecksumLawSurface

    writeReadLengthCanonical :
      ∀ {n} (xs : Vec Base n) →
      fst
        (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs)
      ≡ n

    writeReadPayloadCanonical :
      ∀ {n} (xs : Vec Base n) →
      snd
        (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs)
      ≡ xs

    writeReadStateCanonical :
      ∀ {n} (xs : Vec Base n) →
      SES.stateOf
        (snd
          (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs))
      ≡
      SES.stateOf xs

    writeReadPrefixCanonical :
      ∀ {n} (xs : Vec Base n) →
      SES.EncoderState.prefix
        (SES.stateOf
          (snd
            (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs)))
      ≡ xs

    writeReadRiskRecoveryBoundaryExact :
      SSRS.SynthesisSequencingRiskProfile.recoveryBoundary
        (SSRS.SynthesisSequencingRiskSurface.profile riskSurface)
      ≡
      CCS.IntegratedChannelSurface.recoveryBoundary channelSurface

    writeReadRiskLevelsStable :
      SSRS.SynthesisSequencingRiskProfile.substitutionLevel
        (SSRS.SynthesisSequencingRiskSurface.profile riskSurface)
      ≡
      SSRS.classifyRiskLevel
        (CCS.PhysicalChannelModel.substitutionRisk
          (CCS.IntegratedChannelSurface.channel channelSurface))

    emittedThermoChecksumCanonical :
      ∀ {n} (xs : Vec Base n) →
      CSCL.CrossoverSemanticChecksumLawSurface.emitThermoChecksumCanonical
        checksumSurface xs
      ≡
      CSCL.CrossoverSemanticChecksumLawSurface.emitThermoChecksumCanonical
        checksumSurface xs

    emittedHamiltonianChecksumCanonical :
      ∀ {n} (xs : Vec Base n) →
      CSCL.CrossoverSemanticChecksumLawSurface.emitHamiltonianChecksumCanonical
        checksumSurface xs
      ≡
      CSCL.CrossoverSemanticChecksumLawSurface.emitHamiltonianChecksumCanonical
        checksumSurface xs

    emittedChecksumPairCanonical :
      ∀ {n} (xs : Vec Base n) →
      CSCL.CrossoverSemanticChecksumLawSurface.emitSemanticChecksumPairCanonical
        checksumSurface xs
      ≡
      CSCL.CrossoverSemanticChecksumLawSurface.emitSemanticChecksumPairCanonical
        checksumSurface xs

    nextStepAdmissibilityRealismCanonical :
      ∀ {n} (xs : Vec Base n) (b : Base) →
      SES.stepAdmissible
        (SES.stateOf
          (snd
            (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs)))
        b
      ≡
      SES.stepAdmissible (SES.stateOf xs) b

writeReadLengthCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  fst
    (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs)
  ≡ n
writeReadLengthCanonicalWitness xs = refl

writeReadPayloadCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  snd
    (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs)
  ≡ xs
writeReadPayloadCanonicalWitness xs = refl

writeReadStateCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  SES.stateOf
    (snd
      (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs))
  ≡
  SES.stateOf xs
writeReadStateCanonicalWitness xs = refl

writeReadPrefixCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  SES.EncoderState.prefix
    (SES.stateOf
      (snd
        (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs)))
  ≡ xs
writeReadPrefixCanonicalWitness xs = refl

writeReadRiskRecoveryBoundaryExactWitness :
  SSRS.SynthesisSequencingRiskProfile.recoveryBoundary
    (SSRS.SynthesisSequencingRiskSurface.profile
      SSRS.synthesisSequencingRiskSurface)
  ≡
  CCS.IntegratedChannelSurface.recoveryBoundary CCS.integratedChannelSurface
writeReadRiskRecoveryBoundaryExactWitness =
  SSRS.SynthesisSequencingRiskSurface.recoveryBoundaryExact
    SSRS.synthesisSequencingRiskSurface

writeReadRiskLevelsStableWitness :
  SSRS.SynthesisSequencingRiskProfile.substitutionLevel
    (SSRS.SynthesisSequencingRiskSurface.profile
      SSRS.synthesisSequencingRiskSurface)
  ≡
  SSRS.classifyRiskLevel
    (CCS.PhysicalChannelModel.substitutionRisk
      (CCS.IntegratedChannelSurface.channel CCS.integratedChannelSurface))
writeReadRiskLevelsStableWitness = refl

emittedThermoChecksumCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  CSCL.CrossoverSemanticChecksumLawSurface.emitThermoChecksumCanonical
    CSCL.crossoverSemanticChecksumLawSurface xs
  ≡
  CSCL.CrossoverSemanticChecksumLawSurface.emitThermoChecksumCanonical
    CSCL.crossoverSemanticChecksumLawSurface xs
emittedThermoChecksumCanonicalWitness xs = refl

emittedHamiltonianChecksumCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  CSCL.CrossoverSemanticChecksumLawSurface.emitHamiltonianChecksumCanonical
    CSCL.crossoverSemanticChecksumLawSurface xs
  ≡
  CSCL.CrossoverSemanticChecksumLawSurface.emitHamiltonianChecksumCanonical
    CSCL.crossoverSemanticChecksumLawSurface xs
emittedHamiltonianChecksumCanonicalWitness xs = refl

emittedChecksumPairCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  CSCL.CrossoverSemanticChecksumLawSurface.emitSemanticChecksumPairCanonical
    CSCL.crossoverSemanticChecksumLawSurface xs
  ≡
  CSCL.CrossoverSemanticChecksumLawSurface.emitSemanticChecksumPairCanonical
    CSCL.crossoverSemanticChecksumLawSurface xs
emittedChecksumPairCanonicalWitness xs = refl

nextStepAdmissibilityRealismCanonicalWitness :
  ∀ {n} (xs : Vec Base n) (b : Base) →
  SES.stepAdmissible
    (SES.stateOf
      (snd
        (CCS.IntegratedChannelSurface.emit CCS.integratedChannelSurface xs)))
    b
  ≡
  SES.stepAdmissible (SES.stateOf xs) b
nextStepAdmissibilityRealismCanonicalWitness =
  CSCL.emitNextStepAdmissibilityCanonicalWitness

synthesisSequencingRealismSurface : SynthesisSequencingRealismSurface
synthesisSequencingRealismSurface = record
  { riskSurface = SSRS.synthesisSequencingRiskSurface
  ; channelSurface = CCS.integratedChannelSurface
  ; checksumSurface = CSCL.crossoverSemanticChecksumLawSurface
  ; writeReadLengthCanonical = writeReadLengthCanonicalWitness
  ; writeReadPayloadCanonical = writeReadPayloadCanonicalWitness
  ; writeReadStateCanonical = writeReadStateCanonicalWitness
  ; writeReadPrefixCanonical = writeReadPrefixCanonicalWitness
  ; writeReadRiskRecoveryBoundaryExact =
      writeReadRiskRecoveryBoundaryExactWitness
  ; writeReadRiskLevelsStable = writeReadRiskLevelsStableWitness
  ; emittedThermoChecksumCanonical =
      emittedThermoChecksumCanonicalWitness
  ; emittedHamiltonianChecksumCanonical =
      emittedHamiltonianChecksumCanonicalWitness
  ; emittedChecksumPairCanonical = emittedChecksumPairCanonicalWitness
  ; nextStepAdmissibilityRealismCanonical =
      nextStepAdmissibilityRealismCanonicalWitness
  }
