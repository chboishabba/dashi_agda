module Ontology.DNA.CrossoverSemanticChecksumLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (fst; snd; _,_)
open import Data.Vec using (Vec)

open import Ontology.DNA.Supervoxel4Adic using (Base)

import Ontology.DNA.CrossoverAttachmentSurface as CAS
import Ontology.DNA.CrossoverChannelDepth as CCD
import Ontology.DNA.CrossoverAbstractChannelLaws as CACL
import Ontology.DNA.ChannelCodingSurface as CCS
import Ontology.DNA.StreamingEncoderSurface as SES

------------------------------------------------------------------------
-- Semantic checksum law surface for the DNA-first crossover/channel lane.
-- This stays within the current localized carrier: it packages exact
-- thermo/Hamiltonian checksum semantics and next-step admissibility
-- coherence for emitted sequences at the stable attachment boundary.

record CrossoverSemanticChecksumLawSurface : Set₁ where
  field
    attachment : CAS.CrossoverAttachmentSurface
    abstractLaws : CACL.CrossoverAbstractChannelLawSurface
    channelDepth : CCD.CrossoverChannelDepthSurface

    emitThermoChecksumCanonical :
      ∀ {n} (xs : Vec Base n) →
      fst
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf
            (snd
              (CCS.IntegratedChannelSurface.emit
                (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
                xs))))
      ≡
      SES.EncoderState.thermoState (SES.stateOf xs)

    emitHamiltonianChecksumCanonical :
      ∀ {n} (xs : Vec Base n) →
      snd
        (SES.StreamingEncoderSurface.checksumSurface
          (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
          (SES.stateOf
            (snd
              (CCS.IntegratedChannelSurface.emit
                (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
                xs))))
      ≡
      SES.EncoderState.hamiltonianState (SES.stateOf xs)

    emitSemanticChecksumPairCanonical :
      ∀ {n} (xs : Vec Base n) →
      SES.StreamingEncoderSurface.checksumSurface
        (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
        (SES.stateOf
          (snd
            (CCS.IntegratedChannelSurface.emit
              (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
              xs)))
      ≡
      ( SES.EncoderState.thermoState (SES.stateOf xs)
      , SES.EncoderState.hamiltonianState (SES.stateOf xs)
      )

    emitNextStepAdmissibilityCanonical :
      ∀ {n} (xs : Vec Base n) (b : Base) →
      SES.stepAdmissible
        (SES.stateOf
          (snd
            (CCS.IntegratedChannelSurface.emit
              (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
              xs)))
        b
      ≡
      SES.stepAdmissible (SES.stateOf xs) b

emitThermoChecksumCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  fst
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf
        (snd
          (CCS.IntegratedChannelSurface.emit
            (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
            xs))))
  ≡
  SES.EncoderState.thermoState (SES.stateOf xs)
emitThermoChecksumCanonicalWitness xs = refl

emitHamiltonianChecksumCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  snd
    (SES.StreamingEncoderSurface.checksumSurface
      (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
      (SES.stateOf
        (snd
          (CCS.IntegratedChannelSurface.emit
            (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
            xs))))
  ≡
  SES.EncoderState.hamiltonianState (SES.stateOf xs)
emitHamiltonianChecksumCanonicalWitness xs = refl

emitSemanticChecksumPairCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  SES.StreamingEncoderSurface.checksumSurface
    (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
    (SES.stateOf
      (snd
        (CCS.IntegratedChannelSurface.emit
          (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
          xs)))
  ≡
  ( SES.EncoderState.thermoState (SES.stateOf xs)
  , SES.EncoderState.hamiltonianState (SES.stateOf xs)
  )
emitSemanticChecksumPairCanonicalWitness xs = refl

emitNextStepAdmissibilityCanonicalWitness :
  ∀ {n} (xs : Vec Base n) (b : Base) →
  SES.stepAdmissible
    (SES.stateOf
      (snd
        (CCS.IntegratedChannelSurface.emit
          (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
          xs)))
    b
  ≡
  SES.stepAdmissible (SES.stateOf xs) b
emitNextStepAdmissibilityCanonicalWitness =
  CCD.CrossoverChannelDepthSurface.emittedStateAdmissibleNextExact
    CCD.crossoverChannelDepthSurface

crossoverSemanticChecksumLawSurface : CrossoverSemanticChecksumLawSurface
crossoverSemanticChecksumLawSurface = record
  { attachment = CAS.crossoverAttachmentSurface
  ; abstractLaws = CACL.crossoverAbstractChannelLawSurface
  ; channelDepth = CCD.crossoverChannelDepthSurface
  ; emitThermoChecksumCanonical = emitThermoChecksumCanonicalWitness
  ; emitHamiltonianChecksumCanonical = emitHamiltonianChecksumCanonicalWitness
  ; emitSemanticChecksumPairCanonical = emitSemanticChecksumPairCanonicalWitness
  ; emitNextStepAdmissibilityCanonical =
      emitNextStepAdmissibilityCanonicalWitness
  }
