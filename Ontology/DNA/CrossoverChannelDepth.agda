module Ontology.DNA.CrossoverChannelDepth where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; fst; snd)
open import Data.Vec using (Vec)

open import Ontology.DNA.Supervoxel4Adic using (Base)

import Ontology.DNA.CrossoverAttachmentSurface as CAS
import Ontology.DNA.CrossoverAttachmentLaws as CAL
import Ontology.DNA.ChannelCodingSurface as CCS
import Ontology.DNA.StreamingEncoderSurface as SES

------------------------------------------------------------------------
-- Narrow theorem-bearing depth surface for the DNA crossover/channel lane.
-- This does not add new channel semantics; it strengthens the existing
-- local import boundary with exact facts about the emitted sequence when
-- re-entered into the streaming encoder surface.

record CrossoverChannelDepthSurface : Set₁ where
  field
    attachment : CAS.CrossoverAttachmentSurface
    attachmentLaws : CAL.CrossoverAttachmentLawSurface

    emittedStateExact :
      ∀ {n} (xs : Vec Base n) →
      SES.stateOf
        (snd
          (CCS.IntegratedChannelSurface.emit
            (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
            xs))
      ≡
      SES.stateOf xs

    emittedStatePrefixExact :
      ∀ {n} (xs : Vec Base n) →
      SES.EncoderState.prefix
        (SES.stateOf
          (snd
            (CCS.IntegratedChannelSurface.emit
              (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
              xs)))
      ≡ xs

    emittedStateAdmissibleNextExact :
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

    emittedStateChecksumExact :
      ∀ {n} (xs : Vec Base n) →
      SES.StreamingEncoderSurface.checksumSurface
        (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
        (SES.stateOf
          (snd
            (CCS.IntegratedChannelSurface.emit
              (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
              xs)))
      ≡
      SES.StreamingEncoderSurface.checksumSurface
        (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
        (SES.stateOf xs)

emittedStateExactWitness :
  ∀ {n} (xs : Vec Base n) →
  SES.stateOf
    (snd
      (CCS.IntegratedChannelSurface.emit
        (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
        xs))
  ≡
  SES.stateOf xs
emittedStateExactWitness xs = refl

emittedStatePrefixExactWitness :
  ∀ {n} (xs : Vec Base n) →
  SES.EncoderState.prefix
    (SES.stateOf
      (snd
        (CCS.IntegratedChannelSurface.emit
          (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
          xs)))
  ≡ xs
emittedStatePrefixExactWitness xs = refl

emittedStateAdmissibleNextExactWitness :
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
emittedStateAdmissibleNextExactWitness xs b = refl

emittedStateChecksumExactWitness :
  ∀ {n} (xs : Vec Base n) →
  SES.StreamingEncoderSurface.checksumSurface
    (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
    (SES.stateOf
      (snd
        (CCS.IntegratedChannelSurface.emit
          (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
          xs)))
  ≡
  SES.StreamingEncoderSurface.checksumSurface
    (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
    (SES.stateOf xs)
emittedStateChecksumExactWitness xs = refl

crossoverChannelDepthSurface : CrossoverChannelDepthSurface
crossoverChannelDepthSurface = record
  { attachment = CAS.crossoverAttachmentSurface
  ; attachmentLaws = CAL.crossoverAttachmentLawSurface
  ; emittedStateExact = emittedStateExactWitness
  ; emittedStatePrefixExact = emittedStatePrefixExactWitness
  ; emittedStateAdmissibleNextExact = emittedStateAdmissibleNextExactWitness
  ; emittedStateChecksumExact = emittedStateChecksumExactWitness
  }
