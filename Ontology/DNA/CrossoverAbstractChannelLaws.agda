module Ontology.DNA.CrossoverAbstractChannelLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Data.Vec using (Vec)

open import Ontology.DNA.Supervoxel4Adic using (Base)

import Ontology.DNA.CrossoverAttachmentSurface as CAS
import Ontology.DNA.CrossoverAttachmentLaws as CAL
import Ontology.DNA.CrossoverChannelDepth as CCD
import Ontology.DNA.ChannelCodingSurface as CCS
import Ontology.DNA.StreamingEncoderSurface as SES

------------------------------------------------------------------------
-- More abstract theorem-thin law surface for the DNA crossover/channel
-- lane. This does not introduce richer wet-lab or decoding semantics; it
-- only packages the current canonical emit/re-entry laws at the stable
-- attachment boundary.

record CrossoverAbstractChannelLawSurface : Set₁ where
  field
    attachment : CAS.CrossoverAttachmentSurface
    attachmentLaws : CAL.CrossoverAttachmentLawSurface
    depth : CCD.CrossoverChannelDepthSurface

    emitLengthCanonical :
      ∀ {n} (xs : Vec Base n) →
      fst
        (CCS.IntegratedChannelSurface.emit
          (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
          xs)
      ≡ n

    emitCanonical :
      ∀ {n} (xs : Vec Base n) →
      CCS.IntegratedChannelSurface.emit
        (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
        xs
      ≡ (n , xs)

    emitGenericAdmissibilityCanonical :
      ∀ {n} (xs : Vec Base n) →
      CCS.genericAdmissibilityFlag
        (snd
          (CCS.IntegratedChannelSurface.emit
            (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
            xs))
      ≡
      CCS.genericAdmissibilityFlag xs

    emitInnerAdmissibilityCanonical :
      ∀ {n} (xs : Vec Base n) →
      CCS.InnerChannelCode.admissibilityFlag
        (CCS.IntegratedChannelSurface.innerCode
          (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface))
        (snd
          (CCS.IntegratedChannelSurface.emit
            (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
            xs))
      ≡
      CCS.genericAdmissibilityFlag xs

    emitStreamingStateCanonical :
      ∀ {n} (xs : Vec Base n) →
      SES.stateOf
        (snd
          (CCS.IntegratedChannelSurface.emit
            (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
            xs))
      ≡
      SES.stateOf xs

    emitStreamingPrefixCanonical :
      ∀ {n} (xs : Vec Base n) →
      SES.EncoderState.prefix
        (SES.stateOf
          (snd
            (CCS.IntegratedChannelSurface.emit
              (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
              xs)))
      ≡ xs

    emitChecksumCanonical :
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

emitLengthCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  fst
    (CCS.IntegratedChannelSurface.emit
      (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
      xs)
  ≡ n
emitLengthCanonicalWitness xs = refl

emitCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  CCS.IntegratedChannelSurface.emit
    (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
    xs
  ≡ (n , xs)
emitCanonicalWitness xs = refl

emitGenericAdmissibilityCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  CCS.genericAdmissibilityFlag
    (snd
      (CCS.IntegratedChannelSurface.emit
        (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
        xs))
  ≡
  CCS.genericAdmissibilityFlag xs
emitGenericAdmissibilityCanonicalWitness xs =
  CAL.CrossoverAttachmentLawSurface.emitOutputGenericAdmissibility
    CAL.crossoverAttachmentLawSurface
    xs

emitInnerAdmissibilityCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  CCS.InnerChannelCode.admissibilityFlag
    (CCS.IntegratedChannelSurface.innerCode
      (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface))
    (snd
      (CCS.IntegratedChannelSurface.emit
        (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
        xs))
  ≡
  CCS.genericAdmissibilityFlag xs
emitInnerAdmissibilityCanonicalWitness xs = refl

emitStreamingStateCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  SES.stateOf
    (snd
      (CCS.IntegratedChannelSurface.emit
        (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
        xs))
  ≡
  SES.stateOf xs
emitStreamingStateCanonicalWitness =
  CCD.CrossoverChannelDepthSurface.emittedStateExact
    CCD.crossoverChannelDepthSurface

emitStreamingPrefixCanonicalWitness :
  ∀ {n} (xs : Vec Base n) →
  SES.EncoderState.prefix
    (SES.stateOf
      (snd
        (CCS.IntegratedChannelSurface.emit
          (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
          xs)))
  ≡ xs
emitStreamingPrefixCanonicalWitness =
  CCD.CrossoverChannelDepthSurface.emittedStatePrefixExact
    CCD.crossoverChannelDepthSurface

emitChecksumCanonicalWitness :
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
emitChecksumCanonicalWitness =
  CCD.CrossoverChannelDepthSurface.emittedStateChecksumExact
    CCD.crossoverChannelDepthSurface

crossoverAbstractChannelLawSurface : CrossoverAbstractChannelLawSurface
crossoverAbstractChannelLawSurface = record
  { attachment = CAS.crossoverAttachmentSurface
  ; attachmentLaws = CAL.crossoverAttachmentLawSurface
  ; depth = CCD.crossoverChannelDepthSurface
  ; emitLengthCanonical = emitLengthCanonicalWitness
  ; emitCanonical = emitCanonicalWitness
  ; emitGenericAdmissibilityCanonical = emitGenericAdmissibilityCanonicalWitness
  ; emitInnerAdmissibilityCanonical = emitInnerAdmissibilityCanonicalWitness
  ; emitStreamingStateCanonical = emitStreamingStateCanonicalWitness
  ; emitStreamingPrefixCanonical = emitStreamingPrefixCanonicalWitness
  ; emitChecksumCanonical = emitChecksumCanonicalWitness
  }
