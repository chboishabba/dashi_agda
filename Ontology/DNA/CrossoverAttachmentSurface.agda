module Ontology.DNA.CrossoverAttachmentSurface where

open import Agda.Builtin.Equality using (_≡_; refl)

import Ontology.DNA.StreamingEncoderSurface as SES
import Ontology.DNA.ChannelCodingSurface as CCS
import Ontology.DNA.EigenclassSurface as ES
import Ontology.DNA.SupervoxelAdmissibility as SA

------------------------------------------------------------------------
-- Minimal DNA-side attachment surface for later brain-DNA imports.
-- This does not add new chemistry or coding claims; it only packages the
-- already-owned local surfaces behind one stable import boundary.

record CrossoverAttachmentSurface : Set₁ where
  field
    streaming : SES.StreamingEncoderSurface
    channel : CCS.IntegratedChannelSurface
    classify3 : ES.DNA3 → ES.EigenClass3
    macroSurface : ES.DNA6x3 → ES.MacroAdjacencySurface
    admissibility : SA.SupervoxelAdmissibilitySurface

    channelUsesStreaming :
      CCS.IntegratedChannelSurface.encoderSurface channel ≡ streaming

    macroScanOrderLineMajor :
      (xs : ES.DNA6x3) →
      ES.MacroAdjacencySurface.scanOrder (macroSurface xs) ≡ ES.lineMajor

    supervoxelChecksumExact :
      (sv : SA.Supervoxel256) →
      SA.SupervoxelAdmissibilitySurface.checksum admissibility sv
        ≡ SA.supervoxelChecksum sv

    supervoxelInvolutionExact :
      (sv : SA.Supervoxel256) →
      SA.SupervoxelAdmissibilitySurface.involution admissibility
        (SA.SupervoxelAdmissibilitySurface.involution admissibility sv)
        ≡ sv

crossoverAttachmentSurface : CrossoverAttachmentSurface
crossoverAttachmentSurface = record
  { streaming = SES.streamingEncoderSurface
  ; channel = CCS.integratedChannelSurface
  ; classify3 = ES.classify3
  ; macroSurface = ES.macroSurface
  ; admissibility = SA.supervoxelAdmissibilitySurface
  ; channelUsesStreaming = refl
  ; macroScanOrderLineMajor = ES.macroSurface-scanOrder-lineMajor
  ; supervoxelChecksumExact =
      SA.SupervoxelAdmissibilitySurface.checksumWitness
        SA.supervoxelAdmissibilitySurface
  ; supervoxelInvolutionExact =
      SA.SupervoxelAdmissibilitySurface.involutionLaw
        SA.supervoxelAdmissibilitySurface
  }
