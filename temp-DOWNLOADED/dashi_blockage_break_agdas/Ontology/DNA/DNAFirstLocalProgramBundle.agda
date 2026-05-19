module Ontology.DNA.DNAFirstLocalProgramBundle where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

import Ontology.DNA.Supervoxel4Adic as FourAdic
import Ontology.DNA.ChemistryQuotient as Quotient
import Ontology.DNA.ChemistryConcrete as ChemistryConcrete
import Ontology.DNA.ChemistryUVConcrete as ChemistryUV
import Ontology.DNA.SupervoxelAdmissibility as Admissibility
import Ontology.DNA.StreamingEncoderSurface as Streaming
import Ontology.DNA.ChannelCodingSurface as Channel
import Ontology.DNA.CrossoverAttachmentSurface as Attachment
import Ontology.DNA.CrossoverAttachmentLaws as AttachmentLaws
import Ontology.DNA.CrossoverAbstractChannelLaws as AbstractChannel
import Ontology.DNA.CrossoverSemanticChecksumLaws as Checksum
import Ontology.DNA.SupervoxelChemistryCouplingLaws as Coupling
import Ontology.DNA.SupervoxelChemistryLongWindowLaws as LongWindow
import Ontology.DNA.SynthesisSequencingRiskSurface as Risk
import Ontology.DNA.SynthesisSequencingRealismLaws as Realism

------------------------------------------------------------------------
-- DNA-first local program bundle.
--
-- This breaks the "DNA lane is only conceptual" blockage locally: the carrier,
-- quotient, UV, supervoxel, streaming, channel, checksum, and long-window
-- chemistry surfaces are concrete theorem owners.  It is still an adjacent
-- program bundle, not a physics-unification theorem.

record DNAFirstLocalProgramBundle : Setω where
  field
    fourAdicCarrier : FourAdic.BlockLift4Adic

    chemistryQuotientConcrete : Quotient.ChemistryQuotientInterface
    chemistryQuotientUV : Quotient.ChemistryQuotientInterface

    supervoxelAdmissibility : Admissibility.SupervoxelAdmissibilitySurface
    streamingEncoder : Streaming.StreamingEncoderSurface
    integratedChannel : Channel.IntegratedChannelSurface
    crossoverAttachment : Attachment.CrossoverAttachmentSurface
    crossoverAttachmentLaws : AttachmentLaws.CrossoverAttachmentLawSurface
    crossoverAbstractChannel : AbstractChannel.CrossoverAbstractChannelLawSurface
    semanticChecksum : Checksum.CrossoverSemanticChecksumLawSurface
    supervoxelChemistryCoupling : Coupling.SupervoxelChemistryCouplingLawSurface
    longWindowChemistry : LongWindow.SupervoxelChemistryLongWindowLawSurface
    synthesisSequencingRisk : Risk.SynthesisSequencingRiskSurface
    synthesisSequencingRealism : Realism.SynthesisSequencingRealismSurface

    realFormalAdjacentProgram : ⊤
    notUnificationTheoremLane : ⊤

    promotionWouldRequire : List String

DNAFirstLocalProgram : DNAFirstLocalProgramBundle
DNAFirstLocalProgram = record
  { fourAdicCarrier = FourAdic.canonicalDNA4Adic
  ; chemistryQuotientConcrete = ChemistryConcrete.chemistryQuotientInterfaceConcrete
  ; chemistryQuotientUV = ChemistryUV.chemistryQuotientInterfaceUVConcrete
  ; supervoxelAdmissibility = Admissibility.supervoxelAdmissibilitySurface
  ; streamingEncoder = Streaming.streamingEncoderSurface
  ; integratedChannel = Channel.integratedChannelSurface
  ; crossoverAttachment = Attachment.crossoverAttachmentSurface
  ; crossoverAttachmentLaws = AttachmentLaws.crossoverAttachmentLawSurface
  ; crossoverAbstractChannel = AbstractChannel.crossoverAbstractChannelLawSurface
  ; semanticChecksum = Checksum.crossoverSemanticChecksumLawSurface
  ; supervoxelChemistryCoupling = Coupling.supervoxelChemistryCouplingLawSurface
  ; longWindowChemistry = LongWindow.supervoxelChemistryLongWindowLawSurface
  ; synthesisSequencingRisk = Risk.synthesisSequencingRiskSurface
  ; synthesisSequencingRealism = Realism.synthesisSequencingRealismSurface
  ; realFormalAdjacentProgram = tt
  ; notUnificationTheoremLane = tt
  ; promotionWouldRequire =
      "a bridge from DNA-first channel/chemistry laws into the DASHI closure owner layer"
      ∷ "a theorem showing which DNA observables are closure-relevant, not just codec/channel-relevant"
      ∷ "a bounded empirical or mechanistic interpretation contract for biological mutation dynamics"
      ∷ []
  }
