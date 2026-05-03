module Ontology.BrainDNA.BrainCrossoverAbstractComposition where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; fst; snd)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.BrainDNA.BrainCodecSemanticDepth as Codec using
  (BrainCodecSemanticDepthSurface; brainCodecSemanticDepthSurface;
   BrainCodecSemanticProfile; codecSemanticProfileOf;
   semanticEmittedWidthExact; semanticEmissionAdmissibilityPreserved;
   semanticRecoveryBoundaryExact)
open import Ontology.BrainDNA.BrainCodecSemanticLaws as CodecLaw using
  (BrainCodecSemanticLawSurface; brainCodecSemanticLawSurface;
   semanticWidthAgreement; semanticRecoveredConstantSemantic)
open import Ontology.BrainDNA.BrainExtractionConnectorSemantics as ExtractionSem using
  (BrainExtractionConnectorSemanticsSurface;
   brainExtractionConnectorSemanticsSurface;
   BrainExtractionConnectorSemantics; brainExtractionConnectorSemantics;
   brainExtractionConnectorSemanticsWidthStable;
   brainExtractionConnectorSemanticsAdmissibilityCoherent;
   brainExtractionConnectorSemanticsChemistryStructured;
   brainExtractionConnectorSemanticsHamiltonianStable)
open import Ontology.BrainDNA.BrainSummaryStructuralDepth as Structural using
  (BrainSummaryStructuralDepthSurface; brainSummaryStructuralDepthSurface;
   BrainSummaryStructuralDepth; brainSummaryStructuralDepth;
   brainSummaryStructuralDepthEmittedWidthExact;
   brainSummaryStructuralDepthAdmissibilityCoherent;
   brainSummaryStructuralDepthAdjacencyCollapsed;
   brainSummaryStructuralDepthChemistryStructured;
   brainSummaryStructuralDepthHamiltonianStable)
open import Ontology.BrainDNA.BrainExtractionConnectorDepth as Extraction using
  (BrainExtractionConnectorDepthSurface; brainExtractionConnectorDepthSurface;
   BrainExtractionConnectorDepth; brainExtractionConnectorDepth;
   brainExtractionConnectorDepthOrder-lineMajor;
   brainExtractionConnectorDepthWidthStable;
   brainExtractionConnectorDepthChemistryStructured;
   brainExtractionConnectorDepthHamiltonianStable)
open import Ontology.DNA.CrossoverAbstractChannelLaws as Abstract using
  (CrossoverAbstractChannelLawSurface; crossoverAbstractChannelLawSurface)
open import Ontology.DNA.CrossoverSemanticChecksumLaws as Checksum using
  (CrossoverSemanticChecksumLawSurface; crossoverSemanticChecksumLawSurface)
import Ontology.DNA.CrossoverAttachmentSurface as CAS
import Ontology.DNA.ChannelCodingSurface as CCS
open import Ontology.DNA.ChannelCodingSurface using (genericAdmissibilityFlag)
open import Ontology.DNA.ChemistrySheetHamiltonian using (crossBandEnergy)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)
open import Ontology.DNA.StreamingEncoderSurface as SES
open import Ontology.DNA.Supervoxel4Adic using (Base)

------------------------------------------------------------------------
-- Bounded abstract composition surface for the local brain-DNA crossover.
--
-- This remains theorem-thin and non-claiming. It does not assert a rich
-- encode/decode theory, biological realism, or closure. It only composes
-- the current local codec, structural-summary, extraction-aware connector,
-- and DNA abstract crossover/channel owners into one stable abstraction
-- surface over the current carrier.

record BrainCrossoverAbstractProfile : Set where
  constructor brainCrossoverAbstractProfile
  field
    order : ScanOrder
    emittedWidth : Nat
    emittedAdmissibility : Bool
    adjacencyScore : Nat
    crossBand : Nat
    hamiltonian : Nat
    recoveryBoundary : Nat

brainCrossoverAbstractProfileOf :
  ∀ {n} → BrainState n → BrainCrossoverAbstractProfile
brainCrossoverAbstractProfileOf st =
  brainCrossoverAbstractProfile
    (Extraction.BrainExtractionConnectorDepth.order
      (brainExtractionConnectorDepth st))
    (Codec.BrainCodecSemanticProfile.emittedWidth
      (codecSemanticProfileOf st))
    (Codec.BrainCodecSemanticProfile.emittedAdmissibility
      (codecSemanticProfileOf st))
    (Structural.BrainSummaryStructuralDepth.adjacencyScore
      (brainSummaryStructuralDepth st))
    (Extraction.BrainExtractionConnectorDepth.crossBand
      (brainExtractionConnectorDepth st))
    (Extraction.BrainExtractionConnectorDepth.hamiltonian
      (brainExtractionConnectorDepth st))
    (Codec.BrainCodecSemanticProfile.recoveryBoundary
      (codecSemanticProfileOf st))

abstractOrderLineMajor :
  ∀ {n} (st : BrainState n) →
  BrainCrossoverAbstractProfile.order
    (brainCrossoverAbstractProfileOf st)
    ≡
  lineMajor
abstractOrderLineMajor st =
  Extraction.brainExtractionConnectorDepthOrder-lineMajor st

abstractEmittedWidthExact :
  ∀ {n} (st : BrainState n) →
  BrainCrossoverAbstractProfile.emittedWidth
    (brainCrossoverAbstractProfileOf st)
    ≡
  n
abstractEmittedWidthExact st =
  Codec.semanticEmittedWidthExact st

abstractEmittedWidthMatchesStructural :
  ∀ {n} (st : BrainState n) →
  BrainCrossoverAbstractProfile.emittedWidth
    (brainCrossoverAbstractProfileOf st)
    ≡
  Structural.BrainSummaryStructuralDepth.emittedWidth
    (brainSummaryStructuralDepth st)
abstractEmittedWidthMatchesStructural st
  rewrite Codec.semanticEmittedWidthExact st
        | Structural.brainSummaryStructuralDepthEmittedWidthExact st = refl

abstractEmittedAdmissibilityMatchesStructural :
  ∀ {n} (st : BrainState n) →
  BrainCrossoverAbstractProfile.emittedAdmissibility
    (brainCrossoverAbstractProfileOf st)
    ≡
  Structural.BrainSummaryStructuralDepth.emittedAdmissibility
    (brainSummaryStructuralDepth st)
abstractEmittedAdmissibilityMatchesStructural st
  rewrite Codec.semanticEmissionAdmissibilityPreserved st
        | Structural.brainSummaryStructuralDepthAdmissibilityCoherent st = refl

abstractExtractionWidthMatchesStructural :
  ∀ {n} (st : BrainState n) →
  Extraction.BrainExtractionConnectorDepth.extractionWidth
    (brainExtractionConnectorDepth st)
    ≡
  Structural.BrainSummaryStructuralDepth.emittedWidth
    (brainSummaryStructuralDepth st)
abstractExtractionWidthMatchesStructural st =
  ExtractionSem.brainExtractionConnectorSemanticsWidthStable st

abstractAdjacencyCollapsed :
  ∀ {n} (st : BrainState n) →
  BrainCrossoverAbstractProfile.adjacencyScore
    (brainCrossoverAbstractProfileOf st)
    ≡
  0
abstractAdjacencyCollapsed st =
  Structural.brainSummaryStructuralDepthAdjacencyCollapsed st

abstractChemistryStructured :
  ∀ {n} (st : BrainState n) →
  BrainCrossoverAbstractProfile.crossBand
    (brainCrossoverAbstractProfileOf st)
    ≡
  crossBandEnergy
    (Extraction.BrainExtractionConnectorDepth.sheet
      (brainExtractionConnectorDepth st))
abstractChemistryStructured st =
  ExtractionSem.brainExtractionConnectorSemanticsChemistryStructured st

abstractHamiltonianMatchesStructural :
  ∀ {n} (st : BrainState n) →
  BrainCrossoverAbstractProfile.hamiltonian
    (brainCrossoverAbstractProfileOf st)
    ≡
  Structural.BrainSummaryStructuralDepth.hamiltonian
    (brainSummaryStructuralDepth st)
abstractHamiltonianMatchesStructural st =
  ExtractionSem.brainExtractionConnectorSemanticsHamiltonianStable st

abstractRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) →
  BrainCrossoverAbstractProfile.recoveryBoundary
    (brainCrossoverAbstractProfileOf st)
    ≡
  3
abstractRecoveryBoundaryExact st =
  Codec.semanticRecoveryBoundaryExact st

abstractCodecWidthAgreement :
  ∀ {n} (st : BrainState n) →
  Codec.BrainCodecSemanticProfile.encodedWidth
    (codecSemanticProfileOf st)
    ≡
  BrainCrossoverAbstractProfile.emittedWidth
    (brainCrossoverAbstractProfileOf st)
abstractCodecWidthAgreement st =
  CodecLaw.semanticWidthAgreement st

abstractChannelCanonicalOnEmitted :
  ∀ {n} (st : BrainState n) →
  CCS.IntegratedChannelSurface.emit
    (CAS.CrossoverAttachmentSurface.channel CAS.crossoverAttachmentSurface)
    (snd
      (Codec.BrainCodecSemanticDepthSurface.emittedSemantic
        brainCodecSemanticDepthSurface st))
  ≡
  Codec.BrainCodecSemanticDepthSurface.emittedSemantic
    brainCodecSemanticDepthSurface st
abstractChannelCanonicalOnEmitted st =
  Abstract.CrossoverAbstractChannelLawSurface.emitCanonical
    crossoverAbstractChannelLawSurface
    (snd (Codec.BrainCodecSemanticDepthSurface.emittedSemantic
      brainCodecSemanticDepthSurface st))

abstractChannelAdmissibilityCanonicalOnEmitted :
  ∀ {n} (st : BrainState n) →
  Abstract.CrossoverAbstractChannelLawSurface.emitGenericAdmissibilityCanonical
    crossoverAbstractChannelLawSurface
    (snd
      (Codec.BrainCodecSemanticDepthSurface.emittedSemantic
        brainCodecSemanticDepthSurface st))
  ≡
  Abstract.CrossoverAbstractChannelLawSurface.emitGenericAdmissibilityCanonical
    crossoverAbstractChannelLawSurface
    (snd
      (Codec.BrainCodecSemanticDepthSurface.emittedSemantic
        brainCodecSemanticDepthSurface st))
abstractChannelAdmissibilityCanonicalOnEmitted st = refl

abstractChannelChecksumCanonicalOnEmitted :
  ∀ {n} (st : BrainState n) →
  SES.StreamingEncoderSurface.checksumSurface
    (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
    (SES.stateOf
      (snd
        (Codec.BrainCodecSemanticDepthSurface.emittedSemantic
          brainCodecSemanticDepthSurface st)))
  ≡
  SES.StreamingEncoderSurface.checksumSurface
    (CAS.CrossoverAttachmentSurface.streaming CAS.crossoverAttachmentSurface)
    (SES.stateOf
      (snd
        (Codec.BrainCodecSemanticDepthSurface.emittedSemantic
          brainCodecSemanticDepthSurface st)))
abstractChannelChecksumCanonicalOnEmitted st = refl

abstractSemanticChecksumCanonicalOnEmitted :
  ∀ {n} (st : BrainState n) →
  Checksum.CrossoverSemanticChecksumLawSurface.emitSemanticChecksumPairCanonical
    crossoverSemanticChecksumLawSurface
    (snd
      (Codec.BrainCodecSemanticDepthSurface.emittedSemantic
        brainCodecSemanticDepthSurface st))
  ≡
  Checksum.CrossoverSemanticChecksumLawSurface.emitSemanticChecksumPairCanonical
    crossoverSemanticChecksumLawSurface
    (snd
      (Codec.BrainCodecSemanticDepthSurface.emittedSemantic
        brainCodecSemanticDepthSurface st))
abstractSemanticChecksumCanonicalOnEmitted st = refl

abstractRecoveredSemanticConstant :
  ∀ {n m} (st₁ : BrainState n) (st₂ : BrainState m) →
  Codec.BrainCodecSemanticDepthSurface.recoveredSemantic
    brainCodecSemanticDepthSurface st₁
    ≡
  Codec.BrainCodecSemanticDepthSurface.recoveredSemantic
    brainCodecSemanticDepthSurface st₂
abstractRecoveredSemanticConstant st₁ st₂ =
  CodecLaw.semanticRecoveredConstantSemantic st₁ st₂

record BrainCrossoverAbstractCompositionSurface : Set₂ where
  field
    codecSemanticDepth : BrainCodecSemanticDepthSurface
    codecSemanticLaws : BrainCodecSemanticLawSurface
    structuralDepth : BrainSummaryStructuralDepthSurface
    extractionConnectorDepth : BrainExtractionConnectorDepthSurface
    extractionConnectorSemantics : BrainExtractionConnectorSemanticsSurface
    dnaAbstractChannel : CrossoverAbstractChannelLawSurface
    dnaSemanticChecksum : CrossoverSemanticChecksumLawSurface
    abstractProfile : ∀ {n} → BrainState n → BrainCrossoverAbstractProfile

brainCrossoverAbstractCompositionSurface :
  BrainCrossoverAbstractCompositionSurface
brainCrossoverAbstractCompositionSurface = record
  { codecSemanticDepth = brainCodecSemanticDepthSurface
  ; codecSemanticLaws = brainCodecSemanticLawSurface
  ; structuralDepth = brainSummaryStructuralDepthSurface
  ; extractionConnectorDepth = brainExtractionConnectorDepthSurface
  ; extractionConnectorSemantics = brainExtractionConnectorSemanticsSurface
  ; dnaAbstractChannel = crossoverAbstractChannelLawSurface
  ; dnaSemanticChecksum = crossoverSemanticChecksumLawSurface
  ; abstractProfile = brainCrossoverAbstractProfileOf
  }
