module Ontology.BrainDNA.BrainExtractionConnectorDepth where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.Brain.BrainExtractionSurface as Extraction using
  (BrainExtraction)
open import Ontology.BrainDNA.BrainExtractionChemistryConnector as Connector using
  (BrainExtractionChemistryConnectorSurface;
   brainExtractionChemistryConnectorSurface;
   extractionChemistryOrder; extractionChemistrySheet;
   extractionChemistryCrossBandEnergy; extractionChemistryHamiltonian;
   extractionChemistryWidthExact; extractionChemistryOrderLineMajor)
open import Ontology.BrainDNA.BrainSummaryStructuralDepth as Structural using
  (BrainSummaryStructuralDepth; BrainSummaryStructuralDepthSurface;
   brainSummaryStructuralDepthSurface; brainSummaryStructuralDepth;
   brainSummaryStructuralDepthOrder-lineMajor;
   brainSummaryStructuralDepthSummaryWidthExact;
   brainSummaryStructuralDepthWidthStable;
   brainSummaryStructuralDepthAdmissibilityCoherent;
   brainSummaryStructuralDepthChemistryStructured;
   brainSummaryStructuralDepthHamiltonianStable)
open import Ontology.BrainDNA.BrainSummaryStructuralConsumer as Consumer using
  (BrainSummaryStructuralConsumerSurface; consumerStructuralEncodedBases)
open import Ontology.DNA.ChannelCodingSurface using (genericAdmissibilityFlag)
open import Ontology.DNA.ChemistrySheetHamiltonian using
  (SheetCoordinates; crossBandEnergy)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded depth surface for the explicit extraction-aware connector.
--
-- This remains theorem-thin and non-claiming. It does not add any claim
-- about neuroscience realism, payload semantics, or chemistry recovery.
-- It only packages the current extraction-aware connector together with
-- the downstream structural-depth view so the crossover lane can consume
-- one sharper local source than metadata alone.

record BrainExtractionConnectorDepth (n : Nat) : Set where
  constructor mkBrainExtractionConnectorDepth
  field
    order : ScanOrder
    extractionWidth : Nat
    emittedWidth : Nat
    layer : Nat
    activeFlag : Bool
    emittedAdmissibility : Bool
    sheet : SheetCoordinates n
    crossBand : Nat
    hamiltonian : Nat

brainExtractionConnectorDepth :
  ∀ {n} → BrainState n → BrainExtractionConnectorDepth n
brainExtractionConnectorDepth {n} st =
  mkBrainExtractionConnectorDepth
    (extractionChemistryOrder st)
    (BrainExtraction.width (Extraction.extractState st))
    (Structural.BrainSummaryStructuralDepth.emittedWidth
      (brainSummaryStructuralDepth st))
    (BrainExtraction.layer (Extraction.extractState st))
    (BrainExtraction.activeFlag (Extraction.extractState st))
    (Structural.BrainSummaryStructuralDepth.emittedAdmissibility
      (brainSummaryStructuralDepth st))
    (extractionChemistrySheet st)
    (extractionChemistryCrossBandEnergy st)
    (extractionChemistryHamiltonian st)

brainExtractionConnectorDepthOrder-lineMajor :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorDepth.order
    (brainExtractionConnectorDepth st)
    ≡
  lineMajor
brainExtractionConnectorDepthOrder-lineMajor st =
  extractionChemistryOrderLineMajor st

brainExtractionConnectorDepthExtractionWidthExact :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorDepth.extractionWidth
    (brainExtractionConnectorDepth st)
    ≡
  n
brainExtractionConnectorDepthExtractionWidthExact st =
  extractionChemistryWidthExact st

brainExtractionConnectorDepthEmittedWidthExact :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorDepth.emittedWidth
    (brainExtractionConnectorDepth st)
    ≡
  n
brainExtractionConnectorDepthEmittedWidthExact st =
  Structural.brainSummaryStructuralDepthEmittedWidthExact st

brainExtractionConnectorDepthWidthStable :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorDepth.extractionWidth
    (brainExtractionConnectorDepth st)
    ≡
  BrainExtractionConnectorDepth.emittedWidth
    (brainExtractionConnectorDepth st)
brainExtractionConnectorDepthWidthStable st =
  Structural.brainSummaryStructuralDepthWidthStable st

brainExtractionConnectorDepthLayerStable :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorDepth.layer
    (brainExtractionConnectorDepth st)
    ≡
  BrainExtraction.layer (Extraction.extractState st)
brainExtractionConnectorDepthLayerStable st = refl

brainExtractionConnectorDepthActiveExact :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorDepth.activeFlag
    (brainExtractionConnectorDepth st)
    ≡
  BrainExtraction.activeFlag (Extraction.extractState st)
brainExtractionConnectorDepthActiveExact st = refl

brainExtractionConnectorDepthAdmissibilityCoherent :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorDepth.emittedAdmissibility
    (brainExtractionConnectorDepth st)
    ≡
  genericAdmissibilityFlag
    (Consumer.consumerStructuralEncodedBases st)
brainExtractionConnectorDepthAdmissibilityCoherent st =
  Structural.brainSummaryStructuralDepthAdmissibilityCoherent st

brainExtractionConnectorDepthChemistryStructured :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorDepth.crossBand
    (brainExtractionConnectorDepth st)
    ≡
  crossBandEnergy
    (BrainExtractionConnectorDepth.sheet
      (brainExtractionConnectorDepth st))
brainExtractionConnectorDepthChemistryStructured st =
  Structural.brainSummaryStructuralDepthChemistryStructured st

brainExtractionConnectorDepthHamiltonianStable :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorDepth.hamiltonian
    (brainExtractionConnectorDepth st)
    ≡
  Structural.BrainSummaryStructuralDepth.hamiltonian
    (brainSummaryStructuralDepth st)
brainExtractionConnectorDepthHamiltonianStable st =
  Structural.brainSummaryStructuralDepthHamiltonianStable st

record BrainExtractionConnectorDepthSurface : Set₂ where
  field
    extractionConnector : BrainExtractionChemistryConnectorSurface
    structuralDepth : BrainSummaryStructuralDepthSurface
    depth : ∀ {n} → BrainState n → BrainExtractionConnectorDepth n

brainExtractionConnectorDepthSurface :
  BrainExtractionConnectorDepthSurface
brainExtractionConnectorDepthSurface = record
  { extractionConnector = brainExtractionChemistryConnectorSurface
  ; structuralDepth = brainSummaryStructuralDepthSurface
  ; depth = brainExtractionConnectorDepth
  }
