module Ontology.BrainDNA.BrainExtractionConnectorSemantics where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.Brain.BrainExtractionSurface as Extraction using
  (BrainExtraction; BrainExtractionSurface; brainExtractionSurface; extractState)
open import Ontology.Brain.BrainInvariantSurface as Invariant using
  (BrainCarrierInvariant; BrainInvariantSurface; brainInvariantSurface;
   invariantOfExtraction)
open import Ontology.Brain.BrainInvariantDepth as InvariantDepth using
  (BrainInvariantDepthSurface; brainInvariantDepthSurface;
   extractionDepth)
open import Ontology.BrainDNA.BrainExtractionChemistryConnector as Connector using
  (BrainExtractionChemistryConnectorSurface;
   brainExtractionChemistryConnectorSurface;
   extractionChemistryWidthExact; extractionChemistryOrderLineMajor)
open import Ontology.BrainDNA.BrainExtractionConnectorDepth as Depth using
  (BrainExtractionConnectorDepth; BrainExtractionConnectorDepthSurface;
   brainExtractionConnectorDepthSurface; brainExtractionConnectorDepth;
   brainExtractionConnectorDepthWidthStable;
   brainExtractionConnectorDepthLayerStable;
   brainExtractionConnectorDepthActiveExact;
   brainExtractionConnectorDepthAdmissibilityCoherent;
   brainExtractionConnectorDepthChemistryStructured;
   brainExtractionConnectorDepthHamiltonianStable)
open import Ontology.DNA.ChannelCodingSurface using (genericAdmissibilityFlag)
open import Ontology.DNA.ChemistrySheetHamiltonian using (crossBandEnergy)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded semantics surface over the explicit extraction-aware connector.
--
-- This remains theorem-thin and non-claiming. It does not add neuroscience
-- realism, biological interpretation, or closure claims. It only packages
-- the current extraction owner, invariant owner, extraction-aware connector,
-- and connector-depth surface into one sharper local semantics object.

record BrainExtractionConnectorSemantics (n : Nat) : Set where
  constructor mkBrainExtractionConnectorSemantics
  field
    invariant : BrainCarrierInvariant
    order : ScanOrder
    emittedWidth : Nat
    emittedAdmissibility : Bool
    crossBand : Nat
    hamiltonian : Nat

brainExtractionConnectorSemantics :
  ∀ {n} → BrainState n → BrainExtractionConnectorSemantics n
brainExtractionConnectorSemantics st =
  mkBrainExtractionConnectorSemantics
    (Invariant.invariantOfExtraction (Extraction.extractState st))
    (Depth.BrainExtractionConnectorDepth.order
      (brainExtractionConnectorDepth st))
    (Depth.BrainExtractionConnectorDepth.emittedWidth
      (brainExtractionConnectorDepth st))
    (Depth.BrainExtractionConnectorDepth.emittedAdmissibility
      (brainExtractionConnectorDepth st))
    (Depth.BrainExtractionConnectorDepth.crossBand
      (brainExtractionConnectorDepth st))
    (Depth.BrainExtractionConnectorDepth.hamiltonian
      (brainExtractionConnectorDepth st))

brainExtractionConnectorSemanticsInvariantExact :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorSemantics.invariant
    (brainExtractionConnectorSemantics st)
    ≡
  Invariant.invariantOfExtraction (Extraction.extractState st)
brainExtractionConnectorSemanticsInvariantExact st = refl

brainExtractionConnectorSemanticsWidthExact :
  ∀ {n} (st : BrainState n) →
  BrainCarrierInvariant.width
    (BrainExtractionConnectorSemantics.invariant
      (brainExtractionConnectorSemantics st))
    ≡
  n
brainExtractionConnectorSemanticsWidthExact st =
  extractionChemistryWidthExact st

brainExtractionConnectorSemanticsWidthStable :
  ∀ {n} (st : BrainState n) →
  BrainCarrierInvariant.width
    (BrainExtractionConnectorSemantics.invariant
      (brainExtractionConnectorSemantics st))
    ≡
  BrainExtractionConnectorSemantics.emittedWidth
    (brainExtractionConnectorSemantics st)
brainExtractionConnectorSemanticsWidthStable st =
  brainExtractionConnectorDepthWidthStable st

brainExtractionConnectorSemanticsLayerStable :
  ∀ {n} (st : BrainState n) →
  BrainCarrierInvariant.layer
    (BrainExtractionConnectorSemantics.invariant
      (brainExtractionConnectorSemantics st))
    ≡
  Depth.BrainExtractionConnectorDepth.layer
    (brainExtractionConnectorDepth st)
brainExtractionConnectorSemanticsLayerStable st =
  brainExtractionConnectorDepthLayerStable st

brainExtractionConnectorSemanticsActiveStable :
  ∀ {n} (st : BrainState n) →
  BrainCarrierInvariant.activeFlag
    (BrainExtractionConnectorSemantics.invariant
      (brainExtractionConnectorSemantics st))
    ≡
  Depth.BrainExtractionConnectorDepth.activeFlag
    (brainExtractionConnectorDepth st)
brainExtractionConnectorSemanticsActiveStable st =
  brainExtractionConnectorDepthActiveExact st

brainExtractionConnectorSemanticsOrderLineMajor :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorSemantics.order
    (brainExtractionConnectorSemantics st)
    ≡
  lineMajor
brainExtractionConnectorSemanticsOrderLineMajor st =
  extractionChemistryOrderLineMajor st

brainExtractionConnectorSemanticsAdmissibilityCoherent :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorSemantics.emittedAdmissibility
    (brainExtractionConnectorSemantics st)
    ≡
  Depth.BrainExtractionConnectorDepth.emittedAdmissibility
    (brainExtractionConnectorDepth st)
brainExtractionConnectorSemanticsAdmissibilityCoherent st =
  refl

brainExtractionConnectorSemanticsChemistryStructured :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorSemantics.crossBand
    (brainExtractionConnectorSemantics st)
    ≡
  crossBandEnergy
    (Depth.BrainExtractionConnectorDepth.sheet
      (brainExtractionConnectorDepth st))
brainExtractionConnectorSemanticsChemistryStructured st =
  brainExtractionConnectorDepthChemistryStructured st

brainExtractionConnectorSemanticsHamiltonianStable :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorSemantics.hamiltonian
    (brainExtractionConnectorSemantics st)
    ≡
  Depth.BrainExtractionConnectorDepth.hamiltonian
    (brainExtractionConnectorDepth st)
brainExtractionConnectorSemanticsHamiltonianStable st =
  brainExtractionConnectorDepthHamiltonianStable st

record BrainExtractionConnectorSemanticsSurface : Set₂ where
  field
    extractionSurface : BrainExtractionSurface
    invariantSurface : BrainInvariantSurface
    invariantDepthSurface : BrainInvariantDepthSurface
    extractionConnector : BrainExtractionChemistryConnectorSurface
    connectorDepth : BrainExtractionConnectorDepthSurface
    semantics : ∀ {n} → BrainState n → BrainExtractionConnectorSemantics n
    extractionInvariantDepth : ∀ {n} → BrainState n → Nat

brainExtractionConnectorSemanticsSurface :
  BrainExtractionConnectorSemanticsSurface
brainExtractionConnectorSemanticsSurface = record
  { extractionSurface = brainExtractionSurface
  ; invariantSurface = brainInvariantSurface
  ; invariantDepthSurface = brainInvariantDepthSurface
  ; extractionConnector = brainExtractionChemistryConnectorSurface
  ; connectorDepth = brainExtractionConnectorDepthSurface
  ; semantics = brainExtractionConnectorSemantics
  ; extractionInvariantDepth = λ st →
      extractionDepth (Extraction.extractState st)
  }
