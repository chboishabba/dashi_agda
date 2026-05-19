module Ontology.BrainDNA.BrainAtomicChemistryHandoff where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.Brain.BrainExtractionSurface as Extraction using
  (BrainExtraction; BrainExtractionSurface; brainExtractionSurface; extractState)
open import Ontology.BrainDNA.BrainExtractionChemistryConnector as Connector using
  (BrainExtractionChemistryConnectorSurface;
   brainExtractionChemistryConnectorSurface;
   extractionChemistryOrder;
   extractionChemistrySheet;
   extractionChemistryWidthExact;
   extractionChemistryOrderLineMajor)
open import Ontology.BrainDNA.BrainExtractionConnectorSemantics as ConnectorSem using
  (BrainExtractionConnectorSemanticsSurface;
   brainExtractionConnectorSemanticsSurface;
   BrainExtractionConnectorSemantics; brainExtractionConnectorSemantics;
   brainExtractionConnectorSemanticsChemistryStructured;
   brainExtractionConnectorSemanticsHamiltonianStable)
open import Ontology.BrainDNA.BrainCrossoverIntegrationLaws as Integration using
  (BrainCrossoverIntegrationLawSurface;
   brainCrossoverIntegrationLawSurface;
   BrainCrossoverIntegrationProfile; brainCrossoverIntegrationProfileOf;
   integrationOrderLineMajor;
   integrationChemistryMatchesExtraction;
   integrationHamiltonianMatchesExtraction;
   integrationRecoveryBoundaryExact)
open import Ontology.DNA.ChemistrySheetHamiltonian using
  (SheetCoordinates; crossBandEnergy)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)
open import DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem as Physics using
  (AtomicChemistryRecoveryTheorem;
   canonicalAtomicChemistryRecoveryTheorem)

------------------------------------------------------------------------
-- Bounded local handoff surface from the explicit brain-DNA connector
-- chain into the physics-facing chemistry carrier.
--
-- This remains theorem-thin and interface-like. It does not claim atomic
-- recovery, chemistry recovery, or a physical derivation. It only packages
-- the current local chemistry-visible outputs together with the canonical
-- physics-facing chemistry support surface.

record BrainAtomicChemistryHandoffProfile (n : Nat) : Set where
  constructor brainAtomicChemistryHandoffProfile
  field
    order : ScanOrder
    width : Nat
    layer : Nat
    activeFlag : Bool
    sheet : SheetCoordinates n
    crossBand : Nat
    hamiltonian : Nat
    recoveryBoundary : Nat

brainAtomicChemistryHandoffProfileOf :
  ∀ {n} → BrainState n → BrainAtomicChemistryHandoffProfile n
brainAtomicChemistryHandoffProfileOf st =
  brainAtomicChemistryHandoffProfile
    (Connector.extractionChemistryOrder st)
    (BrainExtraction.width (Extraction.extractState st))
    (BrainExtraction.layer (Extraction.extractState st))
    (BrainExtraction.activeFlag (Extraction.extractState st))
    (Connector.extractionChemistrySheet st)
    (ConnectorSem.BrainExtractionConnectorSemantics.crossBand
      (ConnectorSem.brainExtractionConnectorSemantics st))
    (ConnectorSem.BrainExtractionConnectorSemantics.hamiltonian
      (ConnectorSem.brainExtractionConnectorSemantics st))
    (Integration.BrainCrossoverIntegrationProfile.recoveryBoundary
      (Integration.brainCrossoverIntegrationProfileOf st))

handoffWidthExact :
  ∀ {n} (st : BrainState n) →
  BrainAtomicChemistryHandoffProfile.width
    (brainAtomicChemistryHandoffProfileOf st)
    ≡
  n
handoffWidthExact st = Connector.extractionChemistryWidthExact st

handoffOrderLineMajor :
  ∀ {n} (st : BrainState n) →
  BrainAtomicChemistryHandoffProfile.order
    (brainAtomicChemistryHandoffProfileOf st)
    ≡
  lineMajor
handoffOrderLineMajor st = Connector.extractionChemistryOrderLineMajor st

handoffOrderMatchesIntegration :
  ∀ {n} (st : BrainState n) →
  BrainAtomicChemistryHandoffProfile.order
    (brainAtomicChemistryHandoffProfileOf st)
    ≡
  Integration.BrainCrossoverIntegrationProfile.order
    (Integration.brainCrossoverIntegrationProfileOf st)
handoffOrderMatchesIntegration st = refl

handoffChemistryStructured :
  ∀ {n} (st : BrainState n) →
  BrainAtomicChemistryHandoffProfile.crossBand
    (brainAtomicChemistryHandoffProfileOf st)
    ≡
  crossBandEnergy
    (BrainAtomicChemistryHandoffProfile.sheet
      (brainAtomicChemistryHandoffProfileOf st))
handoffChemistryStructured st =
  ConnectorSem.brainExtractionConnectorSemanticsChemistryStructured st

handoffCrossBandMatchesIntegration :
  ∀ {n} (st : BrainState n) →
  BrainAtomicChemistryHandoffProfile.crossBand
    (brainAtomicChemistryHandoffProfileOf st)
    ≡
  Integration.BrainCrossoverIntegrationProfile.crossBand
    (Integration.brainCrossoverIntegrationProfileOf st)
handoffCrossBandMatchesIntegration st =
  Integration.integrationChemistryMatchesExtraction st

handoffHamiltonianMatchesIntegration :
  ∀ {n} (st : BrainState n) →
  BrainAtomicChemistryHandoffProfile.hamiltonian
    (brainAtomicChemistryHandoffProfileOf st)
    ≡
  Integration.BrainCrossoverIntegrationProfile.hamiltonian
    (Integration.brainCrossoverIntegrationProfileOf st)
handoffHamiltonianMatchesIntegration st =
  Integration.integrationHamiltonianMatchesExtraction st

handoffRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) →
  BrainAtomicChemistryHandoffProfile.recoveryBoundary
    (brainAtomicChemistryHandoffProfileOf st)
    ≡
  3
handoffRecoveryBoundaryExact st =
  Integration.integrationRecoveryBoundaryExact st

record BrainAtomicChemistryHandoffSurface : Setω where
  field
    extractionConnector : BrainExtractionChemistryConnectorSurface
    extractionConnectorSemantics : BrainExtractionConnectorSemanticsSurface
    crossoverIntegration : BrainCrossoverIntegrationLawSurface
    physicsRecovery : AtomicChemistryRecoveryTheorem
    chemistryCarrierSupport : Set
    handoffProfile : ∀ {n} → BrainState n → BrainAtomicChemistryHandoffProfile n

brainAtomicChemistryHandoffSurface : BrainAtomicChemistryHandoffSurface
brainAtomicChemistryHandoffSurface = record
  { extractionConnector = brainExtractionChemistryConnectorSurface
  ; extractionConnectorSemantics = brainExtractionConnectorSemanticsSurface
  ; crossoverIntegration = brainCrossoverIntegrationLawSurface
  ; physicsRecovery = canonicalAtomicChemistryRecoveryTheorem
  ; chemistryCarrierSupport =
      Physics.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport
        canonicalAtomicChemistryRecoveryTheorem
  ; handoffProfile = brainAtomicChemistryHandoffProfileOf
  }
