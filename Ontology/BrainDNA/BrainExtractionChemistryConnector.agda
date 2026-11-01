module Ontology.BrainDNA.BrainExtractionChemistryConnector where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.Brain.BrainExtractionSurface as Extraction using
  (BrainExtraction; BrainExtractionSurface; brainExtractionSurface;
   extractState; extractWidth-compatible; extractLayer-compatible;
   extractActive-compatible)
open import Ontology.BrainDNA.BrainSummaryPacketCompatibility as Summary using
  (BrainSummaryPacketView; summaryStatePacketView)
open import Ontology.BrainDNA.BrainSummaryChemistryCompatibility as Chemistry using
  (BrainSummaryChemistryCompatibilitySurface;
   brainSummaryChemistryCompatibilitySurface;
   summarySheetCoordinates; summarySheetBandEnergy; summaryCrossBandEnergy;
   summaryChemistryHamiltonian; summaryChemistryWidthExact;
   summaryChemistryOrderLineMajor)
open import Ontology.DNA.ChemistrySheetHamiltonian using (SheetCoordinates)
open import Ontology.DNA.EigenclassSurface using (ScanOrder)

------------------------------------------------------------------------
-- Narrow connector from the current brain extraction owner into the
-- current summary-level DNA/chemistry boundary.
--
-- This remains theorem-thin and non-claiming: it only packages the
-- already-local extraction metadata together with the current
-- chemistry-sheet/Hamiltonian boundary induced by the summary packet
-- view on the existing carrier.

extractionChemistryOrder :
  ∀ {n} → BrainState n → ScanOrder
extractionChemistryOrder st =
  BrainSummaryPacketView.order (summaryStatePacketView st)

extractionChemistrySheet :
  ∀ {n} → BrainState n → SheetCoordinates n
extractionChemistrySheet = summarySheetCoordinates

extractionChemistryBandEnergy :
  ∀ {n} → BrainState n → Nat
extractionChemistryBandEnergy = summarySheetBandEnergy

extractionChemistryCrossBandEnergy :
  ∀ {n} → BrainState n → Nat
extractionChemistryCrossBandEnergy = summaryCrossBandEnergy

extractionChemistryHamiltonian :
  ∀ {n} → BrainState n → Nat
extractionChemistryHamiltonian = summaryChemistryHamiltonian

extractionWidth-summary-compatible :
  ∀ {n} (st : BrainState n) →
  BrainExtraction.width (extractState st)
    ≡
  BrainSummaryPacketView.width (summaryStatePacketView st)
extractionWidth-summary-compatible st = refl

extractionLayer-summary-compatible :
  ∀ {n} (st : BrainState n) →
  BrainExtraction.layer (extractState st)
    ≡
  BrainSummaryPacketView.layer (summaryStatePacketView st)
extractionLayer-summary-compatible st = refl

extractionActive-summary-compatible :
  ∀ {n} (st : BrainState n) →
  BrainExtraction.activeFlag (extractState st)
    ≡
  BrainSummaryPacketView.activeFlag (summaryStatePacketView st)
extractionActive-summary-compatible st = refl

extractionChemistryWidthExact :
  ∀ {n} (st : BrainState n) →
  BrainExtraction.width (extractState st) ≡ n
extractionChemistryWidthExact st = refl

extractionChemistryOrderExact :
  ∀ {n} (st : BrainState n) →
  extractionChemistryOrder st
    ≡
  BrainSummaryPacketView.order (summaryStatePacketView st)
extractionChemistryOrderExact st = refl

extractionChemistryOrderLineMajor :
  ∀ {n} (st : BrainState n) →
  extractionChemistryOrder st
    ≡
  Chemistry.BrainSummaryChemistryCompatibilitySurface.summaryOrder
    brainSummaryChemistryCompatibilitySurface st
extractionChemistryOrderLineMajor st = summaryChemistryOrderLineMajor st

extractionChemistrySheetExact :
  ∀ {n} (st : BrainState n) →
  extractionChemistrySheet st
    ≡
  Chemistry.BrainSummaryChemistryCompatibilitySurface.summarySheet
    brainSummaryChemistryCompatibilitySurface st
extractionChemistrySheetExact st = refl

extractionChemistryBandEnergyExact :
  ∀ {n} (st : BrainState n) →
  extractionChemistryBandEnergy st
    ≡
  Chemistry.BrainSummaryChemistryCompatibilitySurface.summarySheetEnergy
    brainSummaryChemistryCompatibilitySurface st
extractionChemistryBandEnergyExact st = refl

extractionChemistryCrossBandEnergyExact :
  ∀ {n} (st : BrainState n) →
  extractionChemistryCrossBandEnergy st
    ≡
  Chemistry.BrainSummaryChemistryCompatibilitySurface.summaryCrossEnergy
    brainSummaryChemistryCompatibilitySurface st
extractionChemistryCrossBandEnergyExact st = refl

extractionChemistryHamiltonianExact :
  ∀ {n} (st : BrainState n) →
  extractionChemistryHamiltonian st
    ≡
  Chemistry.BrainSummaryChemistryCompatibilitySurface.summaryHamiltonian
    brainSummaryChemistryCompatibilitySurface st
extractionChemistryHamiltonianExact st = refl

record BrainExtractionChemistryConnectorSurface : Set₂ where
  field
    extractionSurface : BrainExtractionSurface
    summaryChemistrySurface : BrainSummaryChemistryCompatibilitySurface
    extractionOrder : ∀ {n} → BrainState n → ScanOrder
    extractionSheet : ∀ {n} → BrainState n → SheetCoordinates n
    extractionBandEnergy : ∀ {n} → BrainState n → Nat
    extractionCrossBandEnergy : ∀ {n} → BrainState n → Nat
    extractionHamiltonian : ∀ {n} → BrainState n → Nat

brainExtractionChemistryConnectorSurface :
  BrainExtractionChemistryConnectorSurface
brainExtractionChemistryConnectorSurface = record
  { extractionSurface = brainExtractionSurface
  ; summaryChemistrySurface = brainSummaryChemistryCompatibilitySurface
  ; extractionOrder = extractionChemistryOrder
  ; extractionSheet = extractionChemistrySheet
  ; extractionBandEnergy = extractionChemistryBandEnergy
  ; extractionCrossBandEnergy = extractionChemistryCrossBandEnergy
  ; extractionHamiltonian = extractionChemistryHamiltonian
  }
