module Ontology.BrainDNA.BrainSummaryStructuralCompatibility where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.BrainDNA.BrainSummaryPacketCompatibility as Summary using
  (BrainSummaryPacketCompatibilitySurface;
   brainSummaryPacketCompatibilitySurface;
   BrainSummaryPacketView; summaryStatePacketView)
open import Ontology.BrainDNA.BrainSummaryEigenclassCompatibility as Eigen using
  (BrainSummaryEigenclassCompatibilitySurface;
   brainSummaryEigenclassCompatibilitySurface;
   summaryRepresentativeMacro;
   summaryRepresentativeCoupledAdjacency-true;
   summaryRepresentativeAdjacencyScore-zero;
   summaryRepresentativeOrder-compatible)
open import Ontology.BrainDNA.BrainSummaryChemistryCompatibility as Chemistry using
  (BrainSummaryChemistryCompatibilitySurface;
   brainSummaryChemistryCompatibilitySurface;
   summarySheetCoordinates; summarySheetBandEnergy; summaryCrossBandEnergy;
   summaryChemistryHamiltonian; summaryChemistryWidthExact;
   summaryChemistryOrderLineMajor; summarySheetCoordinatesExact;
   summaryCrossBandEnergyStructured; summaryChemistryHamiltonianExact)
open import Ontology.DNA.ChemistrySheetHamiltonian as Sheet using
  (SheetCoordinates; crossBandEnergy)
open import Ontology.DNA.EigenclassSurface as ES using
  (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Structural-summary composition surface for the crossover lane.
--
-- This stays theorem-thin and local. It does not claim payload recovery or a
-- richer semantic equivalence between the brain and DNA sides. It only
-- composes the existing summary->eigenclass and summary->chemistry bridges
-- into one bounded package with exact witnesses on the current carrier.

structuralSummaryOrder :
  ∀ {n} → BrainState n → ScanOrder
structuralSummaryOrder st =
  ES.MacroAdjacencySurface.scanOrder
    (Eigen.summaryRepresentativeMacro (Summary.summaryStatePacketView st))

structuralSummaryAdjacencyScore :
  ∀ {n} → BrainState n → Nat
structuralSummaryAdjacencyScore st =
  ES.MacroAdjacencySurface.adjacencyScore
    (Eigen.summaryRepresentativeMacro (Summary.summaryStatePacketView st))

structuralSummarySheet :
  ∀ {n} → BrainState n → SheetCoordinates n
structuralSummarySheet = Chemistry.summarySheetCoordinates

structuralSummaryBandEnergy :
  ∀ {n} → BrainState n → Nat
structuralSummaryBandEnergy = Chemistry.summarySheetBandEnergy

structuralSummaryCrossBandEnergy :
  ∀ {n} → BrainState n → Nat
structuralSummaryCrossBandEnergy = Chemistry.summaryCrossBandEnergy

structuralSummaryHamiltonian :
  ∀ {n} → BrainState n → Nat
structuralSummaryHamiltonian = Chemistry.summaryChemistryHamiltonian

structuralSummaryOrder-summary-consistent :
  ∀ {n} (st : BrainState n) →
  structuralSummaryOrder st ≡ Summary.BrainSummaryPacketView.order (Summary.summaryStatePacketView st)
structuralSummaryOrder-summary-consistent st =
  Eigen.summaryRepresentativeOrder-compatible st

structuralSummaryOrder-chemistry-consistent :
  ∀ {n} (st : BrainState n) →
  structuralSummaryOrder st ≡ lineMajor
structuralSummaryOrder-chemistry-consistent st = refl

structuralSummaryWidthExact :
  ∀ {n} (st : BrainState n) →
  Summary.BrainSummaryPacketView.width (Summary.summaryStatePacketView st) ≡ n
structuralSummaryWidthExact st = Chemistry.summaryChemistryWidthExact st

structuralSummaryCoupledAdjacency-true :
  ∀ {n} (st : BrainState n) →
  ES.MacroAdjacencySurface.coupledAdjacency
    (Eigen.summaryRepresentativeMacro (Summary.summaryStatePacketView st))
    ≡ true
structuralSummaryCoupledAdjacency-true st =
  Eigen.summaryRepresentativeCoupledAdjacency-true st

structuralSummaryAdjacencyScore-zero :
  ∀ {n} (st : BrainState n) →
  structuralSummaryAdjacencyScore st ≡ zero
structuralSummaryAdjacencyScore-zero st =
  Eigen.summaryRepresentativeAdjacencyScore-zero st

structuralSummarySheetExact :
  ∀ {n} (st : BrainState n) →
  structuralSummarySheet st ≡ Chemistry.summarySheetCoordinates st
structuralSummarySheetExact st = Chemistry.summarySheetCoordinatesExact st

structuralSummaryCrossBandStructured :
  ∀ {n} (st : BrainState n) →
  structuralSummaryCrossBandEnergy st
    ≡
  crossBandEnergy (structuralSummarySheet st)
structuralSummaryCrossBandStructured st = Chemistry.summaryCrossBandEnergyStructured st

structuralSummaryHamiltonianExact :
  ∀ {n} (st : BrainState n) →
  structuralSummaryHamiltonian st ≡ Chemistry.summaryChemistryHamiltonian st
structuralSummaryHamiltonianExact st = Chemistry.summaryChemistryHamiltonianExact st

record BrainSummaryStructuralCompatibilitySurface : Set₂ where
  field
    summaryPacketSurface : BrainSummaryPacketCompatibilitySurface
    summaryEigenclassSurface : BrainSummaryEigenclassCompatibilitySurface
    summaryChemistrySurface : BrainSummaryChemistryCompatibilitySurface
    structuralOrder : ∀ {n} → BrainState n → ScanOrder
    structuralAdjacencyScore : ∀ {n} → BrainState n → Nat
    structuralSheet : ∀ {n} → BrainState n → SheetCoordinates n
    structuralBandEnergy : ∀ {n} → BrainState n → Nat
    structuralCrossBandEnergy : ∀ {n} → BrainState n → Nat
    structuralHamiltonian : ∀ {n} → BrainState n → Nat

brainSummaryStructuralCompatibilitySurface :
  BrainSummaryStructuralCompatibilitySurface
brainSummaryStructuralCompatibilitySurface = record
  { summaryPacketSurface = brainSummaryPacketCompatibilitySurface
  ; summaryEigenclassSurface = brainSummaryEigenclassCompatibilitySurface
  ; summaryChemistrySurface = brainSummaryChemistryCompatibilitySurface
  ; structuralOrder = structuralSummaryOrder
  ; structuralAdjacencyScore = structuralSummaryAdjacencyScore
  ; structuralSheet = structuralSummarySheet
  ; structuralBandEnergy = structuralSummaryBandEnergy
  ; structuralCrossBandEnergy = structuralSummaryCrossBandEnergy
  ; structuralHamiltonian = structuralSummaryHamiltonian
  }
