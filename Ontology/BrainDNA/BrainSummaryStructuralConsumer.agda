module Ontology.BrainDNA.BrainSummaryStructuralConsumer where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Sigma using (Σ; fst; snd)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.BrainDNA.BrainSummaryPacketCompatibility as Summary using
  (BrainSummaryPacketView; summaryStatePacketView)
open import Ontology.BrainDNA.BrainSummaryEigenclassCompatibility as Eigen using
  (summaryRepresentativeMacro)
open import Ontology.BrainDNA.BrainStateCrossoverLaws as StateLaw using
  (BrainStateCrossoverLawSurface;
   brainStateCrossoverLawSurface;
   stateEmitOutputGenericAdmissibility;
   stateEmitOutputLengthExact)
open import Ontology.BrainDNA.BrainSummaryStructuralCompatibility as Structural using
  (BrainSummaryStructuralCompatibilitySurface;
   brainSummaryStructuralCompatibilitySurface;
   structuralSummaryOrder;
   structuralSummaryOrder-chemistry-consistent;
   structuralSummaryWidthExact;
   structuralSummaryCoupledAdjacency-true;
   structuralSummaryAdjacencyScore;
   structuralSummaryAdjacencyScore-zero;
   structuralSummarySheet;
   structuralSummaryCrossBandEnergy;
   structuralSummaryHamiltonian;
   structuralSummaryCrossBandStructured;
   structuralSummaryHamiltonianExact)
open import Ontology.DNA.ChannelCodingSurface using (genericAdmissibilityFlag)
open import Ontology.DNA.ChemistrySheetHamiltonian using
  (SheetCoordinates; crossBandEnergy)
open import Ontology.DNA.EigenclassSurface as ES using
  (ScanOrder; lineMajor)
open import Ontology.DNA.Supervoxel4Adic using (Base)

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

------------------------------------------------------------------------
-- Downstream consumer surface for the current structural-summary package.
--
-- This is intentionally theorem-thin: it consumes the composed
-- structural-summary package together with the current state-origin
-- crossover law surface, so the structural package is no longer detached.

consumerStructuralOrder :
  ∀ {n} → BrainState n → ScanOrder
consumerStructuralOrder = structuralSummaryOrder

consumerStructuralEncodedBases :
  ∀ {n} → BrainState n → Vec Base n
consumerStructuralEncodedBases =
  StateLaw.BrainStateCrossoverLawSurface.stateEncodedBases
    brainStateCrossoverLawSurface

consumerStructuralEmittedBases :
  ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
consumerStructuralEmittedBases =
  StateLaw.BrainStateCrossoverLawSurface.stateEmittedBases
    brainStateCrossoverLawSurface

consumerStructuralOrder-lineMajor :
  ∀ {n} (st : BrainState n) →
  consumerStructuralOrder st ≡ lineMajor
consumerStructuralOrder-lineMajor = structuralSummaryOrder-chemistry-consistent

consumerStructuralOrderMatchesStateLaw :
  ∀ {n} (st : BrainState n) →
  consumerStructuralOrder st
    ≡
  StateLaw.BrainStateCrossoverLawSurface.stateOrderLineMajor
    brainStateCrossoverLawSurface st
consumerStructuralOrderMatchesStateLaw st = refl

consumerStructuralEmitLengthMatchesSummaryWidth :
  ∀ {n} (st : BrainState n) →
  fst (consumerStructuralEmittedBases st)
    ≡
  n
consumerStructuralEmitLengthMatchesSummaryWidth st =
  stateEmitOutputLengthExact st

consumerStructuralSummaryWidthMatchesEmitLength :
  ∀ {n} (st : BrainState n) →
  BrainSummaryPacketView.width
    (summaryStatePacketView st)
    ≡
  fst (consumerStructuralEmittedBases st)
consumerStructuralSummaryWidthMatchesEmitLength st =
  trans (structuralSummaryWidthExact st) (sym (consumerStructuralEmitLengthMatchesSummaryWidth st))

consumerStructuralEmitOutputGenericAdmissibility :
  ∀ {n} (st : BrainState n) →
  genericAdmissibilityFlag (snd (consumerStructuralEmittedBases st))
    ≡
  genericAdmissibilityFlag (consumerStructuralEncodedBases st)
consumerStructuralEmitOutputGenericAdmissibility =
  stateEmitOutputGenericAdmissibility

consumerStructuralCoupledAdjacency-true :
  ∀ {n} (st : BrainState n) →
  ES.MacroAdjacencySurface.coupledAdjacency
    (summaryRepresentativeMacro (summaryStatePacketView st))
    ≡ true
consumerStructuralCoupledAdjacency-true = structuralSummaryCoupledAdjacency-true

consumerStructuralAdjacencyScore-zero :
  ∀ {n} (st : BrainState n) →
  structuralSummaryAdjacencyScore st ≡ zero
consumerStructuralAdjacencyScore-zero = structuralSummaryAdjacencyScore-zero

consumerStructuralCrossBandStructured :
  ∀ {n} (st : BrainState n) →
  structuralSummaryCrossBandEnergy st
    ≡
  crossBandEnergy (structuralSummarySheet st)
consumerStructuralCrossBandStructured = structuralSummaryCrossBandStructured

consumerStructuralHamiltonianExact :
  ∀ {n} (st : BrainState n) →
  structuralSummaryHamiltonian st ≡ structuralSummaryHamiltonian st
consumerStructuralHamiltonianExact st =
  trans (structuralSummaryHamiltonianExact st) refl

record BrainSummaryStructuralConsumerSurface : Set₂ where
  field
    structuralCompatibility : BrainSummaryStructuralCompatibilitySurface
    stateCrossoverLaws : BrainStateCrossoverLawSurface
    consumerOrder : ∀ {n} → BrainState n → ScanOrder
    consumerEncodedBases : ∀ {n} → BrainState n → Vec Base n
    consumerEmittedBases : ∀ {n} → BrainState n → Σ Nat (λ m → Vec Base m)
    consumerSheet : ∀ {n} → BrainState n → SheetCoordinates n
    consumerCrossBandEnergy : ∀ {n} → BrainState n → Nat
    consumerHamiltonian : ∀ {n} → BrainState n → Nat

brainSummaryStructuralConsumerSurface :
  BrainSummaryStructuralConsumerSurface
brainSummaryStructuralConsumerSurface = record
  { structuralCompatibility = brainSummaryStructuralCompatibilitySurface
  ; stateCrossoverLaws = brainStateCrossoverLawSurface
  ; consumerOrder = consumerStructuralOrder
  ; consumerEncodedBases = consumerStructuralEncodedBases
  ; consumerEmittedBases = consumerStructuralEmittedBases
  ; consumerSheet = structuralSummarySheet
  ; consumerCrossBandEnergy = structuralSummaryCrossBandEnergy
  ; consumerHamiltonian = structuralSummaryHamiltonian
  }
