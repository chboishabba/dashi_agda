module Ontology.BrainDNA.BrainSummaryStructuralDepth where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Sigma using (fst; snd)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.BrainDNA.BrainStateCrossoverLaws as StateLaw using
  (BrainStateCrossoverLawSurface;
   brainStateCrossoverLawSurface;
   stateEmitOutputGenericAdmissibility;
   stateEmitOutputLengthExact)
open import Ontology.BrainDNA.BrainSummaryStructuralConsumer as Consumer using
  (BrainSummaryStructuralConsumerSurface;
   brainSummaryStructuralConsumerSurface;
   consumerStructuralOrder;
   consumerStructuralEncodedBases;
   consumerStructuralEmittedBases;
   consumerStructuralOrder-lineMajor;
   consumerStructuralSummaryWidthMatchesEmitLength;
   consumerStructuralEmitOutputGenericAdmissibility;
   consumerStructuralAdjacencyScore-zero;
   consumerStructuralCrossBandStructured;
   consumerStructuralHamiltonianExact)
open import Ontology.DNA.ChannelCodingSurface using (genericAdmissibilityFlag)
open import Ontology.DNA.ChemistrySheetHamiltonian using
  (crossBandEnergy)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded downstream law/depth surface over the current structural-summary
-- consumer.
--
-- This stays theorem-thin and local. It does not claim payload recovery,
-- biological semantics, or a richer chemistry model. It only packages one
-- deeper downstream view that keeps the current structural-summary consumer,
-- state-origin crossover laws, and chemistry-side exactness in one place.

record BrainSummaryStructuralDepth : Set where
  constructor mkBrainSummaryStructuralDepth
  field
    order : ScanOrder
    summaryWidth : Nat
    emittedWidth : Nat
    emittedAdmissibility : Bool
    adjacencyScore : Nat
    crossBand : Nat
    hamiltonian : Nat

brainSummaryStructuralDepth :
  ∀ {n} → BrainState n → BrainSummaryStructuralDepth
brainSummaryStructuralDepth {n} st =
  mkBrainSummaryStructuralDepth
    (Consumer.consumerStructuralOrder st)
    n
    (fst (Consumer.consumerStructuralEmittedBases st))
    (genericAdmissibilityFlag (snd (Consumer.consumerStructuralEmittedBases st)))
    zero
    (Consumer.BrainSummaryStructuralConsumerSurface.consumerCrossBandEnergy
      Consumer.brainSummaryStructuralConsumerSurface st)
    (Consumer.BrainSummaryStructuralConsumerSurface.consumerHamiltonian
      Consumer.brainSummaryStructuralConsumerSurface st)

brainSummaryStructuralDepthOrder-lineMajor :
  ∀ {n} (st : BrainState n) →
  BrainSummaryStructuralDepth.order
    (brainSummaryStructuralDepth st)
    ≡
  lineMajor
brainSummaryStructuralDepthOrder-lineMajor st =
  Consumer.consumerStructuralOrder-lineMajor st

brainSummaryStructuralDepthSummaryWidthExact :
  ∀ {n} (st : BrainState n) →
  BrainSummaryStructuralDepth.summaryWidth
    (brainSummaryStructuralDepth st)
    ≡
  n
brainSummaryStructuralDepthSummaryWidthExact st = refl

brainSummaryStructuralDepthEmittedWidthExact :
  ∀ {n} (st : BrainState n) →
  BrainSummaryStructuralDepth.emittedWidth
    (brainSummaryStructuralDepth st)
    ≡
  n
brainSummaryStructuralDepthEmittedWidthExact st =
  StateLaw.stateEmitOutputLengthExact st

brainSummaryStructuralDepthWidthStable :
  ∀ {n} (st : BrainState n) →
  BrainSummaryStructuralDepth.summaryWidth
    (brainSummaryStructuralDepth st)
    ≡
  BrainSummaryStructuralDepth.emittedWidth
    (brainSummaryStructuralDepth st)
brainSummaryStructuralDepthWidthStable st =
  Consumer.consumerStructuralSummaryWidthMatchesEmitLength st

brainSummaryStructuralDepthAdmissibilityCoherent :
  ∀ {n} (st : BrainState n) →
  BrainSummaryStructuralDepth.emittedAdmissibility
    (brainSummaryStructuralDepth st)
    ≡
  genericAdmissibilityFlag
    (Consumer.consumerStructuralEncodedBases st)
brainSummaryStructuralDepthAdmissibilityCoherent st =
  Consumer.consumerStructuralEmitOutputGenericAdmissibility st

brainSummaryStructuralDepthAdjacencyCollapsed :
  ∀ {n} (st : BrainState n) →
  BrainSummaryStructuralDepth.adjacencyScore
    (brainSummaryStructuralDepth st)
    ≡
  zero
brainSummaryStructuralDepthAdjacencyCollapsed st =
  Consumer.consumerStructuralAdjacencyScore-zero st

brainSummaryStructuralDepthChemistryStructured :
  ∀ {n} (st : BrainState n) →
  BrainSummaryStructuralDepth.crossBand
    (brainSummaryStructuralDepth st)
    ≡
  crossBandEnergy
    (Consumer.BrainSummaryStructuralConsumerSurface.consumerSheet
      Consumer.brainSummaryStructuralConsumerSurface st)
brainSummaryStructuralDepthChemistryStructured st =
  Consumer.consumerStructuralCrossBandStructured st

brainSummaryStructuralDepthHamiltonianStable :
  ∀ {n} (st : BrainState n) →
  BrainSummaryStructuralDepth.hamiltonian
    (brainSummaryStructuralDepth st)
    ≡
  Consumer.BrainSummaryStructuralConsumerSurface.consumerHamiltonian
    Consumer.brainSummaryStructuralConsumerSurface st
brainSummaryStructuralDepthHamiltonianStable st =
  Consumer.consumerStructuralHamiltonianExact st

record BrainSummaryStructuralDepthSurface : Set₂ where
  field
    consumerSurface : BrainSummaryStructuralConsumerSurface
    stateCrossoverLaws : BrainStateCrossoverLawSurface
    depth : ∀ {n} → BrainState n → BrainSummaryStructuralDepth

brainSummaryStructuralDepthSurface :
  BrainSummaryStructuralDepthSurface
brainSummaryStructuralDepthSurface = record
  { consumerSurface = Consumer.brainSummaryStructuralConsumerSurface
  ; stateCrossoverLaws = StateLaw.brainStateCrossoverLawSurface
  ; depth = brainSummaryStructuralDepth
  }
