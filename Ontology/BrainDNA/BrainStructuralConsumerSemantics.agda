module Ontology.BrainDNA.BrainStructuralConsumerSemantics where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (fst; snd)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.Brain.BrainInvariantDepth as InvariantDepth using
  (_⊎_; inj₁; inj₂; BrainInvariantDepthSurface; brainInvariantDepthSurface)
open import Ontology.BrainDNA.BrainExtractionConnectorSemantics as ExtractionSem using
  (BrainExtractionConnectorSemantics; BrainExtractionConnectorSemanticsSurface;
   brainExtractionConnectorSemanticsSurface; brainExtractionConnectorSemantics;
   brainExtractionConnectorSemanticsInvariantExact;
   brainExtractionConnectorSemanticsWidthStable;
   brainExtractionConnectorSemanticsOrderLineMajor;
   brainExtractionConnectorSemanticsAdmissibilityCoherent;
   brainExtractionConnectorSemanticsChemistryStructured;
   brainExtractionConnectorSemanticsHamiltonianStable)
open import Ontology.BrainDNA.BrainSummaryStructuralConsumer as Consumer using
  (BrainSummaryStructuralConsumerSurface; brainSummaryStructuralConsumerSurface;
   consumerStructuralOrder; consumerStructuralEmittedBases;
   consumerStructuralOrder-lineMajor;
   consumerStructuralEmitOutputGenericAdmissibility;
   consumerStructuralCrossBandStructured;
   consumerStructuralHamiltonianExact)
open import Ontology.BrainDNA.BrainCrossoverAbstractComposition as Abstract using
  (BrainCrossoverAbstractCompositionSurface;
   brainCrossoverAbstractCompositionSurface;
   BrainCrossoverAbstractProfile; brainCrossoverAbstractProfileOf;
   abstractEmittedWidthMatchesStructural;
   abstractEmittedAdmissibilityMatchesStructural;
   abstractChemistryStructured;
   abstractHamiltonianMatchesStructural;
   abstractRecoveryBoundaryExact)
open import Ontology.DNA.ChannelCodingSurface using (genericAdmissibilityFlag)
open import Ontology.DNA.ChemistrySheetHamiltonian using (crossBandEnergy)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded consumer-facing semantics surface for the local brain-side stack.
--
-- This remains theorem-thin and non-claiming. It does not assert richer
-- neuroscience structure, payload meaning, or closure. It only ensures the
-- local brain extraction/invariant/invariant-depth stack is consumed by a
-- sharper crossover-facing structural consumer and abstract composition.

record BrainStructuralConsumerSemanticProfile : Set where
  constructor mkBrainStructuralConsumerSemanticProfile
  field
    invariantDepth : Nat
    order : ScanOrder
    emittedWidth : Nat
    emittedAdmissibility : Bool
    crossBand : Nat
    hamiltonian : Nat
    recoveryBoundary : Nat

brainStructuralConsumerSemanticProfile :
  ∀ {n} → BrainState n → BrainStructuralConsumerSemanticProfile
brainStructuralConsumerSemanticProfile st =
  mkBrainStructuralConsumerSemanticProfile
    (ExtractionSem.BrainExtractionConnectorSemanticsSurface.extractionInvariantDepth
      brainExtractionConnectorSemanticsSurface st)
    (Consumer.consumerStructuralOrder st)
    (fst (Consumer.consumerStructuralEmittedBases st))
    (genericAdmissibilityFlag (snd (Consumer.consumerStructuralEmittedBases st)))
    (Abstract.BrainCrossoverAbstractProfile.crossBand
      (brainCrossoverAbstractProfileOf st))
    (Abstract.BrainCrossoverAbstractProfile.hamiltonian
      (brainCrossoverAbstractProfileOf st))
    (Abstract.BrainCrossoverAbstractProfile.recoveryBoundary
      (brainCrossoverAbstractProfileOf st))

brainStructuralConsumerSemanticInvariantBounded :
  ∀ {n} (st : BrainState n) →
  (BrainStructuralConsumerSemanticProfile.invariantDepth
    (brainStructuralConsumerSemanticProfile st) ≡ zero)
  ⊎
  (BrainStructuralConsumerSemanticProfile.invariantDepth
    (brainStructuralConsumerSemanticProfile st) ≡ suc zero)
brainStructuralConsumerSemanticInvariantBounded st =
  InvariantDepth.BrainInvariantDepthSurface.bounded
    brainInvariantDepthSurface
    (ExtractionSem.BrainExtractionConnectorSemantics.invariant
      (brainExtractionConnectorSemantics st))

brainStructuralConsumerSemanticOrderLineMajor :
  ∀ {n} (st : BrainState n) →
  BrainStructuralConsumerSemanticProfile.order
    (brainStructuralConsumerSemanticProfile st)
    ≡
  lineMajor
brainStructuralConsumerSemanticOrderLineMajor st =
  Consumer.consumerStructuralOrder-lineMajor st

brainStructuralConsumerSemanticWidthMatchesExtraction :
  ∀ {n} (st : BrainState n) →
  BrainStructuralConsumerSemanticProfile.emittedWidth
    (brainStructuralConsumerSemanticProfile st)
    ≡
  ExtractionSem.BrainExtractionConnectorSemantics.emittedWidth
    (brainExtractionConnectorSemantics st)
brainStructuralConsumerSemanticWidthMatchesExtraction st =
  abstractEmittedWidthMatchesStructural st

brainStructuralConsumerSemanticAdmissibilityMatchesExtraction :
  ∀ {n} (st : BrainState n) →
  BrainStructuralConsumerSemanticProfile.emittedAdmissibility
    (brainStructuralConsumerSemanticProfile st)
    ≡
  ExtractionSem.BrainExtractionConnectorSemantics.emittedAdmissibility
    (brainExtractionConnectorSemantics st)
brainStructuralConsumerSemanticAdmissibilityMatchesExtraction st =
  abstractEmittedAdmissibilityMatchesStructural st

brainStructuralConsumerSemanticCrossBandMatchesExtraction :
  ∀ {n} (st : BrainState n) →
  BrainStructuralConsumerSemanticProfile.crossBand
    (brainStructuralConsumerSemanticProfile st)
    ≡
  ExtractionSem.BrainExtractionConnectorSemantics.crossBand
    (brainExtractionConnectorSemantics st)
brainStructuralConsumerSemanticCrossBandMatchesExtraction st = refl

brainStructuralConsumerSemanticHamiltonianMatchesExtraction :
  ∀ {n} (st : BrainState n) →
  BrainStructuralConsumerSemanticProfile.hamiltonian
    (brainStructuralConsumerSemanticProfile st)
    ≡
  ExtractionSem.BrainExtractionConnectorSemantics.hamiltonian
    (brainExtractionConnectorSemantics st)
brainStructuralConsumerSemanticHamiltonianMatchesExtraction st =
  abstractHamiltonianMatchesStructural st

brainStructuralConsumerSemanticRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) →
  BrainStructuralConsumerSemanticProfile.recoveryBoundary
    (brainStructuralConsumerSemanticProfile st)
    ≡
  3
brainStructuralConsumerSemanticRecoveryBoundaryExact st =
  abstractRecoveryBoundaryExact st

record BrainStructuralConsumerSemanticsSurface : Set₂ where
  field
    invariantDepthSurface : BrainInvariantDepthSurface
    extractionConnectorSemantics : BrainExtractionConnectorSemanticsSurface
    structuralConsumerSurface : BrainSummaryStructuralConsumerSurface
    abstractCompositionSurface : BrainCrossoverAbstractCompositionSurface
    semanticProfile : ∀ {n} → BrainState n → BrainStructuralConsumerSemanticProfile

brainStructuralConsumerSemanticsSurface :
  BrainStructuralConsumerSemanticsSurface
brainStructuralConsumerSemanticsSurface = record
  { invariantDepthSurface = brainInvariantDepthSurface
  ; extractionConnectorSemantics = brainExtractionConnectorSemanticsSurface
  ; structuralConsumerSurface = brainSummaryStructuralConsumerSurface
  ; abstractCompositionSurface = brainCrossoverAbstractCompositionSurface
  ; semanticProfile = brainStructuralConsumerSemanticProfile
  }
