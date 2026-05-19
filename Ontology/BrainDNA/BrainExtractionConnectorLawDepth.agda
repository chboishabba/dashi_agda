module Ontology.BrainDNA.BrainExtractionConnectorLawDepth where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.Brain.BrainInvariantDepth as InvariantDepth using
  (_⊎_; BrainInvariantDepthSurface; brainInvariantDepthSurface)
open import Ontology.BrainDNA.BrainExtractionConnectorSemantics as ExtractionSem using
  (BrainExtractionConnectorSemantics; BrainExtractionConnectorSemanticsSurface;
   brainExtractionConnectorSemanticsSurface; brainExtractionConnectorSemantics;
   brainExtractionConnectorSemanticsWidthStable;
   brainExtractionConnectorSemanticsOrderLineMajor;
   brainExtractionConnectorSemanticsAdmissibilityCoherent;
   brainExtractionConnectorSemanticsChemistryStructured;
   brainExtractionConnectorSemanticsHamiltonianStable)
open import Ontology.BrainDNA.BrainStructuralConsumerSemantics as ConsumerSem using
  (BrainStructuralConsumerSemanticProfile;
   BrainStructuralConsumerSemanticsSurface;
   brainStructuralConsumerSemanticsSurface;
   brainStructuralConsumerSemanticProfile;
   brainStructuralConsumerSemanticInvariantBounded;
   brainStructuralConsumerSemanticOrderLineMajor;
   brainStructuralConsumerSemanticWidthMatchesExtraction;
   brainStructuralConsumerSemanticAdmissibilityMatchesExtraction;
   brainStructuralConsumerSemanticCrossBandMatchesExtraction;
   brainStructuralConsumerSemanticHamiltonianMatchesExtraction;
   brainStructuralConsumerSemanticRecoveryBoundaryExact)
open import Ontology.BrainDNA.BrainCrossoverAbstractComposition as Abstract using
  (BrainCrossoverAbstractCompositionSurface;
   brainCrossoverAbstractCompositionSurface;
   BrainCrossoverAbstractProfile; brainCrossoverAbstractProfileOf;
   abstractRecoveryBoundaryExact)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Bounded law/depth surface over the current extraction-aware connector stack.
--
-- This remains theorem-thin and non-claiming. It does not add biological,
-- decoding, or closure claims. It only sharpens the local connector stack
-- by packaging the current extraction semantics, structural-consumer
-- semantics, invariant-depth source, and abstract crossover composition
-- into one exact law/depth profile on the existing carrier.

record BrainExtractionConnectorLawProfile : Set where
  constructor mkBrainExtractionConnectorLawProfile
  field
    invariantDepth : Nat
    order : ScanOrder
    emittedWidth : Nat
    emittedAdmissibility : Bool
    crossBand : Nat
    hamiltonian : Nat
    recoveryBoundary : Nat

brainExtractionConnectorLawProfile :
  ∀ {n} → BrainState n → BrainExtractionConnectorLawProfile
brainExtractionConnectorLawProfile st =
  mkBrainExtractionConnectorLawProfile
    (ExtractionSem.BrainExtractionConnectorSemanticsSurface.extractionInvariantDepth
      brainExtractionConnectorSemanticsSurface st)
    (ConsumerSem.BrainStructuralConsumerSemanticProfile.order
      (brainStructuralConsumerSemanticProfile st))
    (ConsumerSem.BrainStructuralConsumerSemanticProfile.emittedWidth
      (brainStructuralConsumerSemanticProfile st))
    (ConsumerSem.BrainStructuralConsumerSemanticProfile.emittedAdmissibility
      (brainStructuralConsumerSemanticProfile st))
    (ConsumerSem.BrainStructuralConsumerSemanticProfile.crossBand
      (brainStructuralConsumerSemanticProfile st))
    (ConsumerSem.BrainStructuralConsumerSemanticProfile.hamiltonian
      (brainStructuralConsumerSemanticProfile st))
    (ConsumerSem.BrainStructuralConsumerSemanticProfile.recoveryBoundary
      (brainStructuralConsumerSemanticProfile st))

brainExtractionConnectorLawDepthBounded :
  ∀ {n} (st : BrainState n) →
  (BrainExtractionConnectorLawProfile.invariantDepth
    (brainExtractionConnectorLawProfile st) ≡ zero)
  ⊎
  (BrainExtractionConnectorLawProfile.invariantDepth
    (brainExtractionConnectorLawProfile st) ≡ suc zero)
brainExtractionConnectorLawDepthBounded st =
  brainStructuralConsumerSemanticInvariantBounded st

brainExtractionConnectorLawOrderLineMajor :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorLawProfile.order
    (brainExtractionConnectorLawProfile st)
    ≡
  lineMajor
brainExtractionConnectorLawOrderLineMajor st =
  brainStructuralConsumerSemanticOrderLineMajor st

brainExtractionConnectorLawWidthMatchesExtraction :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorLawProfile.emittedWidth
    (brainExtractionConnectorLawProfile st)
    ≡
  ExtractionSem.BrainExtractionConnectorSemantics.emittedWidth
    (brainExtractionConnectorSemantics st)
brainExtractionConnectorLawWidthMatchesExtraction st =
  brainStructuralConsumerSemanticWidthMatchesExtraction st

brainExtractionConnectorLawAdmissibilityMatchesExtraction :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorLawProfile.emittedAdmissibility
    (brainExtractionConnectorLawProfile st)
    ≡
  ExtractionSem.BrainExtractionConnectorSemantics.emittedAdmissibility
    (brainExtractionConnectorSemantics st)
brainExtractionConnectorLawAdmissibilityMatchesExtraction st =
  brainStructuralConsumerSemanticAdmissibilityMatchesExtraction st

brainExtractionConnectorLawCrossBandMatchesExtraction :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorLawProfile.crossBand
    (brainExtractionConnectorLawProfile st)
    ≡
  ExtractionSem.BrainExtractionConnectorSemantics.crossBand
    (brainExtractionConnectorSemantics st)
brainExtractionConnectorLawCrossBandMatchesExtraction st =
  brainStructuralConsumerSemanticCrossBandMatchesExtraction st

brainExtractionConnectorLawHamiltonianMatchesExtraction :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorLawProfile.hamiltonian
    (brainExtractionConnectorLawProfile st)
    ≡
  ExtractionSem.BrainExtractionConnectorSemantics.hamiltonian
    (brainExtractionConnectorSemantics st)
brainExtractionConnectorLawHamiltonianMatchesExtraction st =
  brainStructuralConsumerSemanticHamiltonianMatchesExtraction st

brainExtractionConnectorLawRecoveryBoundaryExact :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorLawProfile.recoveryBoundary
    (brainExtractionConnectorLawProfile st)
    ≡
  3
brainExtractionConnectorLawRecoveryBoundaryExact st =
  brainStructuralConsumerSemanticRecoveryBoundaryExact st

brainExtractionConnectorLawRecoveryBoundaryMatchesAbstract :
  ∀ {n} (st : BrainState n) →
  BrainExtractionConnectorLawProfile.recoveryBoundary
    (brainExtractionConnectorLawProfile st)
    ≡
  Abstract.BrainCrossoverAbstractProfile.recoveryBoundary
    (brainCrossoverAbstractProfileOf st)
brainExtractionConnectorLawRecoveryBoundaryMatchesAbstract st = refl

record BrainExtractionConnectorLawDepthSurface : Set₂ where
  field
    invariantDepthSurface : BrainInvariantDepthSurface
    extractionConnectorSemantics : BrainExtractionConnectorSemanticsSurface
    structuralConsumerSemantics : BrainStructuralConsumerSemanticsSurface
    abstractCompositionSurface : BrainCrossoverAbstractCompositionSurface
    lawProfile : ∀ {n} → BrainState n → BrainExtractionConnectorLawProfile

brainExtractionConnectorLawDepthSurface :
  BrainExtractionConnectorLawDepthSurface
brainExtractionConnectorLawDepthSurface = record
  { invariantDepthSurface = brainInvariantDepthSurface
  ; extractionConnectorSemantics = brainExtractionConnectorSemanticsSurface
  ; structuralConsumerSemantics = brainStructuralConsumerSemanticsSurface
  ; abstractCompositionSurface = brainCrossoverAbstractCompositionSurface
  ; lawProfile = brainExtractionConnectorLawProfile
  }
