module DASHI.Interop.CrossDomainLevelTransportRegression where

------------------------------------------------------------------------
-- CROSS-DOMAIN LEVEL-TRANSPORT REGRESSION
--
-- Four independent repo lanes exercise the same carrier discipline without
-- being identified semantically:
--
--   brain       : a declared invariant survives coarse summary/extraction;
--   memory      : a learning step advances refinement depth while remembered
--                 PNF remains invariant;
--   pedagogy    : J+1 routes reviewed attention through safety/evidence return,
--                 not an automatic intervention;
--   atomics     : earlier/supplied or finite-analogue stages do not discharge
--                 later externally-open first-principles obligations.
--
-- The shared theorem shape is preservation-with-open-residual, not equality of
-- brain, learning, education, chemistry or governance carriers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ArgumentLevelTransportHyperformalismExact as Transport
import DASHI.Core.LevelIndexedProofObligationHyperformalismExact as Levelled
import DASHI.Interop.JPlusOne369FibreCarryHyperformalismExact as Broad
import Ontology.Brain.BrainInvariantDepth as Brain
import Ontology.Brain.BrainVocabularySurface as BrainVocabulary
import DASHI.Cognition.PNF.DepthWheelMemoryHyperfabric as Memory
import DASHI.Biology.PedagogicalJPlusOneRouting as Pedagogy
import DASHI.Physics.Foundations.AtomicGenerationPipelineExact as Atomics

------------------------------------------------------------------------
-- Brain: preserving one invariant does not claim full-state reconstruction.
------------------------------------------------------------------------

brainSummaryPreservesDeclaredDepth :
  ∀ {n} (state : BrainVocabulary.BrainState n) →
  Brain.stateDepth state ≡ Brain.summaryDepth (Brain.summarizeState state)
brainSummaryPreservesDeclaredDepth = Brain.state-summary-depth-exact

brainExtractionPreservesDeclaredDepth :
  ∀ {n} (state : BrainVocabulary.BrainState n) →
  Brain.stateDepth state ≡ Brain.extractionDepth (Brain.extractState state)
brainExtractionPreservesDeclaredDepth = Brain.state-extraction-depth-exact

------------------------------------------------------------------------
-- Memory: vertical learning motion at fixed public remembered PNF.
------------------------------------------------------------------------

memoryAdvancePreservesRememberedPNF :
  (update : Memory.MemoryPreservingUpdate) →
  (source : Memory.WheelMemoryFibre) →
  Memory.publicMemoryProjection (Memory.advancePreservingUpdate update source)
  ≡ Memory.publicMemoryProjection source
memoryAdvancePreservesRememberedPNF =
  Memory.advancePreservesRememberedPNF

memoryAdvanceMovesDepthByOne :
  (update : Memory.MemoryPreservingUpdate) →
  (source : Memory.WheelMemoryFibre) →
  Memory.refinementDepth (Memory.advancePreservingUpdate update source)
  ≡ suc (Memory.refinementDepth source)
memoryAdvanceMovesDepthByOne =
  Memory.advanceMovesDepth

oneLearningWheelMovesThreeDepthsAndKeepsPublicPNF :
  (program : Memory.ThreePhaseLearningProgram) →
  (source : Memory.WheelMemoryFibre) →
  Memory.refinementDepth (Memory.runOneLearningWheel program source)
    ≡ suc (suc (suc (Memory.refinementDepth source)))
  ×
  Memory.publicMemoryProjection (Memory.runOneLearningWheel program source)
    ≡ Memory.publicMemoryProjection source
oneLearningWheelMovesThreeDepthsAndKeepsPublicPNF program source =
  Memory.oneLearningWheelAdvancesDepthByThree program source
  ,
  Memory.oneLearningWheelPreservesRememberedPNF program source

------------------------------------------------------------------------
-- Pedagogy: J+1 is reviewed residual routing, not automatic promotion.
------------------------------------------------------------------------

pedagogicalJPlusOneRoutesAttention :
  Pedagogy.aiOutputRoutesAttention Pedagogy.canonicalPedagogicalJPlusOneRouting
  ≡ true
pedagogicalJPlusOneRoutesAttention =
  Pedagogy.aiOutputRoutesAttentionProof

pedagogicalJPlusOneIsNotAutomatic :
  Pedagogy.jPlusOneNotAutomatic Pedagogy.canonicalPedagogicalJPlusOneRouting
  ≡ true
pedagogicalJPlusOneIsNotAutomatic =
  Pedagogy.pedagogicalCandidateNotAutomaticIntervention

modelOutputCannotEqualIntervention :
  Pedagogy.AdmissibleJPlusOnePromotionRoute
    Pedagogy.modelOutputEqualsInterventionRoute →
  Pedagogy.Never
modelOutputCannotEqualIntervention =
  Pedagogy.modelOutputEqualsInterventionBlocked

------------------------------------------------------------------------
-- Atomics: obligation stages remain independently open.
------------------------------------------------------------------------

atomicEnumerationDoesNotSolveHamiltonian :
  Atomics.generatorAuthority Atomics.enumerateNuclearCharges
    ≡ Atomics.stageFiniteAnalogue
  ×
  Atomics.generatorAuthority Atomics.solveDeclaredHamiltonian
    ≡ Atomics.stageExternallyOpen
atomicEnumerationDoesNotSolveHamiltonian =
  Atomics.enumerationIsNotHamiltonianSolution

atomicObservablePredictionRemainsOpen :
  Atomics.generatorAuthority Atomics.predictObservableChemistry
  ≡ Atomics.stageExternallyOpen
atomicObservablePredictionRemainsOpen = refl

finiteAtomicScoreDoesNotPromoteQuantitativeChemistry :
  Atomics.AtomicGenerationBoundary.finiteInteractionScorePredictsQuantitativeChemistry
    Atomics.canonicalAtomicGenerationBoundary
  ≡ false
finiteAtomicScoreDoesNotPromoteQuantitativeChemistry =
  Atomics.AtomicGenerationBoundary.finiteInteractionScorePredictsQuantitativeChemistryIsFalse
    Atomics.canonicalAtomicGenerationBoundary

------------------------------------------------------------------------
-- Broader 369/J+1/carry receipts remain jointly visible.
------------------------------------------------------------------------

broadNonaryReceipt : Broad.H369.nonaryDimension ≡ 9
broadNonaryReceipt = Broad.threeByThreeIsNine

broadDialecticAddressReceipt :
  Broad.H369.dialecticDiscussionAtomDimension ≡ 27
broadDialecticAddressReceipt = Broad.threeCubedAddressIsTwentySeven

broadResidualRechartReceipt :
  Broad.Rechart.chart (Broad.Rechart.rechart Broad.Rechart.stateAtStar)
  ≡ Broad.Chart.chart 11
broadResidualRechartReceipt = Broad.residualGluingFailureRechartsToEleven

record CrossDomainLevelTransportBoundary : Set where
  constructor crossDomainLevelTransportBoundary
  field
    preservedBrainInvariantImpliesFullBrainIdentity : Bool
    rememberedPNFPreservationImpliesMemoryStateUnchanged : Bool
    pedagogicalJPlusOneIsAutomaticIntervention : Bool
    finiteAtomicStageDischargesOpenLaterStage : Bool
    commonTransportShapeIdentifiesDomainSemantics : Bool

canonicalCrossDomainLevelTransportBoundary : CrossDomainLevelTransportBoundary
canonicalCrossDomainLevelTransportBoundary =
  crossDomainLevelTransportBoundary false false false false false
