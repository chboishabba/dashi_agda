module DASHI.Reasoning.GrokkingGeometricCrystallisationMemoryRoutingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Biology.SpectralGrokkingLatticeExact as Spectral
import DASHI.Biology.SparseExpertRoutingCoalition as Sparse
import DASHI.Reasoning.FibreRoutingGrokkingMoEBrainCrossPollinationExact as Fibre
import DASHI.Cognition.PNF.FibreLearningDynamics as FibreLearning
import DASHI.Cognition.PNF.MemoryCommandSeparationExact as MemoryCommand
import DASHI.Cognition.PlatoCaveTraumaMemoryDecisionBridgeExact as Trauma
import DASHI.Reasoning.LilaWeylGrokkingFibreMaxCutExact as Lila

------------------------------------------------------------------------
-- GROKKING ~= GEOMETRIC CRYSTALLISATION / REFINEMENT HYPOTHESIS
--
-- Reuse-first synthesis only. Existing donors already own:
-- * memorisation -> circuit-formation -> cleanup phases;
-- * irregular-component removal + retained symmetry-adapted modes;
-- * sparse/context-relative expert routing;
-- * learning that may change which fibres carry a consumer;
-- * within-fibre reweight/rewire while public label + remembered event persist;
-- * memory-content != current action command;
-- * learned-history deformation of transition gates without deleting carrier.
--
-- The new claim is explicitly hypothesis-level: visible grokking may correspond
-- to a phase transition in which diffuse redundant representations become a
-- smaller, symmetry-adapted, specialised zoo of reusable fibres/operators, while
-- routing learns when/where to deploy them. Repeated FC/nonlinear stages are a
-- candidate mechanism for iterative cross-label/refinement, not a theorem here.
------------------------------------------------------------------------

record CrystallisationHypothesis : Set where
  constructor crystallisation-hypothesis
  field
    memorisationMayBeDiffuse : Bool
    circuitFormationMayCreateReusableOperators : Bool
    cleanupMayRemoveIrregularComponents : Bool
    symmetryAdaptedModesMayPersist : Bool
    routingMaySpecialiseWithLearning : Bool
    expertZooMayShrinkEffectiveActiveSet : Bool
    repeatedFCLayersMaySupportIterativeRefinement : Bool
    currentRepoProvesRepeatedFCLayersNecessary : Bool
open CrystallisationHypothesis public

canonicalCrystallisationHypothesis : CrystallisationHypothesis
canonicalCrystallisationHypothesis =
  crystallisation-hypothesis true true true true true true true false

cleanupRemovesIrregularComponentsAlreadyPaid :
  Spectral.irregularComponentCount Spectral.cleanupPhase ≡ 0
cleanupRemovesIrregularComponentsAlreadyPaid = Spectral.cleanupRemovesIrregularComponents

cleanupRetainsSymmetryModesAlreadyPaid :
  Spectral.symmetryAdaptedComponentCount Spectral.cleanupPhase ≡ 3
cleanupRetainsSymmetryModesAlreadyPaid = Spectral.cleanupRetainsThreeSymmetryModes

learningMayChangeCarryingFibresAlreadyPaid :
  Fibre.learningMayChangeWhichFibresCarryTheConsumer
    Fibre.canonicalFibreRoutingCrossPollinationBoundary ≡ true
learningMayChangeCarryingFibresAlreadyPaid = refl

sparseProductionAlreadyPaid :
  Sparse.sparseProductionTracked Sparse.canonicalSparseExpertCoalitionBoundary ≡ true
sparseProductionAlreadyPaid = refl

------------------------------------------------------------------------
-- Cross-label / refinement interpretation.
------------------------------------------------------------------------

record IterativeRefinementInterpretation : Set where
  constructor iterative-refinement-interpretation
  field
    samePublicLabelCanHideDifferentInternalTransitionGraph : Bool
    rememberedContentCanPersistAcrossReweighting : Bool
    presentCommandCanChangeWithoutErasingMemory : Bool
    learnedHistoryCanChangeAccessibleTransitions : Bool
    refinementRequiresErasure : Bool
open IterativeRefinementInterpretation public

canonicalIterativeRefinementInterpretation : IterativeRefinementInterpretation
canonicalIterativeRefinementInterpretation =
  iterative-refinement-interpretation true true true true false

learnedHistoryCanChangeGateWithoutDeletingCarrier :
  Trauma.learnedHistoryCanDeformTransitionGateWithoutDeletingCarrier
learnedHistoryCanChangeGateWithoutDeletingCarrier =
  Trauma.learnedHistoryCanDeformTransitionGateWithoutDeletingCarrier

------------------------------------------------------------------------
-- Polymer-animal / hyperfibre / operator-zoo interpretation.
--
-- A small reusable family can be composed/routed in many ways; this is not a
-- literal chemical-polymer or biological-species claim. It is a compression
-- hypothesis about reusable operators plus learned routing.
------------------------------------------------------------------------

record OperatorZooHypothesis : Set where
  constructor operator-zoo-hypothesis
  field
    reusableOperatorFamilyFiniteOrSmall : Bool
    compositionsCanGenerateLargeBehaviourFamily : Bool
    sameOperatorMayParticipateInMultipleFibres : Bool
    routerSelectsContextRelativeSubfamily : Bool
    expertIdentityEqualsSemanticMeaning : Bool
    transformerMoEEqualsBrainArchitecture : Bool
open OperatorZooHypothesis public

canonicalOperatorZooHypothesis : OperatorZooHypothesis
canonicalOperatorZooHypothesis =
  operator-zoo-hypothesis true true true true false false

------------------------------------------------------------------------
-- Experimental predictions.
------------------------------------------------------------------------

record CrystallisationExperimentFrontier : Set where
  constructor crystallisation-experiment-frontier
  field
    checkpointTrajectoriesRequired : Bool
    activationGeometryRequired : Bool
    routerEntropyOrSparsityRequired : Bool
    expertSpecialisationRequired : Bool
    operatorReuseAcrossTasksRequired : Bool
    interventionEquivarianceRequired : Bool
    temporalAlignmentWithGrokkingRequired : Bool
    memoryLikeRetentionVsCommandReweightAnalogueUseful : Bool
    severalFCLayerAblationRequired : Bool
    fibreDepthAblationRequired : Bool
    crystallisationAlreadyEmpiricallyEstablished : Bool
open CrystallisationExperimentFrontier public

currentCrystallisationExperimentFrontier : CrystallisationExperimentFrontier
currentCrystallisationExperimentFrontier =
  crystallisation-experiment-frontier
    true true true true true true true true true true false

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data SymmetryCleanupImpliesUniversalCrystallisation : Set where
data SparseRoutingImpliesLearnedRouter : Set where
data TraumaLearningAnalogyImpliesSameMechanism : Set where
data SeveralFCLayersAreNecessaryFromFormalism : Set where

symmetryCleanupDoesNotProveUniversalCrystallisation :
  SymmetryCleanupImpliesUniversalCrystallisation → ⊥
symmetryCleanupDoesNotProveUniversalCrystallisation ()

sparseRoutingDoesNotByItselfProveLearnedRouter :
  SparseRoutingImpliesLearnedRouter → ⊥
sparseRoutingDoesNotByItselfProveLearnedRouter ()

traumaLearningAnalogyDoesNotIdentifySameMechanism :
  TraumaLearningAnalogyImpliesSameMechanism → ⊥
traumaLearningAnalogyDoesNotIdentifySameMechanism ()

formalismDoesNotYetProveSeveralFCLayersNecessary :
  SeveralFCLayersAreNecessaryFromFormalism → ⊥
formalismDoesNotYetProveSeveralFCLayersNecessary ()
