module DASHI.ComputerScience.FlyStructureFunctionNDimFibreExact where

-- Fly structure/function NDim carrier.
--
-- This owner internalises the graph-colouring / RSA NDim lesson without
-- importing those branch-local modules: keep structurally distinct local
-- candidates separate, build a compatibility relation before composition, and
-- require the global consumer to validate the composed family. More axes are
-- candidate discrimination, not automatic predictive improvement.
--
-- A second boundary is now explicit: held-out PAIRS are not the same as held-
-- out REGIONS. If the same neuropil participates in both train and test pairs,
-- pairwise prediction does not establish generalization to unseen regions.

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Candidate structural fibres.
------------------------------------------------------------------------

data StructuralFibre : Set where
  directForward : StructuralFibre
  directReverse : StructuralFibre
  twoHopForward : StructuralFibre
  twoHopReverse : StructuralFibre
  commonInput : StructuralFibre
  commonOutput : StructuralFibre
  signedForward : StructuralFibre
  signedReverse : StructuralFibre

structuralFibreCount : Nat
structuralFibreCount = 8

record FibreCandidate : Set where
  constructor fibre-candidate
  field
    fibre : StructuralFibre
    hasTrainingVariation : Bool
    admittedByStructuralConsumer : Bool
open FibreCandidate public

------------------------------------------------------------------------
-- Compatibility is structural and precedes outcome fitting.
------------------------------------------------------------------------

data FibreConflictKind : Set where
  nearCollinearOnTrainingCarrier : FibreConflictKind
  duplicateRepresentation : FibreConflictKind
  consumerWrongType : FibreConflictKind

record FibreConflict : Set where
  constructor fibre-conflict
  field
    left : StructuralFibre
    right : StructuralFibre
    kind : FibreConflictKind
open FibreConflict public

record CompatibleFibreFamily : Set where
  constructor compatible-fibre-family
  field
    memberCount : Nat
    pairwiseConflictFree : Bool
    selectedWithoutHeldOutOutcome : Bool
    globalCompositionConstructed : Bool
open CompatibleFibreFamily public

------------------------------------------------------------------------
-- Ordered consumer pipeline.
------------------------------------------------------------------------

data StructureFunctionStage : Set where
  generateStructuralFibres : StructureFunctionStage
  restrictToTrainingCarrier : StructureFunctionStage
  buildFibreConflictGraph : StructureFunctionStage
  selectCompatibleFibreFamily : StructureFunctionStage
  fitCompositionOnTrainingPairs : StructureFunctionStage
  freezeComposition : StructureFunctionStage
  evaluateHeldOutPairs : StructureFunctionStage
  evaluateHeldOutRegions : StructureFunctionStage
  refitInsideNullReplicate : StructureFunctionStage
  compareAgainstNulls : StructureFunctionStage

firstStructureFunctionStage : StructureFunctionStage
firstStructureFunctionStage = generateStructuralFibres

record FlyNDimStructureFunctionBoundary : Set where
  constructor fly-ndim-structure-function-boundary
  field
    directedStructureKeptAsSeparateForwardReverseFibres : Bool
    symmetricFunctionalConsumerAcknowledged : Bool
    commonInputOutputKeptDistinctFromDirectedPaths : Bool
    signedFibresKeptDistinctUntilComposition : Bool
    compatibilitySelectionUsesHeldOutOutcomes : Bool
    compositionFitUsesHeldOutOutcomes : Bool
    pairHoldoutEquivalentToRegionHoldout : Bool
    heldOutRegionAppearsInRegionHoldoutTrainingPairs : Bool
    nullMayReuseObservedFitWithoutRefitting : Bool
    moreFibresAutomaticallyImprovePrediction : Bool
    pairwiseCompatibilityAutomaticallyImpliesHeldOutImprovement : Bool
    globalHeldOutEvaluationStillRequired : Bool
    unseenRegionEvaluationStillRequired : Bool
    nullComparisonStillRequired : Bool
open FlyNDimStructureFunctionBoundary public

canonicalFlyNDimStructureFunctionBoundary : FlyNDimStructureFunctionBoundary
canonicalFlyNDimStructureFunctionBoundary =
  fly-ndim-structure-function-boundary
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    true
    true
    true

------------------------------------------------------------------------
-- WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data DirectedEdgeEqualsSymmetricCorrelation : Set where

data MoreFibresImpliesBetterHeldoutPrediction : Set where

data LocalCompatibilityImpliesGlobalImprovement : Set where

data TrainingFitImpliesNullRejection : Set where

data SharedRegionImpliesSameNeuronIdentity : Set where

data PairHoldoutImpliesUnseenRegionGeneralization : Set where

data FrozenObservedFitIsValidPermutationNull : Set where

directedEdgeDoesNotCreateSymmetricCorrelation :
  DirectedEdgeEqualsSymmetricCorrelation → ⊥
directedEdgeDoesNotCreateSymmetricCorrelation ()

moreFibresDoNotCreateBetterHeldoutPrediction :
  MoreFibresImpliesBetterHeldoutPrediction → ⊥
moreFibresDoNotCreateBetterHeldoutPrediction ()

localCompatibilityDoesNotCreateGlobalImprovement :
  LocalCompatibilityImpliesGlobalImprovement → ⊥
localCompatibilityDoesNotCreateGlobalImprovement ()

trainingFitDoesNotCreateNullRejection :
  TrainingFitImpliesNullRejection → ⊥
trainingFitDoesNotCreateNullRejection ()

sharedRegionDoesNotCreateSameNeuronIdentity :
  SharedRegionImpliesSameNeuronIdentity → ⊥
sharedRegionDoesNotCreateSameNeuronIdentity ()

pairHoldoutDoesNotCreateUnseenRegionGeneralization :
  PairHoldoutImpliesUnseenRegionGeneralization → ⊥
pairHoldoutDoesNotCreateUnseenRegionGeneralization ()

frozenObservedFitDoesNotCreateValidPermutationNull :
  FrozenObservedFitIsValidPermutationNull → ⊥
frozenObservedFitDoesNotCreateValidPermutationNull ()

------------------------------------------------------------------------
-- Current empirical interpretation boundary.
--
-- Existing real pair-held-out run:
--   NDim fibre residual << path-aware residual < fixed three-weight residual
--   < direct residual.
-- This is retained as a real pair-level observation, not yet as unseen-region
-- generalization or null rejection. Region-blocked evaluation and refitted null
-- comparison remain separate consumers.
------------------------------------------------------------------------

record CurrentFlyNDimInterpretation : Set where
  constructor current-fly-ndim-interpretation
  field
    directOnlyCurrentlyBest : Bool
    pathAwareCurrentlyImprovesOnDirect : Bool
    fixedThreeWeightMixtureCurrentlyBeatsPath : Bool
    fixedThreeWeightMixtureIsCanonicalDASHI : Bool
    pairHeldoutNDimCurrentlyImprovesOnPath : Bool
    pairHeldoutImprovementEstablishesUnseenRegionGeneralization : Bool
    pairHeldoutImprovementEstablishesNullRejection : Bool
    ndimFibreFamilyRequiresRegionBlockedEvaluation : Bool
    ndimFibreFamilyRequiresRefittedNullEvaluation : Bool
open CurrentFlyNDimInterpretation public

currentFlyNDimInterpretation : CurrentFlyNDimInterpretation
currentFlyNDimInterpretation =
  current-fly-ndim-interpretation
    false
    true
    false
    false
    true
    false
    false
    true
    true
