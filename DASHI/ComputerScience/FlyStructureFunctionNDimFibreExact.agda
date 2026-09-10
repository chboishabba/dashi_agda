module DASHI.ComputerScience.FlyStructureFunctionNDimFibreExact where

-- Fly structure/function NDim carrier.
--
-- This owner internalises the graph-colouring / RSA NDim lesson without
-- importing those branch-local modules: keep structurally distinct local
-- candidates separate, build a compatibility relation before composition, and
-- require the global consumer to validate the composed family. More axes are
-- candidate discrimination, not automatic predictive improvement.
--
-- A second boundary is explicit: held-out PAIRS are not the same as held-out
-- REGIONS. If the same neuropil participates in both train and test pairs,
-- pairwise prediction does not establish generalization to unseen regions.
--
-- A third boundary is now explicit after the first real LORO run: a low
-- leave-one-region-out residual and a suggestive permutation p-value still do
-- not establish that pair-specific connectome geometry is the source of the
-- gain. Fibre/weight stability and a null preserving coarse in/out strength and
-- source-level signed tendency are separate consumers.

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
  assessFoldwiseFibreStability : StructureFunctionStage
  refitInsideNullReplicate : StructureFunctionStage
  compareAgainstRegionLabelNull : StructureFunctionStage
  compareAgainstStrengthPreservingWiringNull : StructureFunctionStage

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
    foldwiseStabilityStillRequired : Bool
    regionLabelNullStillRequired : Bool
    coarseStrengthPreservingWiringNullStillRequired : Bool
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

data LowLOROResidualImpliesStableFibreMechanism : Set where

data RegionLabelNullTrendImpliesWiringGeometryMechanism : Set where

data CoarseStrengthEqualsPairSpecificWiring : Set where

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

lowLOROResidualDoesNotCreateStableFibreMechanism :
  LowLOROResidualImpliesStableFibreMechanism → ⊥
lowLOROResidualDoesNotCreateStableFibreMechanism ()

regionLabelTrendDoesNotCreateWiringGeometryMechanism :
  RegionLabelNullTrendImpliesWiringGeometryMechanism → ⊥
regionLabelTrendDoesNotCreateWiringGeometryMechanism ()

coarseStrengthDoesNotCreatePairSpecificWiring :
  CoarseStrengthEqualsPairSpecificWiring → ⊥
coarseStrengthDoesNotCreatePairSpecificWiring ()

------------------------------------------------------------------------
-- Current empirical interpretation boundary.
--
-- Real observations currently retained:
--   direct residual       ~ 0.3394
--   path residual         ~ 0.3081
--   fixed mixture         ~ 0.3104
--   pair-held-out NDim    ~ 0.1430
--   leave-one-region-out  ~ 0.1224
--   refitted LORO region-label permutation p ~ 0.099
--
-- The decimal values remain execution observations in the runtime JSON; this
-- Agda owner stores only the interpretation gates. In particular p < 0.10 is
-- not promoted to conventional significance or to a wiring-mechanism claim.
------------------------------------------------------------------------

record CurrentFlyNDimInterpretation : Set where
  constructor current-fly-ndim-interpretation
  field
    directOnlyCurrentlyBest : Bool
    pathAwareCurrentlyImprovesOnDirect : Bool
    fixedThreeWeightMixtureCurrentlyBeatsPath : Bool
    fixedThreeWeightMixtureIsCanonicalDASHI : Bool
    pairHeldoutNDimCurrentlyImprovesOnPath : Bool
    loroNDimCurrentlyImprovesOnPath : Bool
    loroNDimCurrentlyImprovesOnPairHeldoutResidual : Bool
    pairHeldoutImprovementEstablishesUnseenRegionGeneralization : Bool
    loroPermutationTrendIsConventionalNullRejection : Bool
    loroPermutationTrendEstablishesPairSpecificWiringMechanism : Bool
    foldwiseFibreStabilityPaid : Bool
    strengthPreservingWiringNullPaid : Bool
open CurrentFlyNDimInterpretation public

currentFlyNDimInterpretation : CurrentFlyNDimInterpretation
currentFlyNDimInterpretation =
  current-fly-ndim-interpretation
    false
    true
    false
    false
    true
    true
    true
    false
    false
    false
    false
    false
