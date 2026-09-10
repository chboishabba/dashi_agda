module DASHI.ComputerScience.FlyStructureFunctionNDimFibreExact where

-- Fly structure/function NDim carrier.
--
-- This owner internalises the graph-colouring / RSA NDim lesson without
-- importing those branch-local modules: keep structurally distinct local
-- candidates separate, build a compatibility relation before composition, and
-- require the global consumer to validate the composed family. More axes are
-- candidate discrimination, not automatic predictive improvement.
--
-- Held-out PAIRS are not the same as held-out REGIONS. If the same neuropil
-- participates in both train and test pairs, pairwise prediction does not
-- establish generalization to unseen regions.
--
-- The first real LORO run also separates a stable predictive fibre mechanism
-- from a topology-mechanism claim: a strength/polarity-preserving wiring null
-- must still be beaten before pair-specific mesoscale wiring is promoted.
--
-- Finally, the functional atlas itself is fibred. VFB JRC2018 supplies
-- overlapping painted domains/subdomains, so a unique-maximum atlas assignment
-- is a lossy consumer projection rather than source identity. The runtime now
-- retains an optional soft ROI->painted-domain carrier before any such collapse.

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
-- Functional atlas fibres.
------------------------------------------------------------------------

data FunctionalAtlasCarrier : Set where
  uniqueMaximumPaintedDomain : FunctionalAtlasCarrier
  overlappingPaintedDomainMembership : FunctionalAtlasCarrier

record FunctionalAtlasBoundary : Set where
  constructor functional-atlas-boundary
  field
    sourcePaintedDomainsMayOverlap : Bool
    sourceOverlapForcesMutuallyExclusiveIdentity : Bool
    uniqueMaximumCarrierRetainedForHistoricalComparison : Bool
    softOverlapCarrierPreservesMultipleDomainMemberships : Bool
    softMembershipRowsRenormalizedToPartitionUnity : Bool
    softCarrierStillDoesNotCreateNeuronIdentity : Bool
open FunctionalAtlasBoundary public

canonicalFunctionalAtlasBoundary : FunctionalAtlasBoundary
canonicalFunctionalAtlasBoundary =
  functional-atlas-boundary
    true
    false
    true
    true
    false
    true

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
  preserveFunctionalAtlasFibres : StructureFunctionStage
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
firstStructureFunctionStage = preserveFunctionalAtlasFibres

record FlyNDimStructureFunctionBoundary : Set where
  constructor fly-ndim-structure-function-boundary
  field
    directedStructureKeptAsSeparateForwardReverseFibres : Bool
    symmetricFunctionalConsumerAcknowledged : Bool
    commonInputOutputKeptDistinctFromDirectedPaths : Bool
    signedFibresKeptDistinctUntilComposition : Bool
    overlappingFunctionalDomainsKeptDistinctUntilConsumer : Bool
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
data OverlappingAtlasDomainsImplyUniqueRegionIdentity : Set where

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

overlappingAtlasDomainsDoNotCreateUniqueRegionIdentity :
  OverlappingAtlasDomainsImplyUniqueRegionIdentity → ⊥
overlappingAtlasDomainsDoNotCreateUniqueRegionIdentity ()

------------------------------------------------------------------------
-- Current empirical interpretation boundary.
--
-- Real observations currently retained in runtime outputs:
--   direct residual                    ~ 0.3394
--   path residual                      ~ 0.3081
--   fixed mixture                      ~ 0.3104
--   pair-held-out NDim                 ~ 0.1430
--   leave-one-region-out               ~ 0.1224
--   refitted LORO region-label p       ~ 0.0990
--   strength-preserving wiring null p  ~ 0.2376
--
-- Foldwise fibre selection/coefficients are now measured and largely stable;
-- that pays a stability consumer, not the stronger pair-specific wiring claim.
-- The strength-preserving null has also been executed but is not rejected.
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
    strengthPreservingWiringNullRejected : Bool
    pairSpecificWiringMechanismEstablished : Bool
    softFunctionalAtlasCarrierRequiresFreshBenchmark : Bool
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
    true
    true
    false
    false
    true
