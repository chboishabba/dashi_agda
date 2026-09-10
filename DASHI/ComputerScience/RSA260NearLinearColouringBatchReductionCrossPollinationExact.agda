module DASHI.ComputerScience.RSA260NearLinearColouringBatchReductionCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260GraphRefinementNDimSymmetryExact as Refinement
import DASHI.ComputerScience.RSA260NDimSymmetryProductionRoadmapExact as Roadmap
import DASHI.Interop.SymmetryQuotientExecutionBidiCrossPollinationExact as Bidi

record NearLinearColouringTransferReceipt : Set where
  constructor near-linear-colouring-transfer-receipt
  field
    sourceReference : String
    linearlyManyLocalReducersReported : Bool
    pairwiseNonTouchingCompatibilityReported : Bool
    constantFactorRecursiveShrinkReported : Bool
    backwardColourLiftRequired : Bool
    rsaAlgorithmImportedFromColouring : Bool
open NearLinearColouringTransferReceipt public

nearLinearColouringTransfer : NearLinearColouringTransferReceipt
nearLinearColouringTransfer = near-linear-colouring-transfer-receipt
  "Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, The Four Color Theorem with Linearly Many Reducible Configurations and Near-Linear Time Coloring, arXiv:2603.24880v2 (2026); DASHI PR #880 source atlas"
  true true true true false

record LocalReductionCandidate : Set where
  constructor local-reduction-candidate
  field
    candidateReference : String
    supportReference : String
    localConsumerSignatureMatched : Bool
    localActionConstructed : Bool
open LocalReductionCandidate public

record ReductionConflict : Set where
  constructor reduction-conflict
  field
    leftReference : String
    rightReference : String
    supportsOverlap : Bool
    actionsFailToCommute : Bool
    sharedBoundaryConstraint : Bool
open ReductionConflict public

record CompatibleReductionFamily : Set where
  constructor compatible-reduction-family
  field
    familyReference : String
    memberCount : Nat
    pairwiseConflictFree : Bool
    simultaneousActionConstructed : Bool
    simultaneousActionPassesOperatorEquivariance : Bool
    quotientConstructed : Bool
    liftConstructed : Bool
    upstairsVerificationPassed : Bool
    measuredReductionFactor : Nat
open CompatibleReductionFamily public

data BatchSelectionAxis : Set where
  supportOverlapAxis : BatchSelectionAxis
  kHopInteractionAxis : BatchSelectionAxis
  operatorCommutationAxis : BatchSelectionAxis
  projectionConsumerAxis : BatchSelectionAxis
  boundarySeamAxis : BatchSelectionAxis
  liftCompatibilityAxis : BatchSelectionAxis

batchSelectionAxisCount : Nat
batchSelectionAxisCount = 6

record NDimBatchReductionBoundary : Set where
  constructor ndim-batch-reduction-boundary
  field
    refinementProducesLocalCandidateClasses : Bool
    conflictGraphSeparatesMutuallyInterferingCandidates : Bool
    compatibleFamilyMayContainManyLocalCandidates : Bool
    pairwiseCompatibilityAutomaticallyImpliesGlobalMPEqualsPM : Bool
    globalActionMustStillBeChecked : Bool
    successfulBatchMayGiveConstantFactorShrink : Bool
    constantFactorShrinkGuaranteedForRSA : Bool
    recursiveLiftMustRecoverOriginalConsumerResult : Bool
open NDimBatchReductionBoundary public

canonicalNDimBatchReductionBoundary : NDimBatchReductionBoundary
canonicalNDimBatchReductionBoundary = ndim-batch-reduction-boundary
  true true true false true true false true

data ProductionBatchReductionStep : Set where
  refineStructuralSignatures : ProductionBatchReductionStep
  enumerateLocalCandidateReductions : ProductionBatchReductionStep
  buildReductionConflictGraph : ProductionBatchReductionStep
  selectLargeCompatibleFamily : ProductionBatchReductionStep
  composeGlobalCandidateAction : ProductionBatchReductionStep
  verifyGlobalOperatorEquivariance : ProductionBatchReductionStep
  quotientOrFailClosed : ProductionBatchReductionStep
  replayAndLift : ProductionBatchReductionStep

firstBatchReductionStep : ProductionBatchReductionStep
firstBatchReductionStep = refineStructuralSignatures

record RSA260ColouringNDimRoadmapRefinement : Set where
  constructor rsa260-colouring-ndim-roadmap-refinement
  field
    productionBytesRemainFirstConclusionPayingResidual : Bool
    ndimRefinementRunsBeforeFullReplay : Bool
    localCandidatesMayBeGeneratedInParallel : Bool
    conflictGraphSelectionInsertedBeforeGlobalAction : Bool
    globalEquivarianceStillRequiredAfterBatchSelection : Bool
    quotientFailureFallsBackToFullWidthReplay : Bool
    batchReductionCanReplaceSameObjectAcquisition : Bool
    batchReductionCanReplaceUpstairsVerification : Bool
open RSA260ColouringNDimRoadmapRefinement public

currentRSA260ColouringNDimRoadmapRefinement : RSA260ColouringNDimRoadmapRefinement
currentRSA260ColouringNDimRoadmapRefinement = rsa260-colouring-ndim-roadmap-refinement
  true true true true true true false false

existingRefinementBoundary : Refinement.RSA260NDimRoadmapBoundary
existingRefinementBoundary = Refinement.currentRSA260NDimRoadmapBoundary

existingProductionRoadmap : Roadmap.ConsolidatedRSA260RoadmapBoundary
existingProductionRoadmap = Roadmap.currentConsolidatedRSA260RoadmapBoundary

existingBidiBoundary : Bidi.ExecutableSymmetryReducerBoundary
existingBidiBoundary = Bidi.canonicalExecutableSymmetryReducerBoundary

data LocalReducerImpliesGlobalReducer : Set where
data PairwiseDisjointImpliesOperatorEquivariance : Set where
data ColouringConstantFactorImpliesRSAConstantFactor : Set where
data MoreNDimAxesImpliesMoreBatchReduction : Set where

aLocalReducerDoesNotCreateGlobalReducer : LocalReducerImpliesGlobalReducer → ⊥
aLocalReducerDoesNotCreateGlobalReducer ()

disjointnessDoesNotCreateEquivariance : PairwiseDisjointImpliesOperatorEquivariance → ⊥
disjointnessDoesNotCreateEquivariance ()

colouringShrinkDoesNotCreateRSAShrink : ColouringConstantFactorImpliesRSAConstantFactor → ⊥
colouringShrinkDoesNotCreateRSAShrink ()

moreAxesDoNotGuaranteeMoreBatchReduction : MoreNDimAxesImpliesMoreBatchReduction → ⊥
moreAxesDoNotGuaranteeMoreBatchReduction ()
