module DASHI.ComputerScience.RSA260NearLinearColouringBatchReductionCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260GraphRefinementNDimSymmetryExact as Refinement
import DASHI.ComputerScience.RSA260NDimSymmetryProductionRoadmapExact as Roadmap
import DASHI.Interop.SymmetryQuotientExecutionBidiCrossPollinationExact as Bidi

------------------------------------------------------------------------
-- NEAR-LINEAR 2D COLOURING -> RSA NDIM BATCH-REDUCTION CROSS-POLLINATION
--
-- The transferable algorithmic lesson from the 2026 Four-Color work is not
-- simply "find a local reducer".  It is:
--
--   many local reducible regions
--   -> construct a large pairwise-compatible family
--   -> apply that family simultaneously
--   -> obtain constant-factor global shrinkage
--   -> solve recursively
--   -> lift the result through every reduction.
--
-- In the RSA/NDim lane we retain this as a search architecture only.  Matrix
-- candidate orbit classes become local reduction candidates; a conflict graph
-- says which candidates cannot be composed simultaneously; only a compatible
-- family whose global action passes MP=PM may delete work.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Candidate-reduction conflict graph.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- NDIM role: generate candidate local regions and conflict coordinates.
--
-- More structural dimensions can refine candidate supports and conflict
-- predicates, but they do not themselves prove that a batch is admissible.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Revised production cut.
--
-- P2/P3 are refined into:
--   structural refinement
--   -> local reduction candidates
--   -> conflict graph
--   -> large compatible batch
--   -> one global equivariance test
--   -> quotient if paid.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Existing executable / roadmap boundaries retained.
------------------------------------------------------------------------

existingRefinementBoundary : Refinement.RSA260NDimRoadmapBoundary
existingRefinementBoundary = Refinement.currentRSA260NDimRoadmapBoundary

existingProductionRoadmap : Roadmap.RSA260NDimSymmetryProductionRoadmapBoundary
existingProductionRoadmap = Roadmap.currentRSA260NDimSymmetryProductionRoadmapBoundary

existingBidiBoundary : Bidi.SymmetryQuotientExecutionBoundary
existingBidiBoundary = Bidi.canonicalSymmetryQuotientExecutionBoundary

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

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
