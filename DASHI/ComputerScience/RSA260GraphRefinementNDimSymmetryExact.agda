module DASHI.ComputerScience.RSA260GraphRefinementNDimSymmetryExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.ComputerScience.RSA260SymmetryCensusOrbitQuotientBidiExact as Bidi
import DASHI.ComputerScience.RSA260ShorColouring369MonsterSymmetrySearchExact as Search

------------------------------------------------------------------------
-- GRAPH-REFINEMENT / N-DIMENSIONAL SYMMETRY CANDIDATE EXECUTION
--
-- Candidate coordinates are refined simultaneously by several declared
-- structural consumers:
--   row degree, column degree, diagonal bit,
--   outgoing-neighbour colour multiset,
--   incoming-neighbour colour multiset.
--
-- This is N-dimensional in the same sense as the existing Pareto owner:
-- dimension is a declared axis family, not candidate count or visual size.
-- Equal refinement colour is only a candidate orbit. Exact MP=PM remains the
-- promotion gate.
------------------------------------------------------------------------

data StructuralAxis : Set where
  rowDegreeAxis : StructuralAxis
  columnDegreeAxis : StructuralAxis
  diagonalAxis : StructuralAxis
  outgoingNeighbourAxis : StructuralAxis
  incomingNeighbourAxis : StructuralAxis

structuralAxisCount : Nat
structuralAxisCount = 5

record GraphRefinementExecutionReceipt : Set where
  constructor graph-refinement-execution-receipt
  field
    logicalWidth : Nat
    structuralAxes : Nat
    genericRefinementRounds : Nat
    genericColourClasses : Nat
    genericSingletonClasses : Nat
    genericPairClasses : Nat
    genericNontrivialQuotientCandidate : Bool
    pairBenchmarkRefinementRounds : Nat
    pairBenchmarkColourClasses : Nat
    pairBenchmarkPairClasses : Nat
    individualPairSwapsCommuting : Nat
    globalPairSwapCommuting : Bool
    exactGitBlobExecuted : Bool
    sourceEquivalentExecutionPassed : Bool
open GraphRefinementExecutionReceipt public

currentGraphRefinementExecutionReceipt : GraphRefinementExecutionReceipt
currentGraphRefinementExecutionReceipt =
  graph-refinement-execution-receipt
    256 5
    2 256 256 0 false
    64 128 128 0 true
    false true

------------------------------------------------------------------------
-- Key lesson: local structural indistinguishability does not mean each local
-- transposition is an automorphism.  The 128 pair classes only become a valid
-- action when composed into the global pair swap and checked against M.
------------------------------------------------------------------------

record NDimSymmetryInterpretationBoundary : Set where
  constructor ndim-symmetry-interpretation-boundary
  field
    dimensionIsDeclaredStructuralAxisFamily : Bool
    refinementMayIntersectSeveralConsumerEquivalences : Bool
    equalLocalSignaturesAutomaticallyGiveAutomorphism : Bool
    globalCompositionMayBeValidWhenLocalMovesAreNot : Bool
    exactOperatorEquivarianceStillRequired : Bool
    higherDimensionAutomaticallyReducesCarrier : Bool
    higherDimensionCanImproveCandidateDiscrimination : Bool
open NDimSymmetryInterpretationBoundary public

canonicalNDimSymmetryInterpretationBoundary : NDimSymmetryInterpretationBoundary
canonicalNDimSymmetryInterpretationBoundary =
  ndim-symmetry-interpretation-boundary
    true true false true true false true

------------------------------------------------------------------------
-- Bidi cross-pollination back to graph colouring / pants:
-- local reducibility / equal colour class != globally admissible simultaneous
-- reduction. Compatibility and the global consumer are the deciding gates.
------------------------------------------------------------------------

record LocalToGlobalReductionBoundary : Set where
  constructor local-to-global-reduction-boundary
  field
    genericCarrierRefinesToNoNontrivialClasses : Bool
    symmetricCarrierRefinesToOrbitPairs : Bool
    eachOrbitPairIndividuallySwappable : Bool
    simultaneousOrbitActionValid : Bool
    quotientLiftAlreadyExecutable : Bool
    colouringCompatibilityAnalogyHasExecutableMatrixWitness : Bool
open LocalToGlobalReductionBoundary public

canonicalLocalToGlobalReductionBoundary : LocalToGlobalReductionBoundary
canonicalLocalToGlobalReductionBoundary =
  local-to-global-reduction-boundary
    true true false true true true

------------------------------------------------------------------------
-- Roadmap effect.
--
-- Production acquisition remains conclusion-paying. Once the production
-- matrix is acquired, graph refinement is now a concrete pre-replay pass:
--
--   bytes -> structural refinement -> candidate orbit action -> MP=PM
--         -> quotient if qualified -> CPU replay -> lift/upstairs verify.
------------------------------------------------------------------------

data ProductionSymmetryStep : Set where
  refineProductionCoordinates : ProductionSymmetryStep
  constructCandidateActions : ProductionSymmetryStep
  verifyProductionEquivariance : ProductionSymmetryStep
  quotientProductionOperator : ProductionSymmetryStep
  replayReducedKrylov : ProductionSymmetryStep
  liftAndVerifyProductionKernel : ProductionSymmetryStep

firstProductionSymmetryStep : ProductionSymmetryStep
firstProductionSymmetryStep = refineProductionCoordinates

record RSA260NDimRoadmapBoundary : Set where
  constructor rsa260-ndim-roadmap-boundary
  field
    syntheticGraphRefinementPaid : Bool
    syntheticPositiveOrbitRecoveryPaid : Bool
    syntheticNegativeNoOrbitCasePaid : Bool
    productionBytesAcquired : Bool
    productionGraphRefinementRun : Bool
    productionCommutingActionFound : Bool
    productionQuotientReplayRun : Bool
    productionLiftVerified : Bool
    ndimIsCandidateDiscriminatorNotAutomaticReducer : Bool
open RSA260NDimRoadmapBoundary public

currentRSA260NDimRoadmapBoundary : RSA260NDimRoadmapBoundary
currentRSA260NDimRoadmapBoundary =
  rsa260-ndim-roadmap-boundary
    true true true
    false false false false false
    true

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SameRefinementColourImpliesAutomorphism : Set where
data MoreAxesImpliesMoreCompression : Set where
data LocalSwapImpliesGlobalSwap : Set where
data GraphPartitionImpliesOperatorQuotient : Set where

sameColourDoesNotCreateAutomorphism : SameRefinementColourImpliesAutomorphism → ⊥
sameColourDoesNotCreateAutomorphism ()

moreAxesDoNotGuaranteeCompression : MoreAxesImpliesMoreCompression → ⊥
moreAxesDoNotGuaranteeCompression ()

localSwapDoesNotCreateGlobalSwap : LocalSwapImpliesGlobalSwap → ⊥
localSwapDoesNotCreateGlobalSwap ()

graphPartitionDoesNotCreateOperatorQuotient : GraphPartitionImpliesOperatorQuotient → ⊥
graphPartitionDoesNotCreateOperatorQuotient ()

existingNDimBoundary : NDim.NDimParetoHyperfabricBoundary
existingNDimBoundary = NDim.canonicalNDimParetoHyperfabricBoundary

existingSymmetrySearchBoundary : Search.RSA260SymmetryResearchRoadmapBoundary
existingSymmetrySearchBoundary = Search.currentRSA260SymmetryResearchRoadmapBoundary

existingBidiRoadmap : Bidi.RSA260SymmetryExecutionRoadmapBoundary
existingBidiRoadmap = Bidi.currentRSA260SymmetryExecutionRoadmapBoundary
