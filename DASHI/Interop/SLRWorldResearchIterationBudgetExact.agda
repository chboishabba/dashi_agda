module DASHI.Interop.SLRWorldResearchIterationBudgetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRSemanticWorldClosureExact as Closure
import DASHI.Interop.SLRWorldResearchTrancheConvergenceExact as Tranche

------------------------------------------------------------------------
-- BOUNDED EXECUTABLE WORLD-RESEARCH ITERATION
--
-- Runtime:
--   tools/slr-discourse-reconstruct/slr_world_research_budget.py
--   tools/slr-discourse-reconstruct/slr_world_research_gap_flow.py
--   tools/slr-discourse-reconstruct/run_world_research_budgeted_round.sh
--   tools/slr-discourse-reconstruct/run_world_research_loop.sh
--
-- The semantic closure emits A(t+1).  This owner constrains execution of that
-- frontier: deterministic deduplication, Pareto ranking over independent
-- semantic-support coordinates, separate missing-surface and new-QID budgets,
-- append-only attempt history, finite iteration and total-new-atom ceilings,
-- and explicit old-gap contraction/new-gap opening accounting.
------------------------------------------------------------------------

record WorldResearchIterationBudget : Set where
  constructor worldResearchIterationBudget
  field
    maxIterations : Nat
    maxNewQidsPerIteration : Nat
    maxMissingSurfacesPerIteration : Nat
    maxTotalNewAtoms : Nat
    missingSurfaceAttemptsAppendOnly : Bool
    missingSurfaceMayRetryForeverWithinOneLoop : Bool
    missingSurfaceRanksBeforeRelatedQid : Bool
    missingAndQidBudgetsAreSeparate : Bool
    relatedQidSelectionUsesParetoFronts : Bool
    paretoDimensionsScalarized : Bool
    qidLexicalOrderIsEpistemicPriority : Bool
    frontierRankIsTruthRank : Bool
    budgetExhaustionIsConsumerClosure : Bool
    noWorldGrowthMayStopLoop : Bool
    frontierEmptyMayStopLoop : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open WorldResearchIterationBudget public

canonicalWorldResearchIterationBudget : WorldResearchIterationBudget
canonicalWorldResearchIterationBudget =
  worldResearchIterationBudget
    3 8 4 5000
    true false true true
    true false false false false
    true true true false

record GapFlowReceipt : Set where
  constructor gapFlowReceipt
  field
    schemaReference : String
    priorGapReference : String
    contractedGapReference : String
    persistingGapReference : String
    newGapReference : String
    netGapDeltaReference : String
    priorObligationReference : String
    retiredObligationReference : String
    persistingObligationReference : String
    newObligationReference : String
    selectedQidAtomYieldReference : String
    netGapGrowthImpliesNoContraction : Bool
    gapContractionCreatesClaimTruth : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open GapFlowReceipt public

canonicalGapFlowReceipt : GapFlowReceipt
canonicalGapFlowReceipt =
  gapFlowReceipt
    "slr-world-research-gap-flow-v1"
    "prior_gap_atoms"
    "contracted_gap_atoms"
    "persisting_gap_atoms"
    "new_gap_atoms"
    "net_gap_delta"
    "prior_obligations"
    "retired_obligations"
    "persisting_obligations"
    "new_obligations"
    "atoms_added_per_selected_qid"
    false false true false

record BudgetedRoundReceipt : Set where
  constructor budgetedRoundReceipt
  field
    schemaReference : String
    selectedMissingSurfaceReference : String
    selectedRelatedQidReference : String
    paretoFrontReference : String
    qidNodesAddedReference : String
    atomsAddedReference : String
    semanticGapReference : String
    gapFlowReference : String
    remainingObligationReference : String
    stopReasonReference : String
    consumerClosurePaid : Bool
    budgetExhaustionCreatesClosure : Bool
    targetSurfaceAssertionRewritten : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open BudgetedRoundReceipt public

canonicalBudgetedRoundReceipt : BudgetedRoundReceipt
canonicalBudgetedRoundReceipt =
  budgetedRoundReceipt
    "slr-world-research-iteration-v1"
    "selected_missing_surfaces"
    "selected_related_qids"
    "pareto_front_rank"
    "qid_nodes_added_this_round"
    "atoms_added_this_round"
    "semantic_gap_atoms"
    "semantic_gap_flow_reference"
    "next_acquisition_obligations"
    "round_stop_reason"
    false false false true false

record WorldResearchLoopReceipt : Set where
  constructor worldResearchLoopReceipt
  field
    schemaReference : String
    roundsRunReference : String
    totalNewAtomsReference : String
    finalGapReference : String
    finalObligationReference : String
    stopReasonReference : String
    consumerClosurePaid : Bool
    budgetExhaustionCreatesClosure : Bool
    frontierRankCreatesTruthRank : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open WorldResearchLoopReceipt public

canonicalWorldResearchLoopReceipt : WorldResearchLoopReceipt
canonicalWorldResearchLoopReceipt =
  worldResearchLoopReceipt
    "slr-world-research-loop-v1"
    "rounds_run"
    "total_new_atoms"
    "final_semantic_gap_atoms"
    "final_acquisition_obligations"
    "stop_reason"
    false false false true false

semanticClosureAnchor : Closure.SemanticClosureBoundary
semanticClosureAnchor = Closure.canonicalSemanticClosureBoundary

trancheIterationAnchor : Tranche.WorldResearchIterationBoundary
trancheIterationAnchor = Tranche.canonicalWorldResearchIterationBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FrontierRankIsTruthRank : Set where
data BudgetExhaustionPaysConsumerClosure : Set where
data MissingSurfaceMayRetryForever : Set where
data BoundedLoopCreatesSemanticPromotion : Set where
data NoProgressCreatesTruth : Set where
data ParetoFrontRequiresScalarAlpha : Set where
data QidLexicalOrderCreatesEpistemicPriority : Set where
data NetGapGrowthMeansNoOldGapContracted : Set where
data GapContractionCreatesClaimTruth : Set where

frontierRankDoesNotCreateTruthRank : FrontierRankIsTruthRank → ⊥
frontierRankDoesNotCreateTruthRank ()

budgetExhaustionDoesNotPayConsumerClosure : BudgetExhaustionPaysConsumerClosure → ⊥
budgetExhaustionDoesNotPayConsumerClosure ()

missingSurfaceAttemptIsBounded : MissingSurfaceMayRetryForever → ⊥
missingSurfaceAttemptIsBounded ()

boundedLoopDoesNotCreateSemanticPromotion : BoundedLoopCreatesSemanticPromotion → ⊥
boundedLoopDoesNotCreateSemanticPromotion ()

noProgressDoesNotCreateTruth : NoProgressCreatesTruth → ⊥
noProgressDoesNotCreateTruth ()

paretoFrontDoesNotRequireScalarAlpha : ParetoFrontRequiresScalarAlpha → ⊥
paretoFrontDoesNotRequireScalarAlpha ()

qidLexicalOrderDoesNotCreatePriority : QidLexicalOrderCreatesEpistemicPriority → ⊥
qidLexicalOrderDoesNotCreatePriority ()

netGapGrowthDoesNotEraseContraction : NetGapGrowthMeansNoOldGapContracted → ⊥
netGapGrowthDoesNotEraseContraction ()

gapContractionDoesNotCreateClaimTruth : GapContractionCreatesClaimTruth → ⊥
gapContractionDoesNotCreateClaimTruth ()
