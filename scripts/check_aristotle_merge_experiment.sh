#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Reasoning/AristotleMCGSHypergraphExact.agda
  DASHI/Reasoning/AristotleMCGSIntrospectiveSpecimen.agda
  DASHI/Reasoning/AristotleMCGSRecoveredWitness.agda
  DASHI/Reasoning/AristotleBranchMergeExact.agda
  DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda
  DASHI/Reasoning/AristotleMergeGovernanceCrossPollinationExact.agda
  DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda
  DASHI/Reasoning/AristotleActiveExperimentalProofSearchDynamicsExact.agda
  DASHI/Reasoning/AristotleMergeExperimentValidation.agda
  DASHI/Core/ExperimentalCoordinateDesignExact.agda
  DASHI/Core/DiscriminatorSynthesisExact.agda
  DASHI/Core/SequentialConsumerExperimentPlannerExact.agda
  DASHI/Core/ConsumerIndexedResidualRefinementExact.agda
  DASHI/Core/ResidualObserverDependencyExact.agda
  DASHI/Core/GovernedObservationProvenanceExact.agda
  DASHI/Core/ProofSearchLeastPrivilegeAdmissionExact.agda
  DASHI/Core/AdaptiveConsumerModelLoopExact.agda
  DASHI/Core/AffectedDependencyClosureExact.agda
  DASHI/Core/HistoryConditionedChoiceExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required Aristotle merge/experiment source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^data MergeStrategy' DASHI/Reasoning/AristotleBranchMergeExact.agda
grep -q '^joinKnowledge :' DASHI/Reasoning/AristotleBranchMergeExact.agda
grep -q '^fastForwardMerge :' DASHI/Reasoning/AristotleBranchMergeExact.agda
grep -q '^record ThreeWayMergeReceipt' DASHI/Reasoning/AristotleBranchMergeExact.agda
grep -q '^guardedMerge :' DASHI/Reasoning/AristotleBranchMergeExact.agda
grep -q '^sameObservedStateIsInsufficientForHiddenDependencyMerge :' DASHI/Reasoning/AristotleBranchMergeExact.agda
grep -q '^sameObservedStateIsInsufficientForProvenanceMerge :' DASHI/Reasoning/AristotleBranchMergeExact.agda
grep -q '^lemmaASurvivesCompatibleMerge :' DASHI/Reasoning/AristotleBranchMergeExact.agda
grep -q '^lemmaBSurvivesCompatibleMerge :' DASHI/Reasoning/AristotleBranchMergeExact.agda
grep -q 'mergeCalculusIsClaimedByAristotlePaperIsFalse' DASHI/Reasoning/AristotleBranchMergeExact.agda

grep -q '^data BranchWorld' DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda
grep -q '^snapshotOf :' DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda
grep -q '^mergeDecisionResidualRepair :' DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda
grep -q '^coarseObserverCannotCloseMergeDecision :' DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda
grep -q '^dependencyProbe :' DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda
grep -q '^provenanceProbe :' DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda
grep -q '^dependencyThenProvenancePlan :' DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda
grep -q '^guardProbePlan :' DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda
grep -q '^hiddenResidualDependencyDemandsRefinement :' DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda
grep -q 'nextProofSearchProbeMayDependOnOutcomeIsTrue' DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda
grep -q 'proofSearchIsClaimedToBeLiteralPhysicalExperimentIsFalse' DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda

grep -q '^eraseThenAddProducesIntroducedMergeLineage :' DASHI/Reasoning/AristotleMergeGovernanceCrossPollinationExact.agda
grep -q '^eraseThenAddCannotAuthorizeInheritedMergeLineage :' DASHI/Reasoning/AristotleMergeGovernanceCrossPollinationExact.agda
grep -q '^record AdmittedGuardedMerge' DASHI/Reasoning/AristotleMergeGovernanceCrossPollinationExact.agda
grep -q '^canonicalAdmittedMergeHasLiveRoute :' DASHI/Reasoning/AristotleMergeGovernanceCrossPollinationExact.agda
grep -q 'mergeGuardAutomaticallySuppliesRouteAdmissionIsFalse' DASHI/Reasoning/AristotleMergeGovernanceCrossPollinationExact.agda

grep -q '^proofSearchCoordinateDesign :' DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda
grep -q '^historySensitiveMergeWitness :' DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda
grep -q '^record CollisionReceipt' DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda
grep -q '^record DiscriminatorReceipt' DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda
grep -q '^record ObservationReceipt' DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda
grep -q '^record RefinementReceipt' DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda
grep -q '^changedDependencyReopensConsumer :' DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda
grep -q '^selectiveConsumerReopening :' DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda
grep -q '^record ActiveExperimentalProofSearchLoop' DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda
grep -q '^canonicalActiveExperimentalProofSearchLoop :' DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda
grep -q 'activeExperimentalLoopIsClaimedByAristotlePaperIsFalse' DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda

grep -q '^data LoopTransition' DASHI/Reasoning/AristotleActiveExperimentalProofSearchDynamicsExact.agda
grep -q '^data LoopPath' DASHI/Reasoning/AristotleActiveExperimentalProofSearchDynamicsExact.agda
grep -q '^canonicalOneIterationCycle :' DASHI/Reasoning/AristotleActiveExperimentalProofSearchDynamicsExact.agda
grep -q '^canonicalClosurePath :' DASHI/Reasoning/AristotleActiveExperimentalProofSearchDynamicsExact.agda
grep -q '^record ActiveSearchDynamicsReceipt' DASHI/Reasoning/AristotleActiveExperimentalProofSearchDynamicsExact.agda
grep -q 'refinedConsumerClosureCanTerminateSearchIsTrue' DASHI/Reasoning/AristotleActiveExperimentalProofSearchDynamicsExact.agda

scripts/run_agda29_parallel_check.sh DASHI/Reasoning/AristotleMergeExperimentValidation.agda
