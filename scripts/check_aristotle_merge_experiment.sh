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
  DASHI/Reasoning/AristotleMergeExperimentValidation.agda
  DASHI/Core/ExperimentalCoordinateDesignExact.agda
  DASHI/Core/DiscriminatorSynthesisExact.agda
  DASHI/Core/SequentialConsumerExperimentPlannerExact.agda
  DASHI/Core/ConsumerIndexedResidualRefinementExact.agda
  DASHI/Core/ResidualObserverDependencyExact.agda
  DASHI/Core/GovernedObservationProvenanceExact.agda
  DASHI/Core/ProofSearchLeastPrivilegeAdmissionExact.agda
  DASHI/Core/AdaptiveConsumerModelLoopExact.agda
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

scripts/run_agda29_parallel_check.sh DASHI/Reasoning/AristotleMergeExperimentValidation.agda
