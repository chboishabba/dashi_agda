#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round31.sh

files=(
  DASHI/Physics/YangMills/BalabanStrongCouplingLiteralQuaternionScalarBudgetExact.agda
  DASHI/Physics/YangMills/BalabanStrongCouplingLiteralQuaternionScalarYoungExact.agda
  DASHI/Physics/YangMills/BalabanStrongCouplingLiteralHessianBudgetAssemblyExact.agda
  DASHI/Physics/YangMills/YangMillsClayProblemContractExact.agda
  DASHI/Physics/YangMills/YangMillsConstructivePathPrePostInvariantExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound32ClayContractValidation.agda
)

doc=Docs/support/reference/YangMillsClayContractRound32.md

for file in "${files[@]}" "$doc"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "round thirty two contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'BalabanStrongCouplingLiteralQuaternionScalarBudgetExact.agda:nonnegativeSquareReflectsOrder'
  'BalabanStrongCouplingLiteralQuaternionScalarBudgetExact.agda:negativeScalarBelowYoung'
  'BalabanStrongCouplingLiteralQuaternionScalarBudgetExact.agda:placementWilsonScalarBelowYoungBudget'
  'BalabanStrongCouplingLiteralQuaternionScalarBudgetExact.agda:recursiveWilsonScalarSumBelowFourCharges'
  'BalabanStrongCouplingLiteralHessianBudgetAssemblyExact.agda:weightedPlaquetteAtomSumBelowBudget'
  'BalabanStrongCouplingLiteralHessianBudgetAssemblyExact.agda:literalGlobalHessianCoefficientFromAtoms'
  'BalabanStrongCouplingLiteralHessianBudgetAssemblyExact.agda:fourDimensionalSourceCoefficientExact'
  'YangMillsClayProblemContractExact.agda:clayPreconditionCountExact'
  'YangMillsClayProblemContractExact.agda:clayPostconditionCountExact'
  'YangMillsClayProblemContractExact.agda:clayInvariantCountExact'
  'YangMillsClayProblemContractExact.agda:finiteHessianIsNotClay'
  'YangMillsClayProblemContractExact.agda:allBetaLatticeGapIsNotClay'
  'YangMillsClayProblemContractExact.agda:singleGroupGapIsNotAllGroupsClay'
  'YangMillsConstructivePathPrePostInvariantExact.agda:kernelToTerminalInterfaceExact'
  'YangMillsConstructivePathPrePostInvariantExact.agda:terminalToPropagatorInterfaceExact'
  'YangMillsConstructivePathPrePostInvariantExact.agda:propagatorToRGInterfaceExact'
  'YangMillsConstructivePathPrePostInvariantExact.agda:rgToMeasureInterfaceExact'
  'YangMillsConstructivePathPrePostInvariantExact.agda:measureToContinuumInterfaceExact'
  'YangMillsConstructivePathPrePostInvariantExact.agda:continuumToGapInterfaceExact'
  'YangMillsConstructivePathPrePostInvariantExact.agda:gapToAllGroupsInterfaceExact'
  'YangMillsConstructivePathPrePostInvariantExact.agda:strongCouplingClusteringIsNotUltravioletControl'
  'YangMillsConstructivePathPrePostInvariantExact.agda:strongCouplingClusteringIsNotHamiltonianGap'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

grep -q '10.1007/s00220-022-04609-1' \
  DASHI/Physics/YangMills/BalabanStrongCouplingLiteralHessianBudgetAssemblyExact.agda
grep -q '10.1007/BF01215223' \
  DASHI/Physics/YangMills/YangMillsClayProblemContractExact.agda
grep -q 'No canonical inhabitant of ClayYangMillsSolution is supplied' \
  DASHI/Physics/YangMills/YangMillsClayProblemContractExact.agda
grep -q 'Route B does not by itself provide' \
  DASHI/Physics/YangMills/YangMillsConstructivePathPrePostInvariantExact.agda
grep -q 'The repository has \*\*not\*\* implemented a complete Clay solution' "$doc"
grep -q 'YangMillsClayProblemContractExact.agda' "$doc"
grep -q 'YangMillsConstructivePathPrePostInvariantExact.agda' "$doc"
grep -q '@startuml' "$doc"
grep -q 'A static pass is not a kernel pass' "$doc"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound32ClayContractValidation.agda
