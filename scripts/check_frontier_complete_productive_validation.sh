#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_frontier_hodge_automorphic_spectral_round2.sh

files=(
  DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda
  DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveCompletionGateExact.agda
  DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveValidation.agda
  DASHI/EverythingFrontierCompleteProductiveValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

superseded=(
  DASHI/Physics/Constructive/FiniteProductClusteringExact.agda
  DASHI/Physics/YangMills/YangMillsFiniteOS2OS4KPBridgeExact.agda
  DASHI/Mathematics/AlgebraicGeometry/ProjectiveSpaceHodgePatternExact.agda
  DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeUniquenessExact.agda
  DASHI/Moonshine/RankOneHeisenbergFiniteWindowExact.agda
  .github/workflows/frontier-superseded-cleanup.yml
)

for file in "${superseded[@]}"; do
  if [[ -e "$file" ]]; then
    echo "superseded frontier draft remains present: $file" >&2
    exit 1
  fi
done

if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "complete productive frontier contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda:finiteKummerHomomorphism'
  'DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda:finiteKummerInjective'
  'DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda:finiteKummerSurjective'
  'DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda:finiteKummerKernelTrivial'
  'DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveCompletionGateExact.agda:allNamedProgrammeItemsHaveSubstantiveLocalResults'
  'DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveCompletionGateExact.agda:localTheoremIsNotOpenProblemClosure'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "$file"
done

grep -Fq '10.1007/978-0-387-09494-6' DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda
grep -Fq 'Square classes in' DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda
grep -Fq 'MissingGlobalClosure' DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveCompletionGateExact.agda
grep -Fq 'FrontierHodgeAutomorphicSpectralRound2Validation' DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveValidation.agda
grep -Fq 'EverythingFrontierHodgeAutomorphicSpectralRound2' DASHI/EverythingFrontierCompleteProductiveValidation.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/EverythingFrontierCompleteProductiveValidation.agda
