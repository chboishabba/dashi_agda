#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_hhbad_scale_gain_round31.sh

files=(
  DASHI/Physics/Closure/NSTriadKNIndexedGluingRound32Exact.agda
  DASHI/Physics/Closure/NSTriadKNResourceLatticeRound32Exact.agda
  DASHI/Physics/Closure/NSTriadKNScaleTransitionRound32Exact.agda
  DASHI/Physics/Closure/NSTriadKNNineOwnerGridRound32Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoIndexedGluingResourceLatticeRound32Validation.agda
)

doc=docs/ns-clay-contract/ns-indexed-gluing-resource-lattice-round32.md

for file in "${files[@]}" "$doc"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|funext' "${files[@]}"; then
  echo "round thirty-two contains a hole, postulate, unsafe escape, trust primitive, or extensionality shortcut" >&2
  exit 1
fi

checks=(
  'NSTriadKNIndexedGluingRound32Exact.agda:glueExact'
  'NSTriadKNIndexedGluingRound32Exact.agda:transportedRepresentativeIsInternal'
  'NSTriadKNResourceLatticeRound32Exact.agda:remainderValuation'
  'NSTriadKNResourceLatticeRound32Exact.agda:noForbiddenValuation'
  'NSTriadKNResourceLatticeRound32Exact.agda:OwnerDerivation'
  'NSTriadKNScaleTransitionRound32Exact.agda:inverseScaleTransportAbsorbs'
  'NSTriadKNScaleTransitionRound32Exact.agda:physicalInverseScaleProducerConstructed = false'
  'NSTriadKNNineOwnerGridRound32Exact.agda:transposeMixedOwnerInvolutive'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/Closure/$file"
done

grep -q 'transporting its index, carrier, background, and resource valuation' "$doc"
grep -q 'does not prove the physical HH-bad producer' "$doc"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoIndexedGluingResourceLatticeRound32Validation.agda
