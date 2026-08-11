#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_physical_galerkin_flow_round30.sh

files=(
  DASHI/Physics/Closure/NSTriadKNHHBadTimeScaleGainRound31Exact.agda
  DASHI/Physics/Closure/NSTriadKNSameCarrierSameObjectRound31Exact.agda
  DASHI/Physics/Closure/NSTriadKNAdmissibleRemainderGrammarRound31Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHHBadScaleGainRound31Validation.agda
)

doc=docs/ns-clay-contract/ns-hhbad-scale-gain-round31.md

for file in "${files[@]}" "$doc"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|funext' "${files[@]}"; then
  echo "round thirty-one contains a hole, postulate, unsafe escape, trust primitive, or extensionality shortcut" >&2
  exit 1
fi

checks=(
  'NSTriadKNHHBadTimeScaleGainRound31Exact.agda:timeScaleGainAbsorbsRawBernstein'
  'NSTriadKNHHBadTimeScaleGainRound31Exact.agda:finiteTimeLocalizedHHBadAbsorption'
  'NSTriadKNHHBadTimeScaleGainRound31Exact.agda:criticalOccupationRepairsExactlyOneScale'
  'NSTriadKNHHBadTimeScaleGainRound31Exact.agda:viscousAmplitudeGainAbsorbsHHBad'
  'NSTriadKNSameCarrierSameObjectRound31Exact.agda:positiveVelocityExact'
  'NSTriadKNSameCarrierSameObjectRound31Exact.agda:negativeVelocityExact'
  'NSTriadKNSameCarrierSameObjectRound31Exact.agda:retainedModesExact'
  'NSTriadKNSameCarrierSameObjectRound31Exact.agda:sameObjectPhysicalGalerkinVectorField'
  'NSTriadKNAdmissibleRemainderGrammarRound31Exact.agda:remainderNormalForm'
  'NSTriadKNAdmissibleRemainderGrammarRound31Exact.agda:compileGrammarOwnerEstimate'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/Closure/$file"
done

grep -q '10.1007/s00021-014-0167-4' \
  DASHI/Physics/Closure/NSTriadKNHHBadTimeScaleGainRound31Exact.agda
grep -q '10.1512/iumj.1993.42.42034' \
  DASHI/Physics/Closure/NSTriadKNHHBadTimeScaleGainRound31Exact.agda
grep -q '10.1002/cpa.3160370205' \
  DASHI/Physics/Closure/NSTriadKNAdmissibleRemainderGrammarRound31Exact.agda
grep -q 'tau_q' "$doc"
grep -q 'same-carrier' "$doc"
grep -q 'uncontrolled BKM' "$doc"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoHHBadScaleGainRound31Validation.agda
