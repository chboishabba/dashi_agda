#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_indexed_gluing_resource_lattice_round32.sh

files=(
  DASHI/Physics/Closure/NSTriadKNSameObjectLookupConsistencyRound33Exact.agda
  DASHI/Physics/Closure/NSTriadKNHHBadSharpDyadicGainRound33Exact.agda
  DASHI/Physics/Closure/NSTriadKNNineOwnerResourceReserveRound33Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSameObjectSharpGainRound33Validation.agda
)

doc=docs/ns-clay-contract/ns-same-object-lookup-sharp-gain-round33.md

for file in "${files[@]}" "$doc"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|funext' "${files[@]}"; then
  echo "round thirty-three contains a hole, postulate, unsafe escape, trust primitive, or extensionality shortcut" >&2
  exit 1
fi

checks=(
  'NSTriadKNSameObjectLookupConsistencyRound33Exact.agda:builderForcesPositiveModeFunctional'
  'NSTriadKNSameObjectLookupConsistencyRound33Exact.agda:builderForcesPositiveNegativeCompatibility'
  'NSTriadKNSameObjectLookupConsistencyRound33Exact.agda:positiveModeConflictRefutesBuilder'
  'NSTriadKNSameObjectLookupConsistencyRound33Exact.agda:positiveNegativeConflictRefutesBuilder'
  'NSTriadKNSameObjectLookupConsistencyRound33Exact.agda:literalVelocityAtPositiveExact'
  'NSTriadKNSameObjectLookupConsistencyRound33Exact.agda:literalVelocityAtNegativeExact'
  'NSTriadKNSameObjectLookupConsistencyRound33Exact.agda:builderAndCanonicalPositiveAgree'
  'NSTriadKNSameObjectLookupConsistencyRound33Exact.agda:builderAndCanonicalNegativeAgree'
  'NSTriadKNSameObjectLookupConsistencyRound33Exact.agda:canonicalFiniteGalerkinSystemBuilderConstructed = false'
  'NSTriadKNHHBadSharpDyadicGainRound33Exact.agda:rawHHBadRatioDoubles'
  'NSTriadKNHHBadSharpDyadicGainRound33Exact.agda:requiredHHBadGainHalves'
  'NSTriadKNHHBadSharpDyadicGainRound33Exact.agda:requiredHHBadGainCalibration'
  'NSTriadKNHHBadSharpDyadicGainRound33Exact.agda:requiredHHBadGainUnique'
  'NSTriadKNHHBadSharpDyadicGainRound33Exact.agda:physicalHHBadDyadicGainConstructed = false'
  'NSTriadKNNineOwnerResourceReserveRound33Exact.agda:sumOwnerResourceEtaExact'
  'NSTriadKNNineOwnerResourceReserveRound33Exact.agda:nineOwnerResourceForbiddenZero'
  'NSTriadKNNineOwnerResourceReserveRound33Exact.agda:nineOwnerResourceReserveIdentity'
  'NSTriadKNNineOwnerResourceReserveRound33Exact.agda:nineOwnerResourceReservePositive'
  'NSTriadKNNineOwnerResourceReserveRound33Exact.agda:physicalNineOwnerResourceCertificateConstructed = false'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/Closure/$file"
done

grep -q '10.1007/BF02547354' \
  DASHI/Physics/Closure/NSTriadKNSameObjectLookupConsistencyRound33Exact.agda
grep -q '10.1090/chel/343' \
  DASHI/Physics/Closure/NSTriadKNSameObjectLookupConsistencyRound33Exact.agda
grep -q '10.1007/978-3-642-16830-7' \
  DASHI/Physics/Closure/NSTriadKNHHBadSharpDyadicGainRound33Exact.agda
grep -q '10.1007/s00021-019-0411-z' \
  DASHI/Physics/Closure/NSTriadKNHHBadSharpDyadicGainRound33Exact.agda
grep -q 'unique multiplicative gain' "$doc"
grep -q 'does not construct the nine estimates' "$doc"
grep -q 'never transport a bound without transporting its index' "$doc"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoSameObjectSharpGainRound33Validation.agda
