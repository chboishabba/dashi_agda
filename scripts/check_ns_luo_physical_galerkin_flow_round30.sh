#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_dependent_flow_owner_analysis_round29.sh

files=(
  DASHI/Physics/Closure/NSTriadKNPhysicalGalerkinVectorFieldRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNFinitePhysicalCoordinateEquivalenceRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNPicardLindelofTransportRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNLiteralNonlinearEnergyCancellationRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNPhysicalFiniteEnergyIdentityRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNPhysicalGlobalGalerkinFlowRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNPhysicalTimeDependentShellBalanceRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNCutoffUniformCotlarSteinRound30Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalGalerkinFlowRound30Validation.agda
)

doc=docs/ns-clay-contract/physical-galerkin-flow-round30.md

for file in "${files[@]}" "$doc"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|funext' "${files[@]}"; then
  echo "round thirty contains a hole, postulate, unsafe escape, trust primitive, or extensionality shortcut" >&2
  exit 1
fi

checks=(
  'NSTriadKNPhysicalGalerkinVectorFieldRound30Exact.agda:physicalGalerkinVectorField'
  'NSTriadKNPhysicalGalerkinVectorFieldRound30Exact.agda:physicalGalerkinSelectorEquivariant'
  'NSTriadKNPhysicalGalerkinVectorFieldRound30Exact.agda:physicalGalerkinOutputNegativeCoefficientTransverse'
  'NSTriadKNFinitePhysicalCoordinateEquivalenceRound30Exact.agda:physicalFieldEncodedExactly'
  'NSTriadKNFinitePhysicalCoordinateEquivalenceRound30Exact.agda:transportCompleteFiniteVectorLipschitz'
  'NSTriadKNPicardLindelofTransportRound30Exact.agda:transportedTrajectorySolvesPhysicalODE'
  'NSTriadKNPicardLindelofTransportRound30Exact.agda:physicalLocalTrajectoryUniqueCoordinatewise'
  'NSTriadKNLiteralNonlinearEnergyCancellationRound30Exact.agda:literalFiniteNonlinearEnergyCancellation'
  'NSTriadKNPhysicalFiniteEnergyIdentityRound30Exact.agda:physicalFiniteDifferentialEnergyIdentity'
  'NSTriadKNPhysicalFiniteEnergyIdentityRound30Exact.agda:physicalEnergyContinuationTrajectory'
  'NSTriadKNPhysicalGlobalGalerkinFlowRound30Exact.agda:physicalFiniteFlowHasNoFiniteMaximalTime'
  'NSTriadKNPhysicalTimeDependentShellBalanceRound30Exact.agda:physicalFiveSourceShellBalanceAt'
  'NSTriadKNCutoffUniformCotlarSteinRound30Exact.agda:cutoffUniformCotlarSteinSquaredBound'
  'NSTriadKNCutoffUniformCotlarSteinRound30Exact.agda:geometricEnvelopeProducesUniformMass'
)
for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/Closure/$file"
done

grep -q '10.1007/BF02547354' DASHI/Physics/Closure/NSTriadKNPhysicalGalerkinVectorFieldRound30Exact.agda
grep -q '10.1090/chel/343' DASHI/Physics/Closure/NSTriadKNPhysicalFiniteEnergyIdentityRound30Exact.agda
grep -q '10.24033/asens.1404' DASHI/Physics/Closure/NSTriadKNPhysicalTimeDependentShellBalanceRound30Exact.agda
grep -q '10.1002/cpa.3160410704' DASHI/Physics/Closure/NSTriadKNCutoffUniformCotlarSteinRound30Exact.agda
grep -q 'ReconstructedPhysicalState F E -> ReconstructedPhysicalState F E' "$doc"
grep -q 'dE/dt + nu D = 0' "$doc"
grep -q 'T_q\* T_r' "$doc"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoPhysicalGalerkinFlowRound30Validation.agda
