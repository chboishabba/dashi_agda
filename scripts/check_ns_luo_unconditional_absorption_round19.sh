#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_integrated_absorption_round18.sh

files=(
  DASHI/Physics/Closure/NSTriadKNLuoStrainSpectralRigidityExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoStrainQuadraticAbsorptionNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCoupledEnergyStabilityAbsorptionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoResidualSourceLedgerExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoTwoLaneStrictAbsorptionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoUnconditionalAbsorptionRound19Validation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|TODO|FIXME' "${files[@]}"; then
  echo "round nineteen contains a hole, postulate, unsafe escape, trust primitive, or placeholder" >&2
  exit 1
fi

grep -q 'spectralRigidityIdentity' DASHI/Physics/Closure/NSTriadKNLuoStrainSpectralRigidityExact.agda
grep -q 'sharpCubicTraceBound' DASHI/Physics/Closure/NSTriadKNLuoStrainSpectralRigidityExact.agda
grep -q 'extensionalSpectralDefectVanishes' DASHI/Physics/Closure/NSTriadKNLuoStrainSpectralRigidityExact.agda

grep -q 'quadraticProjectionIsNonInjective' DASHI/Physics/Closure/NSTriadKNLuoStrainQuadraticAbsorptionNoGoExact.agda
grep -q 'absorptionGapIdentity' DASHI/Physics/Closure/NSTriadKNLuoStrainQuadraticAbsorptionNoGoExact.agda
grep -q 'cubicExceedsEveryNonnegativeQuadraticCoefficient' DASHI/Physics/Closure/NSTriadKNLuoStrainQuadraticAbsorptionNoGoExact.agda

grep -q 'coupledCancellation' DASHI/Physics/Closure/NSTriadKNLuoCoupledEnergyStabilityAbsorptionExact.agda
grep -q 'strictCoupledAbsorption' DASHI/Physics/Closure/NSTriadKNLuoCoupledEnergyStabilityAbsorptionExact.agda

grep -q 'residualLedgerDecomposition' DASHI/Physics/Closure/NSTriadKNLuoResidualSourceLedgerExact.agda
grep -q 'weightedTotalResidualWithinCombinedBudget' DASHI/Physics/Closure/NSTriadKNLuoResidualSourceLedgerExact.agda

grep -q 'twoLaneAbsorption' DASHI/Physics/Closure/NSTriadKNLuoTwoLaneStrictAbsorptionExact.agda
grep -q 'strictTwoLaneViscosityMargin' DASHI/Physics/Closure/NSTriadKNLuoTwoLaneStrictAbsorptionExact.agda

grep -q '10.1090/proc/16657' DASHI/Physics/Closure/NSTriadKNLuoStrainSpectralRigidityExact.agda
grep -q '10.48550/arXiv.1710.05569' DASHI/Physics/Closure/NSTriadKNLuoStrainSpectralRigidityExact.agda
grep -q 'PhilArchive record: NEMGRO' DASHI/Physics/Closure/NSTriadKNLuoStrainQuadraticAbsorptionNoGoExact.agda
grep -q 'DOI: none located' DASHI/Physics/Closure/NSTriadKNLuoCoupledEnergyStabilityAbsorptionExact.agda
grep -q '10.24033/asens.1404' DASHI/Physics/Closure/NSTriadKNLuoResidualSourceLedgerExact.agda
grep -q '10.20944/preprints202603.1591.v1' DASHI/Physics/Closure/NSTriadKNLuoTwoLaneStrictAbsorptionExact.agda

grep -q 'scaleFreeCubicByQuadraticAbsorptionProved' DASHI/Physics/Closure/NSTriadKNLuoStrainSpectralRigidityExact.agda
grep -q 'spectralRigidityAloneProducesBoth' DASHI/Physics/Closure/NSTriadKNLuoCoupledEnergyStabilityAbsorptionExact.agda
grep -q 'physicalLowerLaneProduced' DASHI/Physics/Closure/NSTriadKNLuoTwoLaneStrictAbsorptionExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoUnconditionalAbsorptionRound19Validation.agda
