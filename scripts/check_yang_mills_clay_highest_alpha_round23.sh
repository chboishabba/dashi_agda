#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33UnscaledCyclePoincareWallExact.agda
  DASHI/Physics/YangMills/BalabanP33TerminalScaleGapPullbackExact.agda
  DASHI/Physics/YangMills/BalabanP33FixedVolumeTerminalScaleSeparationExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound23Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

test -f docs/yang-mills-combes-thomas-provenance.md

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round twenty-three contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33UnscaledCyclePoincareWallExact.agda:halfPeriodSquareWaveMeanZero'
  'BalabanP33UnscaledCyclePoincareWallExact.agda:halfPeriodSquareWaveNormExact'
  'BalabanP33UnscaledCyclePoincareWallExact.agda:halfPeriodSquareWaveCycleEnergyExact'
  'BalabanP33UnscaledCyclePoincareWallExact.agda:squareWave256LeftExact'
  'BalabanP33UnscaledCyclePoincareWallExact.agda:sixteenNotBelowEight'
  'BalabanP33UnscaledCyclePoincareWallExact.agda:oneThirtySecondNotUniformUnscaled'
  'BalabanP33TerminalScaleGapPullbackExact.agda:oneStepPullbackLower'
  'BalabanP33TerminalScaleGapPullbackExact.agda:pullBackGapBelowFine'
  'BalabanP33TerminalScaleGapPullbackExact.agda:pullBackGapClosedForm'
  'BalabanP33TerminalScaleGapPullbackExact.agda:fourStepPullbackExact'
  'BalabanP33TerminalScaleGapPullbackExact.agda:pulledBackNonnegativeImpliesFineNonnegative'
  'BalabanP33FixedVolumeTerminalScaleSeparationExact.agda:bareUniformOneThirtySecondBlocked'
  'BalabanP33FixedVolumeTerminalScaleSeparationExact.agda:terminalScaleGreenKernelDecay'
  'BalabanP33FixedVolumeTerminalScaleSeparationExact.agda:fineScaleGapNonnegativeFromTerminalChain'
  'BalabanP33FixedVolumeTerminalScaleSeparationExact.agda:terminalDecayAndFineGapFloor'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Primary-source metadata and external-source boundary.
grep -q '10.1007/BF01646473' \
  DASHI/Physics/YangMills/BalabanP33UnscaledCyclePoincareWallExact.agda
grep -q '10.1007/BF01240221' \
  DASHI/Physics/YangMills/BalabanP33TerminalScaleGapPullbackExact.agda
grep -q '10.1007/s00023-013-0303-3' \
  DASHI/Physics/YangMills/BalabanP33TerminalScaleGapPullbackExact.agda
grep -q '10.1063/1.5009458' \
  DASHI/Physics/YangMills/BalabanP33TerminalScaleGapPullbackExact.agda
grep -q 'NOT A MATHEMATICAL DEPENDENCY' \
  DASHI/Physics/YangMills/BalabanP33UnscaledCyclePoincareWallExact.agda
grep -q 'Public dates alone cannot establish either dependence or independence' \
  docs/yang-mills-combes-thomas-provenance.md
grep -q 'Hopping-parameter expansion' \
  docs/yang-mills-combes-thomas-provenance.md

# Scope guards: the terminal lane must not assert a physical RG law or a bare
# volume-uniform coercivity theorem.
grep -q 'physicalRGGapTransferProducerLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33TerminalScaleGapPullbackExact.agda
grep -q 'physicalOneStepRGGapEstimateLevel = conditional' \
  DASHI/Physics/YangMills/BalabanP33FixedVolumeTerminalScaleSeparationExact.agda
grep -q 'oneThirtySecondBareVolumeUniformPoincareLevel = machineChecked' \
  DASHI/Physics/YangMills/BalabanP33UnscaledCyclePoincareWallExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound23Validation.agda
