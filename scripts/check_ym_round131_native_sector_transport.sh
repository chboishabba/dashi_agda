#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/YangMills/BalabanCommonMetricSectorRecoveryRound131Exact.agda
  DASHI/Physics/Foundations/BalabanNativeSectorRecoveryTransportExact.agda
  DASHI/Physics/Foundations/BalabanAllSectorContinuumProducerExact.agda
  DASHI/Physics/Foundations/BalabanTransportedSectorFamilyProducerExact.agda
  DASHI/Physics/Foundations/BalabanRound131NativeSectorRecoveryTransportExact.agda
  DASHI/Physics/Foundations/BalabanRound131NativeSectorTransportValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "Round131 native-sector transport contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q '^record NativeBalabanSectorRecoveryTransport' "${files[1]}"
grep -q 'nativeLiteralStressShared' "${files[1]}"
grep -q 'nativeLiteralPairingCommutes' "${files[1]}"
grep -q '^nativeLiteralSectorRecoveryTransportCompilerLevel :' "${files[1]}"

grep -q '^record Round131SharedTransportData' "${files[4]}"
grep -q 'literalConstructionIsSelectedQFTTarget' "${files[4]}"
grep -q 'literalStressPairingCommutes' "${files[4]}"
grep -q '^round131RecoveryToNativeSectorTransport :' "${files[4]}"
grep -q '^round131NativeSectorTransportCompilerLevel :' "${files[4]}"
grep -q '^round131LiteralSectorTransportCompilerLevel :' "${files[4]}"

grep -q 'Transport.nativeLiteralSectorRecoveryTransportCompilerLevel' "${files[5]}"
grep -q 'Adapter.round131LiteralSectorTransportCompilerLevel' "${files[5]}"

cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-round131-native-transport}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME"
export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$root/ym-round131-native-transport-agda.log}"
export AGDA_JOBS="${AGDA_JOBS:-4}"
export DASHI_NO_TMUX="1"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Foundations/BalabanRound131NativeSectorTransportValidation.agda
