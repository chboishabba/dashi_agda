#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

files=(
  DASHI/Physics/ExoticGravity/Zhang2025EMGravitySourceClaimExact.agda
  DASHI/Physics/ExoticGravity/Zhang2025EMGravityPhysicalPromotionExact.agda
  DASHI/Physics/ExoticGravity/Zhang2025EMGravityValidation.agda
)

for f in "${files[@]}"; do
  test -s "$f"
  if grep -En '(^|[[:space:]])(postulate|primitive)[[:space:]]|\{!!\}|trustMe|unsafe|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|--with-K' "$f"; then
    echo "Unapproved proof escape in $f" >&2
    exit 1
  fi
done

grep -q 'Provenance.ProvenancedComparativeAnomalyReceipt' "${files[1]}"
grep -q 'sourceMotionCannotEqualMetricReadout' "${files[2]}"
grep -q 'currentSourceHasNoIndependentPhysicalReceipt' "${files[2]}"

export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$PWD/zhang2025-agda.log}"
export AGDA_BIN="$PWD/scripts/agda29_without_k_wrapper.sh"
bash scripts/run_agda29_parallel_check.sh --safe -- \
  DASHI/Physics/ExoticGravity/Zhang2025EMGravityValidation.agda

echo 'Zhang source/scope Agda proof validation passed on this exact checkout.'
