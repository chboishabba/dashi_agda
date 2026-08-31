#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/YangMills/BalabanPhysicalFrontierSearchHypergraphRound146Exact.agda
  DASHI/Physics/YangMills/BalabanFrontierRouteAdmissionRound147Exact.agda
  DASHI/Physics/YangMills/BalabanFrontierExperimentDesignRound148Exact.agda
  DASHI/Physics/YangMills/BalabanFrontierFeedbackSearchRound149Exact.agda
  DASHI/Physics/YangMills/BalabanConsumerWeightedFrontierPriorityRound150Exact.agda
  DASHI/Physics/YangMills/BalabanRound108DirectUnifiedActionRound151Exact.agda
  DASHI/Physics/YangMills/BalabanProofExperimentFrontierRound150Validation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "YM proof/experiment frontier contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q '^data BalabanFrontierLeaf' "${files[0]}"
grep -q '^densityActionHasDirectRound108Route :' "${files[0]}"
grep -q '^densityActionHasCombinedRGRoute :' "${files[0]}"
grep -q '^unifiedSectorRouteTargets :' "${files[0]}"
grep -q '^numericalExperimentCannotDirectlyCloseLeaf :' "${files[1]}"
grep -q '^data BalabanFrontierCoordinate' "${files[2]}"
grep -q '^record FrontierCoordinateDiscrimination' "${files[2]}"
grep -q '^unifiedSectorClosureMonotone :' "${files[3]}"
grep -q '^record CostedBalabanFrontierResolution' "${files[3]}"
grep -q '^directRound108MatchAlphaIsFour :' "${files[4]}"
grep -q '^combinedRGDensityStateAlphaIsOne :' "${files[4]}"
grep -q '^combinedRGStatePotentialAlphaIsOne :' "${files[4]}"
grep -q '^componentD1AlphaIsThree :' "${files[4]}"
grep -q '^record Round108DirectPresentCutActionRealization' "${files[5]}"
grep -q '^round108DirectSelectedDensityRepresentsBC1Potential :' "${files[5]}"
grep -q 'round151DirectRound108ActionCompiler' "${files[6]}"

cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-ym-proof-experiment}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME"
export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$root/ym-proof-experiment-frontier-agda.log}"
export AGDA_JOBS="${AGDA_JOBS:-4}"
export DASHI_NO_TMUX="1"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanProofExperimentFrontierRound150Validation.agda
