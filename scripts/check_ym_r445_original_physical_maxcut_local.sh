#!/usr/bin/env bash
# Exact original YM F19/P0/R445 local maximum-cut acceptance.
#
# R445_SOURCE_ONLY=1: run finite rational no-go/TV regression tests ONLY,
# explicitly NOT Agda acceptance or a physical continuum theorem.
#
# Default: fail closed unless the pinned Agda runner can run.
set -euo pipefail
cd "$(dirname "$0")/.."

printf '%s\n' "== R445 original finite density ratio and TV arithmetic =="
python3 scripts/check_ym_r445_action_oscillation_tv.py
python3 scripts/check_ym_r445_relative_density_three_moment_cut.py

printf '%s\n' "== R445 conditional influence and logical no-go checker =="
python3 scripts/check_ym_r445_localized_tv_maxcut_countermodels.py

printf '%s\n' "== R445 exact-rational independent regression tests =="
python3 -m unittest discover -s tests \
  -p 'test_ym_r445_localized_tv_maxcut_countermodels.py' -v

if [[ "$(printenv R445_SOURCE_ONLY || true)" == "1" ]]; then
  echo "SOURCE_ONLY_PASS (NOT AGDA KERNEL; physical R445 TV/E1/D1/D2 remain OPEN)"
  exit 0
fi

if ! command -v nix >/dev/null 2>&1 && ! command -v agda >/dev/null 2>&1; then
  echo "KERNEL_BLOCKED: no pinned Nix/Agda 2.9 toolchain. All endpoints OPEN." >&2
  exit 2
fi

printf '%s\n' "== Original F19/P0/R445 Agda source root / kernel =="
bash scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/YMClayOriginalF19P0CommonOSSourceConvergence20261114.agda

echo "KERNEL_CHECK_EXITED_0: inspect transitive legacy RealAnalysisAxioms postulates"
echo "NO_PHYSICAL_R445_Dk_OR_CLAY_ENDPOINT_PROMOTED"
