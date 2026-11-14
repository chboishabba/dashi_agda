#!/usr/bin/env bash
set -euo pipefail
#
# Original Bishop eta (#1408) plus native factorial complex-exp (#1478)
# REAL kernel source-dependency admission, NO CI.
# Source transfer is not proof admission. First Agda failure is authoritative.
#
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
targets=(
  DASHI/Analysis/BishopOriginalEtaDyadicSourceLawReductionExact.agda
  DASHI/Analysis/BishopRiemannDirichletBaselSameObjectExact.agda
  DASHI/Analysis/BishopRiemannAnalyticSetoidExpReuseExact.agda
  DASHI/Foundations/BishopNegativeLogGeometricSourceConvergenceExact.agda
  DASHI/Foundations/BishopRound11TrigAtZeroExact.agda
  DASHI/Analysis/BishopDirichletUniformBaselTailsExact.agda
  DASHI/Analysis/BishopRiemannDirichletExponentialTermExact.agda
  DASHI/Analysis/BishopOriginalDirichletEtaFinitePairingExact.agda
  DASHI/Analysis/BishopOriginalEtaFiniteAbelSourceExact.agda
  DASHI/Analysis/BishopOriginalXiPolynomialReflectionSameCarrierExact.agda
  DASHI/Analysis/BishopOriginalEtaZetaEvenCutoffSeriesWeldExact.agda
  DASHI/Analysis/BishopOriginalEtaEvenSourceScaleFiniteWeldExact.agda
  DASHI/Analysis/BishopComplexExpFactEqualsNativeExpExact.agda
  DASHI/Analysis/BishopOriginalEtaNativeFactorialExpSourceWeldExact.agda
)
for path in "${targets[@]}"; do
  if [[ ! -f "$path" ]]; then
    echo "MISSING: $path" >&2
    exit 2
  fi
done
if [[ -n "${AGDA_BIN:-}" ]] && command -v "$AGDA_BIN" >/dev/null 2>&1; then
  runner=(bash scripts/run_agda29_parallel_check.sh)
elif command -v agda >/dev/null 2>&1; then
  export AGDA_BIN="$(command -v agda)"
  runner=(bash scripts/run_agda29_parallel_check.sh)
elif command -v nix >/dev/null 2>&1; then
  runner=(nix develop .# --command bash scripts/run_agda29_parallel_check.sh)
else
  echo "BLOCKED: no AGDA_BIN, PATH agda, or nix; NO kernel acceptance" >&2
  exit 127
fi
for target in "${targets[@]}"; do
  echo "AGDA SOURCE: $target"
  DASHI_NO_TMUX=1 AGDA_JOBS="${AGDA_JOBS:-1}" "${runner[@]}" "$target"
done
echo "KERNEL PASS: Bishop eta ↔ source native factorial exp 14 target roots"
echo "NOT PROVED HERE: original log(2n) law, native exp addition/multiplication,"
echo "  dyadic a(2k+1) identity, compact-uniform eta convergence, RH."
