#!/usr/bin/env bash
set -euo pipefail

# Highest-information LOCAL P0 frontiers: genuine constructive Bishop
# arithmetic, its explicit original-Wilson scalar interpretation, and
# the concrete rational SU(2) matrix/trace owner.
#
# Not a claim of full SU(N) physical matrix boundedness, a proof that
# the original postulated ℝ has been identified with Bishop ℝ, or a
# terminal Clay gate. The uninhabited weld record stays visible.
#
# Run from the PR #1444 checkout:
#   bash scripts/check_ym_p0_real_carrier_local.sh
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

targets=(
  DASHI/Physics/YangMills/YMClayP0BishopRealCarrierInstancesExact.agda
  DASHI/Physics/YangMills/YMClayP0BishopToOriginalWilsonRealWeldExact.agda
  DASHI/Physics/YangMills/BalabanSU2RationalWilsonTraceBoundExact.agda
)

for target in "${targets[@]}"; do
  if [[ ! -f "$target" ]]; then
    echo "MISSING P0 source: $target" >&2
    exit 2
  fi
done

if ! command -v nix >/dev/null 2>&1; then
  echo 'Nix unavailable: local P0 Agda acceptance NOT performed' >&2
  exit 127
fi

printf 'P0 source-cut head %s\n' "$(git rev-parse HEAD 2>/dev/null || printf unknown)"
for target in "${targets[@]}"; do
  printf '\nP0 kernel target: %s\n' "$target"
  DASHI_NO_TMUX=1 AGDA_JOBS="${AGDA_JOBS:-1}" \
    nix develop .# --command \
    bash scripts/run_agda29_parallel_check.sh "$target"
done

echo 'PASS: all three isolated P0 scalar/SU2 Agda module checks completed.'
echo 'NOTE: OriginalWilsonToBishopScalarWeld is not thereby inhabited.'
