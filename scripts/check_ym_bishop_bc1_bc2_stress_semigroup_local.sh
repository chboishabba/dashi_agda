#!/usr/bin/env bash
set -euo pipefail
# Local Agda 2.9 target split: truly --safe algebra vs Bishop/native vs
# explicitly axiomatic legacy CMP109/CMP116/heat. No CI or Docker.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

safe_sources=(
  DASHI/Physics/YangMills/BalabanCMP109116ConstructiveScalarCoreExact.agda
  DASHI/Physics/YangMills/YangMillsStressOSCommonSemigroupDerivativeExact.agda
)
bishop_source=DASHI/Physics/YangMills/BalabanCMP109116BishopRealSetoidInstantiationExact.agda
ordinary_sources=(
  "$bishop_source"
  DASHI/Physics/YangMills/YangMillsStressOSSourceFirstSemigroupCoreToClosureExact.agda
)
legacy_sources=(
  DASHI/Physics/YangMills/BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact.agda
  DASHI/Physics/YangMills/BalabanHeatDoobFromSameDensityExpectationRound108Exact.agda
  DASHI/Physics/YangMills/BalabanBC2CompactGroupSameDensityRound119Exact.agda
)

if [[ -z "${AGDA_BIN:-}" ]] && command -v agda >/dev/null 2>&1; then
  export AGDA_BIN="$(command -v agda)"
fi

for file in "${safe_sources[@]}" "${ordinary_sources[@]}" "${legacy_sources[@]}"; do
  test -s "$file" || { echo "MISSING $file" >&2; exit 2; }
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|primTrustMe|TERMINATING|NON_COVERING' "$file"; then
    echo "BLOCKED source escape: $file" >&2
    exit 2
  fi
done

for file in "${safe_sources[@]}"; do
  echo "AGDA --safe: $file"
  DASHI_NO_TMUX=1 AGDA_JOBS=1 \
    bash scripts/run_agda29_parallel_check.sh --safe "$file"
done

for file in "${ordinary_sources[@]}"; do
  echo "AGDA normal source check (not transitive safe): $file"
  DASHI_NO_TMUX=1 AGDA_JOBS=1 \
    bash scripts/run_agda29_parallel_check.sh "$file"
done

for file in "${legacy_sources[@]}"; do
  echo "AGDA legacy original source (RealAnalysisAxioms postulates disclosed): $file"
  DASHI_NO_TMUX=1 AGDA_JOBS=1 \
    bash scripts/run_agda29_parallel_check.sh "$file"
done

echo "SOURCE TRUST AUDIT: legacy roots expected to remain non-safe"
python3 scripts/audit_ym_legacy_real_safe_boundary.py --json
echo "SAFE ROOTS / NORMAL BISHOP SOURCE / AXIOMATIC LEGACY receipt separated."
echo "NOT A CLAY PROOF. Run the source auditor --strict before any --safe promotion."
