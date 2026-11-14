#!/usr/bin/env bash
# Source-level NS A/B/C/D x TOE and exact nested f9e C/D verification.
# Kernel mode is fail-closed; a SymPy PASS is never a kernel certificate.
set -euo pipefail
AGDA_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_ROOT="${DASHI_CLAY_LEAN_WORKTREE:-}"
MODE="${NS_TOE_VERIFY_MODE:-source-only}"
if [[ ! -d "$LEAN_ROOT/ExternalClayNS" ]]; then
  echo "BLOCKED: DASHI_CLAY_LEAN_WORKTREE must point at canonical Lean Clay PR #108" >&2
  exit 21
fi
for root in "$AGDA_ROOT" "$LEAN_ROOT"; do
  git -C "$root" rev-parse --is-inside-work-tree >/dev/null || exit 22
done
printf 'AGDA_HEAD=%s\n' "$(git -C "$AGDA_ROOT" rev-parse HEAD)"
printf 'LEAN_HEAD=%s\n' "$(git -C "$LEAN_ROOT" rev-parse HEAD)"
for file in \
  DASHI/Papers/NavierStokes/FourLaneProofProgramExact.agda \
  DASHI/Unified/NavierStokesClayFrontierTOEConvergenceExact.agda \
  DASHI/Unified/NavierStokesBM2TOEConvergenceExact.agda \
  DASHI/Physics/Closure/NSWholeSpaceCanonicalPairSaturationOriginExact.agda \
  DASHI/Physics/Closure/NSWholeSpaceR3RadialFactorBudgetExact.agda \
  DASHI/Physics/Closure/NSR3RadialLebesgueSignedSecondMomentAggregationExact.agda \
  DASHI/Physics/Closure/NSTriadKNR650Rational345LipschitzIntegralRound854Exact.agda; do
  test -f "$AGDA_ROOT/$file" || { echo "BLOCKED: missing $file" >&2; exit 23; }
done
for file in ClaySpec.lean Gap.lean Adapter.lean LiteralABCD.lean \
   ClauseAudit.lean ProvenanceAudit.lean SubmissionAudit.lean lakefile.toml lean-toolchain; do
  test -f "$LEAN_ROOT/ExternalClayNS/$file" || { echo "BLOCKED: missing $file" >&2; exit 24; }
done
EXPECTED_PIN='f9e8bc5b38b6e212696e8a30e3e91517af887bbd'
grep -F -q "$EXPECTED_PIN" "$LEAN_ROOT/ExternalClayNS/lakefile.toml" || {
  echo "BLOCKED: ExternalClayNS pin differs from exact reviewed f9e source" >&2; exit 25;
}
grep -F -q 'leanprover/lean4:v4.34.0-rc2' "$LEAN_ROOT/ExternalClayNS/lean-toolchain" || {
  echo 'BLOCKED: wrong nested Lean toolchain' >&2; exit 26;
}
if python3 -c 'import sympy' >/dev/null 2>&1; then
  (cd "$AGDA_ROOT" && python3 scripts/check_ns_abcd_r3_toe_sympy_20261115.py)
else
  echo 'NS_ABCD_SYMPY_SKIPPED: sympy unavailable; no symbolic receipt'
fi
if [[ "$MODE" == 'source-only' ]]; then
  echo 'NS_TOE_SOURCE_PREFLIGHT_ONLY: no Agda/Lean kernel proof is asserted'
  exit 0
fi
if [[ "$MODE" != 'kernel' ]]; then
  echo "BLOCKED: NS_TOE_VERIFY_MODE must be source-only or kernel" >&2; exit 27
fi
for binary in git lake; do
  command -v "$binary" >/dev/null || { echo "KERNEL_BLOCKED: $binary unavailable" >&2; exit 28; }
done
UPSTREAM="$LEAN_ROOT/ExternalClayNS/.lake/packages/NavierStokesAndEuler"
if [[ ! -d "$UPSTREAM/.git" ]]; then
  echo 'KERNEL_BLOCKED: pinned f9e OAI NS upstream not installed; no network fallback' >&2
  exit 29
fi
ACTUAL_PIN="$(git -C "$UPSTREAM" rev-parse HEAD)"
[[ "$ACTUAL_PIN" == "$EXPECTED_PIN" ]] || {
  echo "KERNEL_BLOCKED: source commit drift: $ACTUAL_PIN" >&2; exit 30;
}
(cd "$LEAN_ROOT/ExternalClayNS" && lake env lean --version && lake build)
echo 'EXTERNAL_CLAY_NS_BUILD_EXECUTED: inspect #print axioms output and mathematical scope'
if [[ -f "$AGDA_ROOT/scripts/run_agda29_parallel_check.sh" ]]; then
  (cd "$AGDA_ROOT" && AGDA_JOBS=1 DASHI_NO_TMUX=1 bash \
    scripts/run_agda29_parallel_check.sh \
    DASHI/Unified/NavierStokesClayFrontierTOEConvergenceValidation.agda)
  echo 'AGDA_29_DRAFT_CHECK_EXECUTED: final authority still requires pinned Track A'
else
  echo 'KERNEL_BLOCKED: Agda wrapper unavailable' >&2
  exit 31
fi
