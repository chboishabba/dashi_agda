#!/usr/bin/env bash
# Six-frontier local source acceptance, 14-Nov-2026.
# CROSS-PR: require actual worktrees at EACH owner branch; never pass
# source files from different heads through a synthetic aggregate.
#
# Example:
#   DASHI_YM_WORKTREE=/path/ym1503 DASHI_KARP_WORKTREE=/path/karp1502 \
#   DASHI_NS_WORKTREE=/path/ns1501 DASHI_BISHOP_WORKTREE=/path/bishop1478 \
#   DASHI_BSD_LEAN_WORKTREE=/path/bsd107 DASHI_RH_LEAN_WORKTREE=/path/rh108 \
#   bash scripts/check_clay_sixfrontier_physical_local_20261114.sh
#
# CLAY_SIX_SOURCE_ONLY=1 performs finite Python diagnostics only.
# It NEVER constitutes Agda/Lean kernel acceptance or Clay success.
set -euo pipefail

need_tree() {
  local name="$1" dir="$2"
  if [[ -z "$dir" || ! -d "$dir" ]]; then
    echo "BLOCKED: $name worktree absent; do not fall back to default branch" >&2
    exit 24
  fi
}
need_tree "YM #1503" "${DASHI_YM_WORKTREE:-}"
need_tree "Karp #1502" "${DASHI_KARP_WORKTREE:-}"
need_tree "NS #1501" "${DASHI_NS_WORKTREE:-}"
need_tree "Bishop #1478" "${DASHI_BISHOP_WORKTREE:-}"
need_tree "BSD Lean #107" "${DASHI_BSD_LEAN_WORKTREE:-}"
need_tree "RH Lean #108" "${DASHI_RH_LEAN_WORKTREE:-}"

pycheck() {
  local root="$1" script="$2"
  (cd "$root" && python3 "scripts/$script")
}

echo "=== Six-frontier finite exact diagnostics (NOT KERNEL) ==="
pycheck "$DASHI_YM_WORKTREE" check_ym_r445_weighted_exterior_influence.py
pycheck "$DASHI_YM_WORKTREE" check_ym_r445_interacting_transfer_contraction_20261114.py
pycheck "$DASHI_KARP_WORKTREE" check_karp21_literal_gamma_allwords_20261114.py
pycheck "$DASHI_NS_WORKTREE" check_ns_r853_quadratic_lie_derivative_20261114.py
pycheck "$DASHI_BISHOP_WORKTREE" check_bishop_eta_all_cutoffs_maxcut_20261114.py
pycheck "$DASHI_BISHOP_WORKTREE" check_bishop_natlog_two_sided_dyadic_20261114.py
pycheck "$DASHI_BSD_LEAN_WORKTREE" check_bsd_q2_eight_squareclasses_20261114.py
pycheck "$(cd "$(dirname "$0")/.." && pwd)" check_rh_original_a2_interval_maxcut_20261114.py
echo "FINITE_EXACT_PASS: all selected diagnostics passed; NONE is an original physical theorem."

if [[ "${CLAY_SIX_SOURCE_ONLY:-0}" == "1" ]]; then
  echo "SOURCE_ONLY: kernel status BLOCKED, YM/Karp/BSD/NS/Bishop/RH terminal gates OPEN."
  exit 0
fi
command -v agda >/dev/null 2>&1 || command -v nix >/dev/null 2>&1 || {
  echo "KERNEL_BLOCKED: no Agda/Nix toolchain" >&2; exit 25;
}
command -v lake >/dev/null 2>&1 || {
  echo "KERNEL_BLOCKED: no Lake/Lean toolchain" >&2; exit 26;
}

echo "=== Check original Agda/Lean SOURCE ROOTS, not Clay endpoint proofs ==="
(cd "$DASHI_YM_WORKTREE" && bash scripts/check_ym_r445_original_physical_maxcut_local.sh)
(cd "$DASHI_KARP_WORKTREE" && bash scripts/check_karp21_allwords_physical_local.sh)
(cd "$DASHI_NS_WORKTREE" && bash scripts/check_ns_r854_affine_integral_local.sh)
(cd "$DASHI_BISHOP_WORKTREE" && bash scripts/check_bishop_eta_native_exp_cross_pr_local.sh)
(cd "$DASHI_BSD_LEAN_WORKTREE" && bash scripts/check_bsd_q2_hensel_3705_local.sh)
(cd "$(cd "$(dirname "$0")/.." && pwd)" && RH_LEAN_REPO_DIR="$DASHI_RH_LEAN_WORKTREE" bash scripts/check_rh_a2_g3_attachment_local.sh)
echo "SOURCE_ROOT_CHECKS_EXITED_0. Audit transitive axioms and exact heads."
echo "NOT CLOSED: YM E1/D1/D2; Karp original N21 InNP; BSD H1/Sha2; NS physical real trajectory/rate; Bishop eta uniform source; RH A2/G3 signed zero inequality."
