#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OUT="${DASHI_SOLVER_FIBRE_AUDIT_OUT:-${TMPDIR:-/tmp}/dashi-solver-fibre-audit.tsv}"
STRICT="${DASHI_SOLVER_FIBRE_AUDIT_STRICT:-0}"

printf 'class\tfile\tsolver_calls\tbare_solver_lines\theavy_tokens\n' > "$OUT"

# Reflection/ring solving is not forbidden.  The dangerous shape is a solver
# re-entering an already-instantiated physical/fibre term after a compression
# boundary.  This static audit is deliberately conservative: it identifies
# candidates for profiler/inspection rather than pretending syntax proves OOM.
mapfile -t files < <(
  grep -RIl --include='*.agda' \
    -E 'RingSolver|solve-∀|\.solve([[:space:]]|$)' \
    DASHI/Physics/YangMills DASHI/Physics/Closure 2>/dev/null | sort
)

failures=0
for file in "${files[@]}"; do
  solver_calls="$(grep -Ec 'solve-∀|\.solve([[:space:]]|$)' "$file" || true)"
  bare_solver_lines="$(grep -Ec 'solve-∀[[:space:]]*$|\.solve[[:space:]]*$' "$file" || true)"
  heavy_tokens="$(grep -Ec 'SiteField|physicalBlockSites|globalBlockInner|sumRational|martingale|Fourier|Galerkin|R406|lattice|fibre|Fibre' "$file" || true)"

  class='scalar-or-unknown'
  case "$file" in
    *BalabanOpaqueGlobalAlgebraExact.agda|*ZZRing*|*ExactRingSolverBridge.agda)
      class='atomic-scalar-leaf'
      ;;
    *)
      if [ "$heavy_tokens" -gt 0 ]; then
        if [ "$bare_solver_lines" -gt 0 ]; then
          class='carrier-facing-review'
          if [ "$STRICT" = '1' ]; then
            failures=$((failures + 1))
          fi
        else
          class='compressed-explicit-or-pointwise-review'
        fi
      fi
      ;;
  esac

  printf '%s\t%s\t%s\t%s\t%s\n' \
    "$class" "$file" "$solver_calls" "$bare_solver_lines" "$heavy_tokens" >> "$OUT"
done

cat "$OUT"

cat <<'EOF'

Interpretation:
  atomic-scalar-leaf
      preferred location for reflection/algebra; no physical carrier semantics.

  compressed-explicit-or-pointwise-review
      solver occurs in a carrier-aware module but does not end on a syntactically
      bare solver line. Inspect whether its explicit arguments are already opaque
      scalar coordinates or whether a pointwise atomic proof is being discharged.

  carrier-facing-review
      highest-priority profiling/refactor candidate. A bare solver invocation is
      present in a module whose vocabulary includes large fibre/global carriers.
      Replace with atomic lemma + observer/relation lift when the solver can see
      an instantiated physical goal.

This audit is diagnostic by default. Set DASHI_SOLVER_FIBRE_AUDIT_STRICT=1 only
for a deliberately curated validation root; repository-wide legacy code is not
silently reclassified as invalid merely because it needs review.
EOF

if [ "$failures" -ne 0 ]; then
  echo "strict solver/fibre audit found $failures carrier-facing candidate(s)" >&2
  exit 1
fi
