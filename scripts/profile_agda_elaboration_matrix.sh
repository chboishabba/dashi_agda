#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OUT_ROOT="${DASHI_ELAB_PROFILE_DIR:-${XDG_CACHE_HOME:-$ROOT/.cache}/dashi-agda29/elaboration-profiles}"
STAMP="$(date +%Y%m%d-%H%M%S)"
MATRIX_DIR="$OUT_ROOT/matrix-$STAMP"
mkdir -p "$MATRIX_DIR"

# Deliberately different elaboration shapes:
#   1. CS control: real branching/loops/codecs, small import-only validation root.
#   2. NS cheap control: tiny ordered-rational core after dependency-cone surgery.
#   3. NS repaired hotspot: formerly ~17.7 GiB warm-cache eight-way normalization.
#   4. YM side-four stressor: deep finite-sum/martingale variance decomposition.
#   5. YM Path13 atomic/fibre lift: 13-point physical Poincare plus canonical
#      finite-sum <= observer, before directional/four-axis composition.
#   6. YM Path13 directional layer: predecessor norm contraction and literal
#      multiplicity-13 transport, before the four-axis martingale consumer.
#   7. YM Path13 global stressor: 28,561-site physical Poincare composition.
TARGETS=(
  "DASHI/ComputerScience/ComputerScienceFibreFoundationValidationExact.agda|cs-fibre-control"
  "DASHI/Physics/Closure/NSTriadKNLuoFiniteRationalOrderCore.agda|ns-rational-control"
  "DASHI/Physics/Closure/NSTriadKNLuoFiniteEightPointSixThreeHolderBoundary.agda|ns-repaired-holder"
  "DASHI/Physics/YangMills/BalabanPath4PhysicalVarianceDecompositionExact.agda|ym-variance-stressor"
  "DASHI/Physics/YangMills/BalabanPath13ZeroMeanFibrePoincareLiftExact.agda|ym-path13-fibre-lift"
  "DASHI/Physics/YangMills/BalabanPath13DirectionalEnergyContractionExact.agda|ym-path13-directional"
  "DASHI/Physics/YangMills/BalabanPath13FourAxisPhysicalPoincareExact.agda|ym-poincare-13"
)

RESULTS="$MATRIX_DIR/matrix.tsv"
printf 'label\ttarget\tstatus\tallocated_bytes\tmax_residency_bytes\tmax_slop_bytes\ttotal_memory_bytes\tmax_rss_kb\telapsed\tuser_seconds\tsystem_seconds\tagda_metas\tagda_max_open_constraints\tagda_attempted_constraints\tagda_compare\tagda_compare_by_reduction\tagda_compare_meta\tagda_fresh_nodes\tagda_fresh_shared_terms\tagda_log\n' > "$RESULTS"

failures=0
for entry in "${TARGETS[@]}"; do
  target="${entry%%|*}"
  label="${entry#*|}"

  if [ ! -f "$target" ]; then
    echo "missing matrix target: $target" >&2
    failures=$((failures + 1))
    continue
  fi

  run_root="$MATRIX_DIR/$label"
  mkdir -p "$run_root"
  set +e
  DASHI_ELAB_PROFILE_DIR="$run_root" \
    bash scripts/profile_agda_elaboration_residency.sh "$target" "$label"
  status=$?
  set -e

  summary="$(find "$run_root" -type f -name summary.tsv -print | sort | tail -n1 || true)"
  if [ -n "$summary" ]; then
    tail -n +2 "$summary" >> "$RESULTS"
  else
    failures=$((failures + 1))
  fi

  if [ "$status" -ne 0 ]; then
    failures=$((failures + 1))
  fi
done

cat > "$MATRIX_DIR/INTERPRETATION.txt" <<'EOF'
This matrix tests the hypothesis that Clay-lane OOM risk is primarily an
elaboration-residency phenomenon rather than a source-size/nestedness phenomenon.

Do not rank targets by line count or import count alone.  Compare especially:
  * allocated_bytes / max_residency_bytes
  * max_residency_bytes / max_rss_kb
  * agda_compare / agda_compare_by_reduction / agda_compare_meta
  * agda_metas / agda_max_open_constraints / agda_attempted_constraints
  * agda_fresh_nodes / agda_fresh_shared_terms
  * GC time versus mutator/typechecking time

Expected diagnostic classes:
  allocation-heavy, residency-light
      expensive but reclaimable; usually not the primary OOM wall.

  conversion-heavy + residency-heavy
      stage equalities; lift through fibre observers; keep downstream algebra
      on opaque observed coordinates; avoid giant global solver re-entry.

  constraint/meta-heavy + residency-heavy
      expose indices/implicits; split inference problems.

  sharing-poor / repeated normalization
      introduce stable intermediate lemmas or compiled interfaces.

  import-heavy but low residency
      dependency cone is not the causal OOM explanation.

Path13 is intentionally split into three roots.  Compare fibre-lift ->
directional -> global.  The first transition that sharply raises residency or
conversion activity identifies the next representation boundary to repair.
The generated LDL certificate may take substantial CPU while remaining
residency-stable; that is analytically different from global carrier re-entry.

-j is intentionally fixed at 1 here.  Parallel module scheduling is a separate
multiplier and must not obscure single-module elaboration behaviour.
EOF

echo "Elaboration matrix: $RESULTS"
column -t -s $'\t' "$RESULTS" 2>/dev/null || cat "$RESULTS"

# A killed stressor is itself useful evidence, so the matrix remains written.
# Return non-zero so CI/automation cannot mistake an incomplete profile for a
# successful certification run.
if [ "$failures" -ne 0 ]; then
  exit 1
fi
