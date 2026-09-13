#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [ "$#" -lt 1 ]; then
  echo "usage: $0 TARGET.agda [LABEL]" >&2
  exit 2
fi

TARGET="$1"
LABEL="${2:-$(basename "$TARGET" .agda)}"
OUT_ROOT="${DASHI_AGDA_PROFILER_VIEW_DIR:-${XDG_CACHE_HOME:-$ROOT/.cache}/dashi-agda29/profiler-views}"
STAMP="$(date +%Y%m%d-%H%M%S)"
RUN_ROOT="$OUT_ROOT/$STAMP-$LABEL"
mkdir -p "$RUN_ROOT"

# Agda 2.9 exposes three alternative timing observers.  --profile=all chooses
# internal timing and enables the orthogonal counter/statistics profilers.  We
# therefore use one canonical memory/counter pass plus separate localization
# passes for definitions and modules.
#
# All runs are -j1 so module parallelism cannot masquerade as a single-module
# elaboration-residency effect.
COMMON_ENV=(
  AGDA_JOBS=1
  AGDA_RTS_STATS=1
  DASHI_NO_TMUX=1
  DASHI_TMUX_KEEP_FAILED=0
  DASHI_AGDA_RSS_LIMIT_MB="${DASHI_AGDA_RSS_LIMIT_MB:-28672}"
  AGDA_LOG_KEEP_COUNT=100
)

run_view() {
  local view="$1" profile="$2" rts_stats="$3"
  local dir="$RUN_ROOT/$view"
  mkdir -p "$dir"

  echo "Profiling $TARGET [$view: --profile=$profile]"
  set +e
  env "${COMMON_ENV[@]}" \
    AGDA_PROFILE="$profile" \
    AGDA_RTS_STATS="$rts_stats" \
    AGDA_LOG_PATH="$dir/agda.log" \
    scripts/run_agda29_parallel_check.sh "$TARGET" \
    >"$dir/stdout-stderr.log" 2>&1
  local status=$?
  set -e
  printf '%s\n' "$status" > "$dir/status.txt"
  return "$status"
}

failures=0

# Canonical system observation: internal timing + sharing/serialize/constraints/
# metas/interactive/conversion via Agda's profile=all, plus GHC RTS statistics.
if ! run_view internal-all all 1; then
  failures=$((failures + 1))
fi

# Hotspot localization.  These are alternative timing fibres, not replacements
# for the canonical residency/counter pass.
if ! run_view definitions definitions 0; then
  failures=$((failures + 1))
fi

if ! run_view modules modules 0; then
  failures=$((failures + 1))
fi

cat > "$RUN_ROOT/receipt.tsv" <<EOF
label\ttarget\tview\tprofile\tstatus\tlog
$LABEL\t$TARGET\tinternal-all\tall\t$(cat "$RUN_ROOT/internal-all/status.txt")\t$RUN_ROOT/internal-all/stdout-stderr.log
$LABEL\t$TARGET\tdefinitions\tdefinitions\t$(cat "$RUN_ROOT/definitions/status.txt")\t$RUN_ROOT/definitions/stdout-stderr.log
$LABEL\t$TARGET\tmodules\tmodules\t$(cat "$RUN_ROOT/modules/status.txt")\t$RUN_ROOT/modules/stdout-stderr.log
EOF

cat > "$RUN_ROOT/README.txt" <<'EOF'
Agda profiler observation suite
===============================

internal-all
  Agda --profile=all.  Canonical system-level profiler receipt.  Includes
  internal timing and the orthogonal sharing/serialization/constraint/meta/
  interactive/conversion observers.  GHC +RTS -s is enabled here.

definitions
  Agda --profile=definitions.  Definition-local timing observer used after a
  residency/counter anomaly to find proof-term hotspots.

modules
  Agda --profile=modules.  Module-local timing observer used to separate an
  expensive imported/checking cone from a definition-local hotspot.

Epistemic boundary
  These outputs are empirical diagnostics.  They do not inhabit or strengthen
  the theorem being checked.  Timing views are alternative observers and must
  not be merged as if their entries had identical semantics.
EOF

echo "Agda profiler views: $RUN_ROOT/receipt.tsv"
cat "$RUN_ROOT/receipt.tsv"

if [ "$failures" -ne 0 ]; then
  exit 1
fi
