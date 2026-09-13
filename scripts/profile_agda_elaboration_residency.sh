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
OUT_ROOT="${DASHI_ELAB_PROFILE_DIR:-${XDG_CACHE_HOME:-$ROOT/.cache}/dashi-agda29/elaboration-profiles}"
STAMP="$(date +%Y%m%d-%H%M%S)"
RUN_DIR="$OUT_ROOT/$STAMP-$LABEL"
mkdir -p "$RUN_DIR"

# This profiler is intentionally serial.  We are measuring one module's live
# elaboration problem, not module-level parallelism.  Agda 2.9 permits the
# internal timing profiler together with conversion/constraint/meta/sharing
# counters via --profile=all.  GHC +RTS -s supplies allocation/residency/GC data.
# GNU time adds OS-level maximum RSS when available.
export AGDA_JOBS=1
export AGDA_PROFILE=all
export AGDA_RTS_STATS=1
export DASHI_NO_TMUX=1
export DASHI_TMUX_KEEP_FAILED=0
export DASHI_AGDA_RSS_LIMIT_MB="${DASHI_AGDA_RSS_LIMIT_MB:-28672}"
export AGDA_LOG_KEEP_COUNT=100
export AGDA_LOG_PATH="$RUN_DIR/agda.log"

# Preserve the normal persistent shadow/interface cache by default.  Set
# DASHI_ELAB_PROFILE_COLD=1 for a deliberately cold run.
if [ "${DASHI_ELAB_PROFILE_COLD:-0}" = "1" ]; then
  export DASHI_AGDA29_CLEAN=1
fi

# The Agda shadow is intentionally source-only plus persistent .agdai files.
# Python helpers occasionally leave __pycache__ directories in an older shadow.
# rsync --delete then quite correctly refuses to delete the directory because
# its excluded .pyc children are protected, producing noisy "cannot delete
# non-empty directory" diagnostics.  Python bytecode is irrelevant to Agda and
# is safe to discard without touching the warm .agdai cache.
DASHI_PROFILE_CACHE_ROOT="${DASHI_AGDA29_CACHE_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/dashi-agda29}"
DASHI_PROFILE_SHADOW="$DASHI_PROFILE_CACHE_ROOT/dashi-shadow"
if [ -d "$DASHI_PROFILE_SHADOW" ]; then
  find "$DASHI_PROFILE_SHADOW" -type d -name '__pycache__' -prune -exec rm -rf {} + 2>/dev/null || true
  find "$DASHI_PROFILE_SHADOW" -type f \( -name '*.pyc' -o -name '*.pyo' \) -delete 2>/dev/null || true
fi

COMMAND=(scripts/run_agda29_parallel_check.sh "$TARGET")
TIME_LOG="$RUN_DIR/time.txt"
STATUS_FILE="$RUN_DIR/status.txt"

set +e
if [ -x /usr/bin/time ]; then
  /usr/bin/time -v -o "$TIME_LOG" "${COMMAND[@]}"
  status=$?
else
  : > "$TIME_LOG"
  "${COMMAND[@]}"
  status=$?
fi
set -e
printf '%s\n' "$status" > "$STATUS_FILE"

# The wrapper timestamps the actual Agda log.  Locate the only/newest generated
# log in this run directory rather than guessing its filename.
AGDA_RUN_LOG="$(find "$RUN_DIR" -maxdepth 1 -type f -name 'agda-*.log' -printf '%T@ %p\n' 2>/dev/null | sort -n | tail -n1 | cut -d' ' -f2- || true)"
if [ -z "$AGDA_RUN_LOG" ]; then
  AGDA_RUN_LOG="$RUN_DIR/agda.log"
fi

extract_first_number() {
  local pattern="$1" file="$2"
  grep -E "$pattern" "$file" 2>/dev/null | tail -n1 | sed -E 's/^[^0-9]*([0-9][0-9,]*).*/\1/' | tr -d ',' || true
}

# Agda --profile=all prints per-module counters as aligned "label  value" rows.
# Parse only labels we have observed in real Agda 2.9 output.  The final match
# is used so the target module's statistics win over earlier dependency blocks.
extract_profile_stat() {
  local label="$1" file="$2"
  awk -v label="$label" '
    {
      line=$0
      sub(/^[[:space:]]+/, "", line)
      if (index(line, label) == 1) {
        rest=substr(line, length(label) + 1)
        gsub(/^[[:space:]]+|[[:space:]]+$/, "", rest)
        if (rest ~ /^[0-9][0-9,]*$/) value=rest
      }
    }
    END {
      gsub(/,/, "", value)
      print value
    }
  ' "$file" 2>/dev/null || true
}

ALLOC_BYTES="$(extract_first_number 'bytes allocated in the heap' "$AGDA_RUN_LOG")"
MAX_RESIDENCY_BYTES="$(extract_first_number 'maximum residency' "$AGDA_RUN_LOG")"
MAX_SLOP_BYTES="$(extract_first_number 'maximum slop' "$AGDA_RUN_LOG")"
TOTAL_MEMORY_BYTES="$(extract_first_number 'total memory in use' "$AGDA_RUN_LOG")"
MAX_RSS_KB="$(grep -E 'Maximum resident set size' "$TIME_LOG" 2>/dev/null | tail -n1 | awk -F: '{gsub(/^[[:space:]]+|[[:space:]]+$/, "", $2); print $2}' || true)"
ELAPSED="$(grep -E 'Elapsed \(wall clock\) time' "$TIME_LOG" 2>/dev/null | tail -n1 | sed -E 's/.*: //' || true)"
USER_SECONDS="$(grep -E '^\s*User time \(seconds\)' "$TIME_LOG" 2>/dev/null | tail -n1 | awk -F: '{gsub(/^[[:space:]]+|[[:space:]]+$/, "", $2); print $2}' || true)"
SYSTEM_SECONDS="$(grep -E '^\s*System time \(seconds\)' "$TIME_LOG" 2>/dev/null | tail -n1 | awk -F: '{gsub(/^[[:space:]]+|[[:space:]]+$/, "", $2); print $2}' || true)"

AGDA_METAS="$(extract_profile_stat 'metas' "$AGDA_RUN_LOG")"
AGDA_MAX_OPEN_CONSTRAINTS="$(extract_profile_stat 'max-open-constraints' "$AGDA_RUN_LOG")"
AGDA_ATTEMPTED_CONSTRAINTS="$(extract_profile_stat 'attempted-constraints' "$AGDA_RUN_LOG")"
AGDA_COMPARE="$(extract_profile_stat 'compare' "$AGDA_RUN_LOG")"
AGDA_COMPARE_BY_REDUCTION="$(extract_profile_stat 'compare by reduction' "$AGDA_RUN_LOG")"
AGDA_COMPARE_META="$(extract_profile_stat 'compare meta' "$AGDA_RUN_LOG")"
AGDA_FRESH_NODES="$(extract_profile_stat 'Node  (fresh)' "$AGDA_RUN_LOG")"
AGDA_FRESH_SHARED_TERMS="$(extract_profile_stat 'Shared Term  (fresh)' "$AGDA_RUN_LOG")"

SUMMARY="$RUN_DIR/summary.tsv"
printf 'label\ttarget\tstatus\tallocated_bytes\tmax_residency_bytes\tmax_slop_bytes\ttotal_memory_bytes\tmax_rss_kb\telapsed\tuser_seconds\tsystem_seconds\tagda_metas\tagda_max_open_constraints\tagda_attempted_constraints\tagda_compare\tagda_compare_by_reduction\tagda_compare_meta\tagda_fresh_nodes\tagda_fresh_shared_terms\tagda_log\n' > "$SUMMARY"
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
  "$LABEL" "$TARGET" "$status" "${ALLOC_BYTES:-}" "${MAX_RESIDENCY_BYTES:-}" \
  "${MAX_SLOP_BYTES:-}" "${TOTAL_MEMORY_BYTES:-}" "${MAX_RSS_KB:-}" \
  "${ELAPSED:-}" "${USER_SECONDS:-}" "${SYSTEM_SECONDS:-}" \
  "${AGDA_METAS:-}" "${AGDA_MAX_OPEN_CONSTRAINTS:-}" "${AGDA_ATTEMPTED_CONSTRAINTS:-}" \
  "${AGDA_COMPARE:-}" "${AGDA_COMPARE_BY_REDUCTION:-}" "${AGDA_COMPARE_META:-}" \
  "${AGDA_FRESH_NODES:-}" "${AGDA_FRESH_SHARED_TERMS:-}" "$AGDA_RUN_LOG" >> "$SUMMARY"

cat > "$RUN_DIR/README.txt" <<EOF
Agda elaboration-residency profile
=================================
label: $LABEL
target: $TARGET
status: $status
mode: serial (-j1), --profile=all, +RTS -s
RSS guard MiB: $DASHI_AGDA_RSS_LIMIT_MB
cold shadow: ${DASHI_ELAB_PROFILE_COLD:-0}

Interpretation boundary:
  allocated bytes != maximum live residency != operating-system RSS.
  Agda counters describe elaboration shape; they are not memory units.
  import count/depth is metadata, not the OOM diagnosis.
  a high residency/GC/conversion signal should trigger proof-expression surgery
  before changing -j or increasing heap limits.
EOF

echo "Elaboration profile: $SUMMARY"
cat "$SUMMARY"
exit "$status"
