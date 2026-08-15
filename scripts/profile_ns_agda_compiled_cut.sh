#!/usr/bin/env bash
set -euo pipefail

# Local-only profiling ladder for the NS Agda dependency cuts.
#
# This intentionally does NOT invoke GitHub Actions.  It uses the repository's
# pinned Agda 2.9 wrapper, one worker, persistent cache, and a 20 GiB RTS heap.
# The expensive ABC inhabitation root is opt-in via FULL=1.

REPO_ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
cd "$REPO_ROOT"

export AGDA_JOBS="${AGDA_JOBS:-1}"
export AGDA_RTS_HEAP="${AGDA_RTS_HEAP:--M20G}"
export DASHI_NO_TMUX=1
export DASHI_AGDA29_EPHEMERAL="${DASHI_AGDA29_EPHEMERAL:-0}"
export DASHI_AGDA29_CLEAN="${DASHI_AGDA29_CLEAN:-0}"
export DASHI_AGDA29_CACHE_ROOT="${DASHI_AGDA29_CACHE_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/dashi-agda29-ns-cut}"

OUT_DIR="${NS_CUT_PROFILE_DIR:-$REPO_ROOT/.cache/ns-agda-cut-profile}"
mkdir -p "$OUT_DIR"
STAMP="$(date +%Y%m%d-%H%M%S)"
CSV="$OUT_DIR/profile-$STAMP.csv"

TARGETS=(
  "DASHI/Physics/Closure/NSTriadKNLuoFiniteRationalOrderCore.agda"
  "DASHI/Physics/Closure/NSTriadKNLuoFiniteEightPointSixThreeHolderBoundary.agda"
  "DASHI/Physics/Closure/NSTriadKNLuoFiniteEightPointSixThreeHolderTransportBoundary.agda"
  "DASHI/Physics/Closure/NSTriadKNLuoFiniteEightPointSixThreeHolderExact.agda"
  "DASHI/Physics/Closure/NSTriadKNLuoFiniteSixThreeKernelBranchBoundary.agda"
  "DASHI/Physics/Closure/NSTriadKNLuoFiniteSixThreeKernelEstimateExact.agda"
  "DASHI/Physics/Closure/NSTriadKNLuoFiniteSixThreeKernelDimensionFreeExact.agda"
  "DASHI/Physics/Closure/NSTriadKNABCLeafAssemblyRound58.agda"
)

if [ "${FULL:-0}" = "1" ]; then
  TARGETS+=("DASHI/Physics/Closure/NSTriadKNABCInhabitationRound58Exact.agda")
fi

printf 'target,rc,elapsed_seconds,max_rss_kib\n' > "$CSV"

echo "NS compiled-cut profile"
echo "  cache: $DASHI_AGDA29_CACHE_ROOT"
echo "  jobs:  $AGDA_JOBS"
echo "  heap:  $AGDA_RTS_HEAP"
echo "  csv:   $CSV"
echo

for target in "${TARGETS[@]}"; do
  slug="${target//\//__}"
  slug="${slug%.agda}"
  time_file="$OUT_DIR/$STAMP-$slug.time"
  log_file="$OUT_DIR/$STAMP-$slug.log"

  echo "=== $target ==="
  set +e
  /usr/bin/time -f '%e %M' -o "$time_file" \
    env AGDA_LOG_PATH="$log_file" \
      bash scripts/run_agda29_parallel_check.sh "$target"
  rc=$?
  set -e

  elapsed="NA"
  rss="NA"
  if [ -s "$time_file" ]; then
    read -r elapsed rss < "$time_file" || true
  fi
  printf '%s,%s,%s,%s\n' "$target" "$rc" "$elapsed" "$rss" >> "$CSV"
  echo "rc=$rc elapsed=${elapsed}s max_rss=${rss}KiB"
  echo

  if [ "$rc" -ne 0 ]; then
    echo "Stopping at first nonzero target; inspect $log_file" >&2
    exit "$rc"
  fi
done

# Produce the static graph ranking beside the measured ladder.  Previously
# observed RSS values may be injected by EXTRA_RSS_ARGS, e.g.
#   EXTRA_RSS_ARGS='--rss DASHI.Physics.Closure.Foo=15800'
# shellcheck disable=SC2086
python scripts/ns_agda_dependency_cut_audit.py \
  --root DASHI.Physics.Closure.NSTriadKNABCInhabitationRound58Exact \
  --show-dominators --top 40 ${EXTRA_RSS_ARGS:-} \
  > "$OUT_DIR/dependency-cut-$STAMP.txt"

echo "completed: $CSV"
echo "cut audit: $OUT_DIR/dependency-cut-$STAMP.txt"
