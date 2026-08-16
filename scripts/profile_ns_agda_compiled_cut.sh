#!/usr/bin/env bash
set -euo pipefail

# Local-only profiling ladder for the NS Agda dependency cuts.
#
# This intentionally does NOT invoke GitHub Actions.  It uses the repository's
# pinned Agda 2.9 wrapper, one worker, persistent cache, and a 20 GiB RTS heap.
# The canonical ABC inhabitation module is now part of the normal ladder because
# its historical Com envelope transport has been split into a separate adapter.
# LEGACY=1 adds that adapter; FULL=1 additionally retries the conjectural/heavy
# downstream package after the lightweight boundary is known healthy.
#
# Round 61 profiling showed the previous dimension-free route reached the legacy
# recursive finite-Gram theorem first (~263.5 s in finiteGramStep) and then hit
# the historical ConstantOneV2 let-binding parser error.  The ladder therefore
# checks the new compiled constant-one Holder module explicitly before the
# dimension-free kernel consumer; neither should now require the legacy Gram
# graph.  This is the path intended to remain runnable on a 32 GiB workstation.

REPO_ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
cd "$REPO_ROOT"
export DASHI_REPO_ROOT="$REPO_ROOT"

export AGDA_JOBS="${AGDA_JOBS:-1}"
export AGDA_RTS_HEAP="${AGDA_RTS_HEAP:-20G}"
export DASHI_NO_TMUX=1
export DASHI_AGDA29_EPHEMERAL="${DASHI_AGDA29_EPHEMERAL:-0}"
INITIAL_CLEAN="${DASHI_AGDA29_CLEAN:-0}"
export DASHI_AGDA29_CLEAN=0
export DASHI_AGDA29_CACHE_ROOT="${DASHI_AGDA29_CACHE_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/dashi-agda29-ns-cut}"

if [ -x /usr/bin/time ]; then
  TIME_CMD=(/usr/bin/time)
else
  TIME_CMD=(nix shell nixpkgs#time --command time)
fi

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
  "DASHI/Physics/Closure/NSTriadKNLuoFiniteSixThreeHolderConstantOneCompiledExact.agda"
  "DASHI/Physics/Closure/NSTriadKNLuoFiniteSixThreeKernelDimensionFreeExact.agda"
  "DASHI/Physics/Closure/NSTriadKNABCLeafAssemblyRound58.agda"
  "DASHI/Physics/Closure/NSTriadKNABCInhabitationRound58Exact.agda"
)

if [ "${LEGACY:-0}" = "1" ]; then
  TARGETS+=("DASHI/Physics/Closure/NSTriadKNABCComLegacyEnvelopeAdapterRound60Exact.agda")
fi

if [ "${FULL:-0}" = "1" ]; then
  TARGETS+=("DASHI/Physics/Closure/NSTriadKNABCConjecturalSourceRound58Exact.agda")
fi

printf 'target,rc,elapsed_seconds,max_rss_kib\n' > "$CSV"

echo "NS compiled-cut profile"
echo "  cache:  $DASHI_AGDA29_CACHE_ROOT"
echo "  jobs:   $AGDA_JOBS"
echo "  heap:   $AGDA_RTS_HEAP"
echo "  legacy: ${LEGACY:-0}"
echo "  full:   ${FULL:-0}"
echo "  csv:    $CSV"
echo

first_target=1
for target in "${TARGETS[@]}"; do
  slug="${target//\//__}"
  slug="${slug%.agda}"
  time_file="$OUT_DIR/$STAMP-$slug.time"
  log_file="$OUT_DIR/$STAMP-$slug.log"

  echo "=== $target ==="
  set +e
  clean_for_target=0
  if [ "$first_target" -eq 1 ]; then
    clean_for_target="$INITIAL_CLEAN"
  fi
  "${TIME_CMD[@]}" -f '%e %M' -o "$time_file" \
    env AGDA_LOG_PATH="$log_file" \
      DASHI_AGDA29_CLEAN="$clean_for_target" \
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
  first_target=0
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
