#!/usr/bin/env bash
set -euo pipefail

JOBS="${AGDA_JOBS:-8}"
AGDA_FLAKE="${AGDA_FLAKE:-/home/c/Documents/code/agda#debug.bin}"
REPO_ROOT="${DASHI_REPO_ROOT:-/home/c/Documents/code/dashi_agda}"
STDLIB_SRC="${AGDA_STDLIB_SRC:-/nix/store/pkks1pz1n2bci0pva1sxbydnc4xyliid-standard-library-2.3}"

if [ "$#" -eq 0 ]; then
  TARGETS=("DASHI/Everything.agda")
else
  TARGETS=("$@")
fi

AGDA_BIN="${AGDA_BIN:-$(nix build --no-link --print-out-paths "$AGDA_FLAKE")/bin/agda}"
DASHI_WORK="$(mktemp -d /tmp/dashi-agda29-shadow.XXXXXX)"
STDLIB_WORK="$(mktemp -d /tmp/agda-stdlib-2.3-shadow.XXXXXX)"

cleanup() {
  rm -rf "$DASHI_WORK" "$STDLIB_WORK"
}
trap cleanup EXIT

rsync -a --prune-empty-dirs \
  --include='*/' \
  --include='*.agda' \
  --include='*.lagda' \
  --include='*.lagda.md' \
  --include='*.lagda.rst' \
  --include='*.lagda.tex' \
  --exclude='*' \
  "$REPO_ROOT/" "$DASHI_WORK/"

rsync -a "$STDLIB_SRC/" "$STDLIB_WORK/"
chmod -R u+w "$STDLIB_WORK"

cd "$DASHI_WORK"
for target in "${TARGETS[@]}"; do
  "$AGDA_BIN" \
    --no-libraries --no-default-libraries \
    "-j$JOBS" \
    -i . -i DCHoTT-Agda -i cubical -i "$STDLIB_WORK/src" \
    -WnoUnsupportedIndexedMatch \
    "$target"
done
