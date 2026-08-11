#!/usr/bin/env bash
set -euo pipefail

# Execute the same pinned Agda binary used by the repository checker, but make
# K/UIP opt-out explicit.  The Round-36 source scan separately rejects any
# module-local `--with-K` pragma, so a source file cannot silently re-enable K.
AGDA_FLAKE="${AGDA_FLAKE:-/home/c/Documents/code/agda#debug.bin}"
REAL_AGDA_BIN="${DASHI_REAL_AGDA_BIN:-$(nix build --no-link --print-out-paths "$AGDA_FLAKE")/bin/agda}"

exec "$REAL_AGDA_BIN" --without-K "$@"
