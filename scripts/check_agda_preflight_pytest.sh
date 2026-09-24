#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

TARGET="${AGDA_PREFLIGHT_TARGET:-DASHI/Everything.agda}"

exec python -m pytest \
  --agda-preflight \
  --agda-deps \
  --agda-root "$ROOT" \
  "$TARGET" \
  -vv \
  "$@"
