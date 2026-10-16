#!/usr/bin/env bash
set -euo pipefail

# Reproducible external rigorous-certificate runner.
#
# This script deliberately fails if FLINT is unavailable; it never falls back
# to mpmath or ordinary floating point while claiming a rigorous certificate.
# The generated SHA-256 manifest pins the exact NDJSON bytes checked downstream.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC="$ROOT/scripts/monster_climbing_gym_flint_certify.c"
VERIFY="$ROOT/scripts/monster_climbing_gym_verify_rigorous_bundle.py"
OUT="${1:-$ROOT/generated/monster_climbing_gym_flint_849.ndjson}"
COUNT="${2:-849}"
PREC="${3:-256}"
BUILD_DIR="${TMPDIR:-/tmp}/dashi-monster-climbing-gym-flint"
BIN="$BUILD_DIR/monster_climbing_gym_flint_certify"

if ! command -v pkg-config >/dev/null 2>&1; then
  echo "pkg-config is required" >&2
  exit 2
fi
if ! pkg-config --exists flint; then
  echo "FLINT development package is required; refusing non-rigorous fallback" >&2
  exit 2
fi
if ! command -v python3 >/dev/null 2>&1; then
  echo "python3 is required for the exact dyadic bundle checker" >&2
  exit 2
fi

mkdir -p "$BUILD_DIR" "$(dirname "$OUT")"
cc -O2 -std=c11 "$SRC" $(pkg-config --cflags --libs flint) -o "$BIN"

"$BIN" "$COUNT" "$PREC" > "$OUT"
python3 "$VERIFY" "$OUT" --output "$OUT.verify.json"
sha256sum "$OUT" > "$OUT.sha256"

FLINT_VERSION="$(pkg-config --modversion flint)"
printf '%s\n' \
  "producer=FLINT acb_dirichlet + Arb" \
  "flint_pkg_config_version=$FLINT_VERSION" \
  "zero_count=$COUNT" \
  "precision_bits=$PREC" \
  "bundle=$(basename "$OUT")" \
  "bundle_sha256=$(cut -d' ' -f1 "$OUT.sha256")" \
  "external_producer_is_agda_proof=false" \
  > "$OUT.provenance.txt"

cat "$OUT.verify.json"
