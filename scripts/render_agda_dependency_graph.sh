#!/usr/bin/env bash
set -euo pipefail

resolve_agda_bin() {
  if [ -n "${AGDA_BIN:-}" ]; then
    printf '%s\n' "${AGDA_BIN}"
    return 0
  fi

  local candidate_store candidate_bin
  candidate_store="$(nix build --no-link --print-out-paths /home/c/Documents/code/agda#debug.bin 2>/dev/null)"
  candidate_bin="${candidate_store}/bin/agda"
  if [ -n "$candidate_store" ] && [ -x "$candidate_bin" ]; then
    printf '%s\n' "$candidate_bin"
    return 0
  fi

  if command -v agda >/dev/null 2>&1; then
    command -v agda
    return 0
  fi

  echo agda
}

MODULE="${1:-DASHI/Everything.agda}"
OUTPUT_DIR="${2:-/tmp}"
AGDA_BIN="$(resolve_agda_bin)"

if ! command -v "$AGDA_BIN" >/dev/null 2>&1; then
  echo "error: agda binary not found: ${AGDA_BIN}" >&2
  exit 1
fi

if ! command -v dot >/dev/null 2>&1; then
  echo "error: graphviz 'dot' not found" >&2
  exit 1
fi

if [[ ! -f "${MODULE}" ]]; then
  echo "error: module file not found: ${MODULE}" >&2
  exit 1
fi

mkdir -p "${OUTPUT_DIR}"

base="$(basename "${MODULE}" .agda)"
dot_file="${OUTPUT_DIR}/${base}.dot"
svg_file="${OUTPUT_DIR}/${base}.svg"

echo "Step 1: generating Agda dependency graph for ${MODULE}..."
"$AGDA_BIN" \
  --dependency-graph="${dot_file}" \
  -i . \
  -i DCHoTT-Agda \
  -i cubical \
  -l standard-library \
  "${MODULE}"

echo "Step 2: rendering SVG..."
if command -v tred >/dev/null 2>&1; then
  tred "${dot_file}" | dot -Tsvg > "${svg_file}"
  echo "Applied transitive reduction."
else
  dot -Tsvg "${dot_file}" > "${svg_file}"
  echo "Rendered without transitive reduction."
fi

echo "DOT: ${dot_file}"
echo "SVG: ${svg_file}"
