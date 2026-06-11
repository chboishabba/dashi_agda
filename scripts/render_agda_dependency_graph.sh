#!/usr/bin/env bash
set -euo pipefail

MODULE="${1:-DASHI/Everything.agda}"
OUTPUT_DIR="${2:-/tmp}"

if ! command -v agda >/dev/null 2>&1; then
  echo "error: agda not found" >&2
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
agda \
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
