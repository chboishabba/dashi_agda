#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-mabo-proof-graph}"
OUT_DIR="${2:-$HANDOFF_ROOT/mabo-proof-graph}"
START_ITERATION="${3:-0}"
SLR_MABO_CONSUMER_SPEC="${SLR_MABO_CONSUMER_SPEC:-}"
SLR_SOURCE_TEXT="${SLR_SOURCE_TEXT:-}"
SLR_SOURCE_DOCUMENT_REF="${SLR_SOURCE_DOCUMENT_REF:-}"
SLR_SOURCE_QID="${SLR_SOURCE_QID:-}"
SLR_SOURCE_REVISION_REF="${SLR_SOURCE_REVISION_REF:-}"
SLR_MAX_ITERATIONS="${SLR_MAX_ITERATIONS:-3}"

[[ -n "$SLR_MABO_CONSUMER_SPEC" && -s "$SLR_MABO_CONSUMER_SPEC" ]] || {
  printf 'ERROR: mabo-profile-unavailable; set SLR_MABO_CONSUMER_SPEC to the SensibLaw-owned binary SLRC profile\n' >&2
  exit 1
}

if [[ -z "$SLR_SOURCE_TEXT" || ! -s "$SLR_SOURCE_TEXT" || -z "$SLR_SOURCE_DOCUMENT_REF" || -z "$SLR_SOURCE_QID" || -z "$SLR_SOURCE_REVISION_REF" ]]; then
  printf 'ERROR: mabo-source-metadata-incomplete; require SLR_SOURCE_TEXT, SLR_SOURCE_DOCUMENT_REF, SLR_SOURCE_QID, SLR_SOURCE_REVISION_REF\n' >&2
  exit 1
fi

export SLR_CONSUMER_SPEC="$SLR_MABO_CONSUMER_SPEC"
export SLR_SOURCE_TEXT
export SLR_SOURCE_DOCUMENT_REF
export SLR_SOURCE_QID
export SLR_SOURCE_REVISION_REF
export SLR_MAX_ITERATIONS

mkdir -p "$OUT_DIR"

"$HERE/run_world_research_iteration_loop.sh" \
  "$HANDOFF_ROOT" "$OUT_DIR" "$START_ITERATION"

printf 'SLR_MABO_PROFILE_RECEIPT legal_semantics_owner=SensibLaw research_recurrence_owner=SLR consumer_wire=SLRC candidate_only=true semantic_promotion=false profile_executes_legal_semantics=false\n'
