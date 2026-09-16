#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="${SLR_ARTICLE_RECURRENCE_SMOKE_ROOT:-/tmp/slr-article-recurrence-smoke}"
OUT_DIR="$ROOT/gwb-world"
SEED_TEXT="$ROOT/seed.txt"
CONSUMER_SPEC="$ROOT/article-recurrence.slrc"
CONSUMER_BIN="${SLR_CONSUMER_RESIDUAL_BIN:-}"

rm -rf "$ROOT"
mkdir -p "$ROOT"
printf 'Bush spoke.\n' > "$SEED_TEXT"

if [[ -z "$CONSUMER_BIN" ]] && command -v sensiblaw-consumer-residual >/dev/null 2>&1; then
  CONSUMER_BIN="$(command -v sensiblaw-consumer-residual)"
fi
[[ -n "$CONSUMER_BIN" && -x "$CONSUMER_BIN" ]] || {
  printf 'ERROR: rust-consumer-residual-unavailable; set SLR_CONSUMER_RESIDUAL_BIN or install sensiblaw-consumer-residual\n' >&2
  exit 1
}

"$CONSUMER_BIN" encode \
  --consumer-id smoke:q207:article-recurrence \
  --surface-id smoke:q207:article-recurrence-seed \
  --requirement need-patient patient any \
  --output "$CONSUMER_SPEC"

export SLR_SOURCE_TEXT="$SEED_TEXT"
export SLR_SOURCE_DOCUMENT_REF="smoke:q207:article-recurrence-seed"
export SLR_SOURCE_QID="Q207"
export SLR_SOURCE_LANGUAGE="en"
export SLR_SOURCE_REVISION_REF="smoke-seed-v1"
export SLR_CONSUMER_SPEC="$CONSUMER_SPEC"
export SLR_MAX_ITERATIONS=2
unset SLR_SPACY_OBSERVATION_STREAM || true
unset SLR_ROUTE_CANDIDATE_STREAM || true

printf 'SLR_ARTICLE_RECURRENCE_SMOKE qid=Q207 consumer=smoke:q207:article-recurrence requirement=need-patient candidate_only=true semantic_promotion=false\n'
"$HERE/run_world_research_iteration_loop.sh" "$ROOT" "$OUT_DIR" 0
