#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
OUT_DIR="${2:-$HANDOFF_ROOT/gwb-world}"
ITERATION_INDEX="${3:-0}"
ENV_FILE="${SLR_WORLD_ENV_FILE:-.env}"
WORLD_COMPILER_BIN="${SLR_WORLD_COMPILER_BIN:-}"
CONSUMER_RESIDUAL_BIN="${SLR_CONSUMER_RESIDUAL_BIN:-}"
RESIDUAL_PLANNER_BIN="${SLR_RESIDUAL_PLANNER_BIN:-}"
WORLD_STORE_BIN="${SLR_WORLD_STORE_BIN:-}"
SLR_SPACY_OBSERVATION_STREAM="${SLR_SPACY_OBSERVATION_STREAM:-}"
SLR_CONSUMER_SPEC="${SLR_CONSUMER_SPEC:-}"
SLR_SOURCE_TEXT="${SLR_SOURCE_TEXT:-}"
SLR_SOURCE_DOCUMENT_REF="${SLR_SOURCE_DOCUMENT_REF:-}"
SLR_SOURCE_QID="${SLR_SOURCE_QID:-}"
SLR_SOURCE_LANGUAGE="${SLR_SOURCE_LANGUAGE:-en}"
SLR_SOURCE_REVISION_REF="${SLR_SOURCE_REVISION_REF:-}"
SLR_SPACY_MODEL="${SLR_SPACY_MODEL:-}"
ROUND_DIR="$OUT_DIR/world-research-rounds/round-$ITERATION_INDEX"
GENERATED_OBSERVATIONS="$ROUND_DIR/spacy-observations.slro"
SLR_WORLD_WIRE_STREAM="$ROUND_DIR/world-wire.slrw"
SLR_RESIDUAL_WORLD_STREAM="$ROUND_DIR/residual-world.slrw"
SLR_ROUTE_INTENTS="$ROUND_DIR/route-intents.slrw"
SPACY_ERR="$ROUND_DIR/spacy-observation.stderr"
COMPILER_ERR="$ROUND_DIR/world-compiler.stderr"
RESIDUAL_ERR="$ROUND_DIR/consumer-residual.stderr"
PLANNER_ERR="$ROUND_DIR/residual-planner.stderr"
PG_RECEIPT="$ROUND_DIR/postgres-world-persistence-receipt.txt"
PG_FRONTIER="$ROUND_DIR/postgres-latest-frontier.slrw"
PG_ERR="$ROUND_DIR/postgres-world-persistence.stderr"

mkdir -p "$ROUND_DIR"

if [[ -z "$SLR_SPACY_OBSERVATION_STREAM" ]]; then
  if [[ -z "$SLR_SOURCE_TEXT" || ! -s "$SLR_SOURCE_TEXT" ]]; then
    printf 'ERROR: binary-observation-wire-unavailable; set SLR_SPACY_OBSERVATION_STREAM or SLR_SOURCE_TEXT\n' >&2
    exit 1
  fi
  if [[ -z "$SLR_SOURCE_DOCUMENT_REF" || -z "$SLR_SOURCE_QID" || -z "$SLR_SOURCE_REVISION_REF" ]]; then
    printf 'ERROR: source-observation-metadata-incomplete; require SLR_SOURCE_DOCUMENT_REF, SLR_SOURCE_QID, SLR_SOURCE_REVISION_REF\n' >&2
    exit 1
  fi
  spacy_args=(
    --text "$SLR_SOURCE_TEXT"
    --document-ref "$SLR_SOURCE_DOCUMENT_REF"
    --qid "$SLR_SOURCE_QID"
    --language "$SLR_SOURCE_LANGUAGE"
    --revision-ref "$SLR_SOURCE_REVISION_REF"
    --output "$GENERATED_OBSERVATIONS"
  )
  [[ -n "$SLR_SPACY_MODEL" ]] && spacy_args+=(--model "$SLR_SPACY_MODEL")
  python3 "$HERE/slr_spacy_observation_wire.py" "${spacy_args[@]}" 2> "$SPACY_ERR"
  SLR_SPACY_OBSERVATION_STREAM="$GENERATED_OBSERVATIONS"
fi

if [[ ! -s "$SLR_SPACY_OBSERVATION_STREAM" ]]; then
  printf 'ERROR: binary-observation-wire-unavailable; trained-spaCy boundary produced no SLRO frames\n' >&2
  exit 1
fi

if [[ -z "$WORLD_COMPILER_BIN" ]] && command -v sensiblaw-world-compiler >/dev/null 2>&1; then
  WORLD_COMPILER_BIN="$(command -v sensiblaw-world-compiler)"
fi
if [[ -z "$WORLD_COMPILER_BIN" || ! -x "$WORLD_COMPILER_BIN" ]]; then
  printf 'ERROR: rust-world-compiler-unavailable; set SLR_WORLD_COMPILER_BIN or install sensiblaw-world-compiler\n' >&2
  exit 1
fi

"$WORLD_COMPILER_BIN" compile \
  --input "$SLR_SPACY_OBSERVATION_STREAM" \
  --output "$SLR_WORLD_WIRE_STREAM" \
  --iteration "$ITERATION_INDEX" \
  2> "$COMPILER_ERR"

if [[ ! -s "$SLR_WORLD_WIRE_STREAM" ]]; then
  printf 'ERROR: binary-world-wire-unavailable; world compiler produced no SLRW frames\n' >&2
  exit 1
fi

if [[ -z "$SLR_CONSUMER_SPEC" || ! -s "$SLR_CONSUMER_SPEC" ]]; then
  printf 'ERROR: binary-consumer-spec-unavailable; set SLR_CONSUMER_SPEC to a non-empty .slrc typed consumer specification\n' >&2
  exit 1
fi

if [[ -z "$CONSUMER_RESIDUAL_BIN" ]] && command -v sensiblaw-consumer-residual >/dev/null 2>&1; then
  CONSUMER_RESIDUAL_BIN="$(command -v sensiblaw-consumer-residual)"
fi
if [[ -z "$CONSUMER_RESIDUAL_BIN" || ! -x "$CONSUMER_RESIDUAL_BIN" ]]; then
  printf 'ERROR: rust-consumer-residual-unavailable; set SLR_CONSUMER_RESIDUAL_BIN or install sensiblaw-consumer-residual\n' >&2
  exit 1
fi

"$CONSUMER_RESIDUAL_BIN" compile \
  --world "$SLR_WORLD_WIRE_STREAM" \
  --consumer "$SLR_CONSUMER_SPEC" \
  --output "$SLR_RESIDUAL_WORLD_STREAM" \
  --iteration "$ITERATION_INDEX" \
  2> "$RESIDUAL_ERR"

if [[ ! -s "$SLR_RESIDUAL_WORLD_STREAM" ]]; then
  printf 'ERROR: residual-world-wire-unavailable; consumer residual compiler produced no SLRW frames\n' >&2
  exit 1
fi

if [[ -z "$WORLD_STORE_BIN" ]] && command -v sensiblaw-world-store >/dev/null 2>&1; then
  WORLD_STORE_BIN="$(command -v sensiblaw-world-store)"
fi
if [[ -z "$WORLD_STORE_BIN" || ! -x "$WORLD_STORE_BIN" ]]; then
  printf 'ERROR: rust-world-store-unavailable; set SLR_WORLD_STORE_BIN or install sensiblaw-world-store\n' >&2
  exit 1
fi

"$WORLD_STORE_BIN" ingest-wire \
  --input "$SLR_RESIDUAL_WORLD_STREAM" \
  --env-file "$ENV_FILE" \
  > "$PG_RECEIPT" \
  2> "$PG_ERR"

"$WORLD_STORE_BIN" frontier \
  --env-file "$ENV_FILE" \
  > "$PG_FRONTIER" \
  2>> "$PG_ERR"

if [[ -z "$RESIDUAL_PLANNER_BIN" ]] && command -v sensiblaw-residual-planner >/dev/null 2>&1; then
  RESIDUAL_PLANNER_BIN="$(command -v sensiblaw-residual-planner)"
fi
if [[ -z "$RESIDUAL_PLANNER_BIN" || ! -x "$RESIDUAL_PLANNER_BIN" ]]; then
  printf 'ERROR: rust-residual-planner-unavailable; set SLR_RESIDUAL_PLANNER_BIN or install sensiblaw-residual-planner\n' >&2
  exit 1
fi

"$RESIDUAL_PLANNER_BIN" plan \
  --frontier "$PG_FRONTIER" \
  --output "$SLR_ROUTE_INTENTS" \
  2> "$PLANNER_ERR"

printf 'SLR_WORLD_PIPELINE_BACKEND spacy_boundary=python-local observation_wire=SLRO compiler=rust-world-compiler consumer_spec=SLRC residual_compiler=rust-consumer-residual active_frontier=rust-world-store producer_planner=rust-residual-planner world_wire=SLRW store=rust-world-store binary_wire=true json_transport=false regex_world_parser=false python_world_semantics=false postgres_persistence_is_semantic_authority=false route_intent_is_claim_truth=false\n' >> "$PG_ERR"

printf 'spacy_observation_stream=%s\nworld_wire_stream=%s\nconsumer_spec=%s\nresidual_world_stream=%s\nspacy_stderr=%s\ncompiler_stderr=%s\nresidual_stderr=%s\npostgres_receipt=%s\npostgres_latest_frontier=%s\nroute_intents=%s\nplanner_stderr=%s\nround_dir=%s\n' \
  "$SLR_SPACY_OBSERVATION_STREAM" "$SLR_WORLD_WIRE_STREAM" "$SLR_CONSUMER_SPEC" "$SLR_RESIDUAL_WORLD_STREAM" "$SPACY_ERR" "$COMPILER_ERR" "$RESIDUAL_ERR" "$PG_RECEIPT" "$PG_FRONTIER" "$SLR_ROUTE_INTENTS" "$PLANNER_ERR" "$ROUND_DIR"
