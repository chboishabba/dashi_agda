#!/usr/bin/env bash
set -euo pipefail

HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
OUT_DIR="${2:-$HANDOFF_ROOT/gwb-world}"
ITERATION_INDEX="${3:-0}"
ENV_FILE="${SLR_WORLD_ENV_FILE:-.env}"
WORLD_COMPILER_BIN="${SLR_WORLD_COMPILER_BIN:-}"
WORLD_STORE_BIN="${SLR_WORLD_STORE_BIN:-}"
SLR_SPACY_OBSERVATION_STREAM="${SLR_SPACY_OBSERVATION_STREAM:-}"
ROUND_DIR="$OUT_DIR/world-research-rounds/round-$ITERATION_INDEX"
SLR_WORLD_WIRE_STREAM="$ROUND_DIR/world-wire.slrw"
COMPILER_ERR="$ROUND_DIR/world-compiler.stderr"
PG_RECEIPT="$ROUND_DIR/postgres-world-persistence-receipt.txt"
PG_FRONTIER="$ROUND_DIR/postgres-latest-frontier.slrw"
PG_ERR="$ROUND_DIR/postgres-world-persistence.stderr"

mkdir -p "$ROUND_DIR"

if [[ -z "$WORLD_COMPILER_BIN" ]] && command -v sensiblaw-world-compiler >/dev/null 2>&1; then
  WORLD_COMPILER_BIN="$(command -v sensiblaw-world-compiler)"
fi
if [[ -z "$WORLD_COMPILER_BIN" || ! -x "$WORLD_COMPILER_BIN" ]]; then
  printf 'ERROR: rust-world-compiler-unavailable; set SLR_WORLD_COMPILER_BIN or install sensiblaw-world-compiler\n' >&2
  exit 1
fi

if [[ -z "$SLR_SPACY_OBSERVATION_STREAM" || ! -s "$SLR_SPACY_OBSERVATION_STREAM" ]]; then
  printf 'ERROR: binary-observation-wire-unavailable; set SLR_SPACY_OBSERVATION_STREAM to a non-empty SLRO stream produced by the trained-spaCy observation boundary\n' >&2
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

if [[ -z "$WORLD_STORE_BIN" ]] && command -v sensiblaw-world-store >/dev/null 2>&1; then
  WORLD_STORE_BIN="$(command -v sensiblaw-world-store)"
fi
if [[ -z "$WORLD_STORE_BIN" || ! -x "$WORLD_STORE_BIN" ]]; then
  printf 'ERROR: rust-world-store-unavailable; set SLR_WORLD_STORE_BIN or install sensiblaw-world-store\n' >&2
  exit 1
fi

"$WORLD_STORE_BIN" ingest-wire \
  --input "$SLR_WORLD_WIRE_STREAM" \
  --env-file "$ENV_FILE" \
  > "$PG_RECEIPT" \
  2> "$PG_ERR"

"$WORLD_STORE_BIN" frontier \
  --env-file "$ENV_FILE" \
  > "$PG_FRONTIER" \
  2>> "$PG_ERR"

printf 'SLR_WORLD_PIPELINE_BACKEND observation_wire=SLRO compiler=rust-world-compiler world_wire=SLRW store=rust-world-store binary_wire=true json_transport=false regex_world_parser=false python_heavy_persistence=false postgres_persistence_is_semantic_authority=false\n' >> "$PG_ERR"

printf 'spacy_observation_stream=%s\nworld_wire_stream=%s\ncompiler_stderr=%s\npostgres_receipt=%s\npostgres_latest_frontier=%s\nround_dir=%s\n' \
  "$SLR_SPACY_OBSERVATION_STREAM" "$SLR_WORLD_WIRE_STREAM" "$COMPILER_ERR" "$PG_RECEIPT" "$PG_FRONTIER" "$ROUND_DIR"
