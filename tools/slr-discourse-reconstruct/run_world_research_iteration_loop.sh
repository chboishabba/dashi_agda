#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
OUT_DIR="${2:-$HANDOFF_ROOT/gwb-world}"
START_ITERATION="${3:-0}"
SLR_MAX_ITERATIONS="${SLR_MAX_ITERATIONS:-3}"

case "$SLR_MAX_ITERATIONS" in
  ''|*[!0-9]*)
    printf 'ERROR: SLR_MAX_ITERATIONS must be a positive integer\n' >&2
    exit 2
    ;;
esac
if (( SLR_MAX_ITERATIONS < 1 )); then
  printf 'ERROR: SLR_MAX_ITERATIONS must be a positive integer\n' >&2
  exit 2
fi

current_observation="${SLR_SPACY_OBSERVATION_STREAM:-}"
iteration="$START_ITERATION"
completed=0

while (( completed < SLR_MAX_ITERATIONS )); do
  round_dir="$OUT_DIR/world-research-rounds/round-$iteration"
  mkdir -p "$round_dir"

  if [[ -n "$current_observation" ]]; then
    export SLR_SPACY_OBSERVATION_STREAM="$current_observation"
  else
    unset SLR_SPACY_OBSERVATION_STREAM || true
  fi

  "$HERE/run_world_research_typed_route_round.sh" \
    "$HANDOFF_ROOT" "$OUT_DIR" "$iteration" \
    > "$round_dir/iteration-round.stdout"

  completed=$((completed + 1))
  next_observation="$round_dir/next-spacy-observations.slro"
  round_observation="$round_dir/spacy-observations.slro"

  if [[ ! -s "$next_observation" ]]; then
    printf 'SLR_ITERATION_CONTROL iteration=%s completed=%s decision=bounded-stop:no-next-observation candidate_only=true semantic_promotion=false\n' \
      "$iteration" "$completed"
    exit 0
  fi

  comparison_observation="$current_observation"
  if [[ -z "$comparison_observation" && -s "$round_observation" ]]; then
    comparison_observation="$round_observation"
  fi

  if [[ -n "$comparison_observation" && -s "$comparison_observation" ]] && cmp -s "$comparison_observation" "$next_observation"; then
    printf 'SLR_ITERATION_CONTROL iteration=%s completed=%s decision=bounded-stop:repeated-observation candidate_only=true semantic_promotion=false\n' \
      "$iteration" "$completed"
    exit 0
  fi

  if (( completed >= SLR_MAX_ITERATIONS )); then
    printf 'SLR_ITERATION_CONTROL iteration=%s completed=%s decision=bounded-stop:max-iterations candidate_only=true semantic_promotion=false\n' \
      "$iteration" "$completed"
    exit 0
  fi

  printf 'SLR_ITERATION_CONTROL iteration=%s completed=%s decision=continue:next-observation candidate_only=true semantic_promotion=false\n' \
    "$iteration" "$completed"
  current_observation="$next_observation"
  iteration=$((iteration + 1))
done

printf 'SLR_ITERATION_CONTROL iteration=%s completed=%s decision=bounded-stop:max-iterations candidate_only=true semantic_promotion=false\n' \
  "$iteration" "$completed"
