#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
OUT_DIR="${2:-$HANDOFF_ROOT/gwb-world}"
ITERATION_INDEX="${3:-3}"
INPUT_ITERATION="${4:-$OUT_DIR/world-research-rounds/round-$((ITERATION_INDEX-1))/world-research-iteration.json}"
BASE_GRAPH="${5:-$OUT_DIR/world-research-rounds/round-$((ITERATION_INDEX-1))/merged-wikimedia-world-graph.json}"
LANGUAGES="${6:-en,es,fr,de,simple}"
MAX_TARGETS="${SLR_WORLD_MAX_TYPED_ROUTE_TARGETS:-4}"
MAX_MISSING="${SLR_WORLD_MAX_MISSING_SURFACES_PER_ITERATION:-4}"
ROUNDS_DIR="$OUT_DIR/world-research-rounds"
ROUND_DIR="$ROUNDS_DIR/round-$ITERATION_INDEX"
ROUTE_PLAN="$ROUND_DIR/typed-route-plan.json"
ROUTE_SEEDS="$ROUND_DIR/typed-route-selected-seeds.jsonl"
ROUTE_PLAN_ERR="$ROUND_DIR/typed-route-plan.stderr"
ROUTE_HISTORY="$ROUNDS_DIR/route-yield-history.json"
ROUTE_HISTORY_NEXT="$ROUND_DIR/route-yield-history.json"
SYNTHETIC_CLOSURE="$ROUND_DIR/typed-route-input-closure.json"
SYNTHETIC_ITERATION="$ROUND_DIR/typed-route-input-iteration.json"
FRONTIER_WELD_ERR="$ROUND_DIR/typed-route-frontier-weld.stderr"

mkdir -p "$ROUND_DIR"
[[ -s "$INPUT_ITERATION" ]] || { echo "ERROR: missing input iteration $INPUT_ITERATION" >&2; exit 1; }
[[ -s "$BASE_GRAPH" ]] || { echo "ERROR: missing base graph $BASE_GRAPH" >&2; exit 1; }

PREVIOUS_CLOSURE="$(python3 - "$INPUT_ITERATION" <<'PY'
import json, sys
m=json.load(open(sys.argv[1], encoding='utf-8'))
print(str(m.get('semantic_closure_reference','')))
PY
)"
[[ -s "$PREVIOUS_CLOSURE" ]] || { echo "ERROR: missing previous closure $PREVIOUS_CLOSURE" >&2; exit 1; }

python3 "$HERE/slr_world_research_route_pareto.py" self-check 2> "$ROUND_DIR/typed-route-self-check.stderr"
route_args=(
  plan
  --closure "$PREVIOUS_CLOSURE"
  --graph "$BASE_GRAPH"
  --output "$ROUTE_PLAN"
  --seeds "$ROUTE_SEEDS"
  --iteration-index "$ITERATION_INDEX"
  --max-targets "$MAX_TARGETS"
)
[[ -s "$ROUTE_HISTORY" ]] && route_args+=(--history "$ROUTE_HISTORY")
python3 "$HERE/slr_world_research_route_pareto.py" "${route_args[@]}" 2> "$ROUTE_PLAN_ERR"

grep -q 'pareto_dimensions_scalarized=false' "$ROUTE_PLAN_ERR" || { cat "$ROUTE_PLAN_ERR" >&2; exit 1; }
grep -q 'typed_property_is_claim_truth=false' "$ROUTE_PLAN_ERR" || { cat "$ROUTE_PLAN_ERR" >&2; exit 1; }
grep -q 'ibrahim_historical_equivalence=false' "$ROUTE_PLAN_ERR" || { cat "$ROUTE_PLAN_ERR" >&2; exit 1; }

# Weld the selected typed route actions into a synthetic closure and iteration.
# The bounded round refresh logic keys off semantic_closure_reference; pointing
# it at the locked synthetic closure prevents the generic planner from replacing
# the typed targets with unrelated high-Pareto QIDs.
python3 "$HERE/slr_world_research_typed_route_frontier.py" \
  --iteration "$INPUT_ITERATION" \
  --closure "$PREVIOUS_CLOSURE" \
  --plan "$ROUTE_PLAN" \
  --output-closure "$SYNTHETIC_CLOSURE" \
  --output-iteration "$SYNTHETIC_ITERATION" \
  2> "$FRONTIER_WELD_ERR"

grep -q 'typed_route_frontier_locked=true' "$FRONTIER_WELD_ERR" || { cat "$FRONTIER_WELD_ERR" >&2; exit 1; }

grep -q 'typed_route_selection_rewrites_truth=false' "$FRONTIER_WELD_ERR" || { cat "$FRONTIER_WELD_ERR" >&2; exit 1; }

SELECTED_TARGETS="$(python3 - "$ROUTE_PLAN" <<'PY'
import json, sys
p=json.load(open(sys.argv[1], encoding='utf-8'))
print(len(p.get('selected_route_actions') or []))
PY
)"

SLR_WORLD_MAX_NEW_QIDS_PER_ITERATION="$SELECTED_TARGETS" \
SLR_WORLD_MAX_MISSING_SURFACES_PER_ITERATION="$MAX_MISSING" \
SLR_WORLD_FOLLOW_MAX_DEPTH=0 \
bash "$HERE/run_world_research_budgeted_round.sh" \
  "$HANDOFF_ROOT" "$OUT_DIR" "$ITERATION_INDEX" "$SYNTHETIC_ITERATION" "$BASE_GRAPH" "$LANGUAGES"

# Strong execution weld: the QIDs actually selected by the inner bounded plan
# must equal the typed-route targets.  Any drift means route-controlled
# execution failed and the round is invalid.
python3 - "$ROUTE_PLAN" "$ROUND_DIR/budget-plan.json" <<'PY'
import json, sys
route=json.load(open(sys.argv[1], encoding='utf-8'))
budget=json.load(open(sys.argv[2], encoding='utf-8'))
expected=sorted({str(x.get('target_qid','')) for x in route.get('selected_route_actions') or [] if x.get('target_qid')})
actual=sorted({str(x.get('qid','')) for x in budget.get('selected_related_qids') or [] if x.get('qid')})
if actual != expected:
    raise SystemExit(f"typed-route execution mismatch: expected={expected} actual={actual}")
print('SLR_TYPED_ROUTE_EXECUTION_WELD_RECEIPT selected_targets_match=true inner_replanning_changed_targets=false candidate_only=true semantic_promotion=false')
PY

GAP_FLOW="$ROUND_DIR/semantic-gap-flow.json"
DELTA_GRAPH="$ROUND_DIR/wikimedia-delta-graph.json"
if [[ -s "$GAP_FLOW" && -s "$DELTA_GRAPH" ]]; then
  hist_args=(
    update-history
    --plan "$ROUTE_PLAN"
    --gap-flow "$GAP_FLOW"
    --delta-graph "$DELTA_GRAPH"
    --output "$ROUTE_HISTORY_NEXT"
  )
  [[ -s "$ROUTE_HISTORY" ]] && hist_args+=(--history "$ROUTE_HISTORY")
  python3 "$HERE/slr_world_research_route_pareto.py" "${hist_args[@]}" 2> "$ROUND_DIR/typed-route-yield-history.stderr"
  cp "$ROUTE_HISTORY_NEXT" "$ROUTE_HISTORY"
fi

cat "$ROUTE_PLAN_ERR"
cat "$FRONTIER_WELD_ERR"
[[ -s "$ROUND_DIR/typed-route-yield-history.stderr" ]] && cat "$ROUND_DIR/typed-route-yield-history.stderr"
printf 'typed_route_plan=%s\ntyped_route_history=%s\nround_dir=%s\n' "$ROUTE_PLAN" "$ROUTE_HISTORY" "$ROUND_DIR"
