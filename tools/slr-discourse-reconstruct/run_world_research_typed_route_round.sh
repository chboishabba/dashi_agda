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
SYNTHETIC_ITERATION="$ROUND_DIR/typed-route-input-iteration.json"

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

# Adapt typed route choices to the existing bounded round ABI.  Missing-surface
# obligations are retained independently; each selected route contributes one
# explicit target-QID obligation with route metadata attached for audit.
python3 - "$INPUT_ITERATION" "$ROUTE_PLAN" "$SYNTHETIC_ITERATION" <<'PY'
import json, sys
from pathlib import Path
iteration=json.load(open(sys.argv[1], encoding='utf-8'))
plan=json.load(open(sys.argv[2], encoding='utf-8'))
missing=[x for x in iteration.get('next_acquisition_obligations') or [] if isinstance(x,dict) and x.get('obligation_kind')=='missing-language-surface']
route_rows=[]
for a in plan.get('selected_route_actions') or []:
    route_rows.append({
      'obligation_kind':'follow-related-qid',
      'qid':a.get('target_qid',''),
      'cross_language_gap_coverage':a.get('cross_language_gap_coverage',0),
      'source_surface_support':a.get('source_surface_support',0),
      'root_qid_support':a.get('root_qid_support',0),
      'typed_wikidata_property_target':bool(a.get('property_id')),
      'route_action_id':a.get('action_id',''),
      'route_family':a.get('route_family',''),
      'route_source_qid':a.get('source_qid',''),
      'route_property_id':a.get('property_id',''),
      'route_direction':a.get('route_direction',''),
      'pareto_front_rank':a.get('pareto_front_rank',0),
      'candidate_only':True,
      'semantic_promotion':False,
    })
iteration['next_acquisition_obligations']=missing+route_rows
iteration['typed_route_plan_reference']=str(Path(sys.argv[2]))
iteration['typed_route_selection_rewrites_truth']=False
iteration['semantic_promotion']=False
Path(sys.argv[3]).write_text(json.dumps(iteration, indent=2, sort_keys=True)+'\n', encoding='utf-8')
PY

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
[[ -s "$ROUND_DIR/typed-route-yield-history.stderr" ]] && cat "$ROUND_DIR/typed-route-yield-history.stderr"
printf 'typed_route_plan=%s\ntyped_route_history=%s\nround_dir=%s\n' "$ROUTE_PLAN" "$ROUTE_HISTORY" "$ROUND_DIR"
