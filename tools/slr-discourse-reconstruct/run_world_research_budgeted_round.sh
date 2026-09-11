#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
OUT_DIR="${2:-$HANDOFF_ROOT/gwb-world}"
ITERATION_INDEX="${3:-1}"
INPUT_ITERATION="${4:-$OUT_DIR/slr-world-research-iteration.json}"
BASE_GRAPH="${5:-$OUT_DIR/gwb-wikimedia-world-graph.json}"
LANGUAGES="${6:-en,es,fr,de,simple}"
MAX_NEW_QIDS="${SLR_WORLD_MAX_NEW_QIDS_PER_ITERATION:-8}"
MAX_MISSING_SURFACES="${SLR_WORLD_MAX_MISSING_SURFACES_PER_ITERATION:-4}"
MAX_DEPTH="${SLR_WORLD_FOLLOW_MAX_DEPTH:-1}"
ROUNDS_DIR="$OUT_DIR/world-research-rounds"
ROUND_DIR="$ROUNDS_DIR/round-$ITERATION_INDEX"
HISTORY="$ROUNDS_DIR/missing-surface-attempt-history.json"
HISTORY_NEXT="$ROUND_DIR/missing-surface-attempt-history.json"
PLAN="$ROUND_DIR/budget-plan.json"
SEEDS="$ROUND_DIR/selected-related-qid-seeds.jsonl"
PLAN_ERR="$ROUND_DIR/budget-plan.stderr"
DELTA_GRAPH="$ROUND_DIR/wikimedia-delta-graph.json"
DELTA_WORLD="$ROUND_DIR/wikimedia-delta-world.json"
FOLLOW_ERR="$ROUND_DIR/wikimedia-delta-follow.stderr"
MERGED_GRAPH="$ROUND_DIR/merged-wikimedia-world-graph.json"
MERGE_ERR="$ROUND_DIR/graph-merge.stderr"
CLOSURE="$ROUND_DIR/semantic-world-closure.json"
CLOSURE_ERR="$ROUND_DIR/semantic-world-closure.stderr"
GAP_FLOW="$ROUND_DIR/semantic-gap-flow.json"
GAP_FLOW_ERR="$ROUND_DIR/semantic-gap-flow.stderr"
NEXT_ITERATION="$ROUND_DIR/world-research-iteration.json"
ROUND_ERR="$ROUND_DIR/world-research-round.stderr"
WORLD="$OUT_DIR/sensiblaw-gwb-candidate-world-model-source-role-attached.json"
[[ -s "$WORLD" ]] || WORLD="$OUT_DIR/sensiblaw-gwb-candidate-world-model.json"

mkdir -p "$ROUND_DIR"
[[ -s "$INPUT_ITERATION" ]] || { echo "ERROR: missing iteration $INPUT_ITERATION" >&2; exit 1; }
[[ -s "$BASE_GRAPH" ]] || { echo "ERROR: missing graph $BASE_GRAPH" >&2; exit 1; }
[[ -s "$WORLD" ]] || { echo "ERROR: missing CandidateWorldModel" >&2; exit 1; }

PREVIOUS_CLOSURE="$(python3 - "$INPUT_ITERATION" <<'PY'
import json, sys
m=json.load(open(sys.argv[1], encoding='utf-8'))
print(str(m.get('semantic_closure_reference','')))
PY
)"
[[ -s "$PREVIOUS_CLOSURE" ]] || { echo "ERROR: previous semantic closure unavailable: $PREVIOUS_CLOSURE" >&2; exit 1; }

python3 "$HERE/slr_world_research_budget.py" self-check 2> "$ROUND_DIR/budget-self-check.stderr"
plan_args=(
  plan
  --iteration "$INPUT_ITERATION"
  --output "$PLAN"
  --seeds "$SEEDS"
  --history-output "$HISTORY_NEXT"
  --iteration-index "$ITERATION_INDEX"
  --max-new-qids "$MAX_NEW_QIDS"
  --max-missing-surfaces "$MAX_MISSING_SURFACES"
)
[[ -s "$HISTORY" ]] && plan_args+=(--history "$HISTORY")
python3 "$HERE/slr_world_research_budget.py" "${plan_args[@]}" 2> "$PLAN_ERR"

grep -q 'frontier_rank_is_truth_rank=false' "$PLAN_ERR" || { cat "$PLAN_ERR" >&2; exit 1; }
grep -q 'pareto_dimensions_scalarized=false' "$PLAN_ERR" || { cat "$PLAN_ERR" >&2; exit 1; }
grep -q 'budget_exhaustion_is_consumer_closure=false' "$PLAN_ERR" || { cat "$PLAN_ERR" >&2; exit 1; }

SEED_COUNT="$(grep -cve '^$' "$SEEDS" || true)"
if [[ "$SEED_COUNT" -gt 0 ]]; then
  python3 "$HERE/slr_wikimedia_world_follow.py" \
    --world-model "$WORLD" \
    --seeds "$SEEDS" \
    --output-model "$DELTA_WORLD" \
    --output-graph "$DELTA_GRAPH" \
    --cache-dir "$OUT_DIR/wikimedia-http-cache" \
    --max-depth "$MAX_DEPTH" \
    --max-seed-search-results 1 \
    --max-item-properties "${SLR_WORLD_MAX_ITEM_PROPERTIES:-80}" \
    --max-wikipedia-links "${SLR_WORLD_MAX_WIKIPEDIA_LINKS:-30}" \
    --max-retries "${WIKIMEDIA_MAX_RETRIES:-5}" \
    --backoff-base "${WIKIMEDIA_BACKOFF_BASE:-2}" \
    --max-backoff "${WIKIMEDIA_MAX_BACKOFF:-60}" \
    --min-request-interval "${WIKIMEDIA_MIN_REQUEST_INTERVAL:-0.35}" \
    2> "$FOLLOW_ERR"
  python3 "$HERE/slr_world_research_budget.py" merge \
    --base-graph "$BASE_GRAPH" \
    --delta-graph "$DELTA_GRAPH" \
    --output "$MERGED_GRAPH" \
    2> "$MERGE_ERR"
else
  cp "$BASE_GRAPH" "$MERGED_GRAPH"
  : > "$FOLLOW_ERR"
  printf 'SLR_WORLD_RESEARCH_GRAPH_MERGE_SKIPPED reason=no-selected-related-qids candidate_only=true semantic_promotion=false\n' > "$MERGE_ERR"
fi

# Recompute closure from the merged graph without the original four-QID
# multilingual limiter so newly followed QIDs can become roots in this round.
python3 "$HERE/slr_semantic_world_closure.py" \
  --graph "$MERGED_GRAPH" \
  --cache-dir "$OUT_DIR/semantic-world-http-cache" \
  --output "$CLOSURE" \
  --languages "$LANGUAGES" \
  --max-links "${SLR_WORLD_MAX_SURFACE_LINKS:-60}" \
  --retries "${MULTILINGUAL_MAX_RETRIES:-5}" \
  2> "$CLOSURE_ERR"

grep -q 'target_surface_asserted=false' "$CLOSURE_ERR" || { cat "$CLOSURE_ERR" >&2; exit 1; }
grep -q 'pareto_dimensions_scalarized=false' "$CLOSURE_ERR" || { cat "$CLOSURE_ERR" >&2; exit 1; }
grep -q 'semantic_promotion=false' "$CLOSURE_ERR" || { cat "$CLOSURE_ERR" >&2; exit 1; }

python3 "$HERE/slr_world_research_gap_flow.py" --self-check 2> "$ROUND_DIR/semantic-gap-flow-self-check.stderr"
python3 "$HERE/slr_world_research_gap_flow.py" \
  --previous "$PREVIOUS_CLOSURE" \
  --current "$CLOSURE" \
  --plan "$PLAN" \
  --output "$GAP_FLOW" \
  2> "$GAP_FLOW_ERR"

grep -q 'net_gap_growth_implies_no_contraction=false' "$GAP_FLOW_ERR" || { cat "$GAP_FLOW_ERR" >&2; exit 1; }
grep -q 'semantic_promotion=false' "$GAP_FLOW_ERR" || { cat "$GAP_FLOW_ERR" >&2; exit 1; }

python3 - "$INPUT_ITERATION" "$PLAN" "$BASE_GRAPH" "$MERGED_GRAPH" "$CLOSURE" "$GAP_FLOW" "$NEXT_ITERATION" "$ITERATION_INDEX" 2> "$ROUND_ERR" <<'PY'
import json, sys
from pathlib import Path
previous = json.load(open(sys.argv[1], encoding='utf-8'))
plan = json.load(open(sys.argv[2], encoding='utf-8'))
base_graph = json.load(open(sys.argv[3], encoding='utf-8'))
merged_graph = json.load(open(sys.argv[4], encoding='utf-8'))
closure = json.load(open(sys.argv[5], encoding='utf-8'))
flow = json.load(open(sys.argv[6], encoding='utf-8'))
out = Path(sys.argv[7]); idx = int(sys.argv[8])
prev_summary = previous.get('summary') or {}
summary = closure.get('summary') or {}
atoms_added = int(summary.get('canonical_atoms', 0)) - int(prev_summary.get('canonical_atoms', 0))
qids_added = int((merged_graph.get('summary') or {}).get('qid_node_count', 0)) - int((base_graph.get('summary') or {}).get('qid_node_count', 0))
selected_actions = int((plan.get('summary') or {}).get('selected_missing_surfaces', 0)) + int((plan.get('summary') or {}).get('selected_related_qids', 0))
if selected_actions == 0:
    round_stop = plan.get('stop_reason', 'no-actionable-frontier')
elif atoms_added <= 0 and qids_added <= 0:
    round_stop = 'no-world-growth'
else:
    round_stop = 'continue-with-budget-if-available'
payload = {
    'schema': 'slr-world-research-iteration-v1',
    'iteration_index': idx,
    'previous_iteration_reference': str(Path(sys.argv[1])),
    'budget_plan_reference': str(Path(sys.argv[2])),
    'world_graph_reference': str(Path(sys.argv[4])),
    'semantic_closure_reference': str(Path(sys.argv[5])),
    'semantic_gap_flow_reference': str(Path(sys.argv[6])),
    'tranches': previous.get('tranches') or [],
    'summary': {
        'tranches': int(prev_summary.get('tranches', 0)),
        'world_ready_tranches': int(prev_summary.get('world_ready_tranches', 0)),
        'retained_source_ready_tranches': int(prev_summary.get('retained_source_ready_tranches', 0)),
        'source_unpaid_tranches': int(prev_summary.get('source_unpaid_tranches', 0)),
        'canonical_atoms': int(summary.get('canonical_atoms', 0)),
        'observed_surfaces': int(summary.get('observed_surfaces', 0)),
        'simplewiki_surfaces': int(summary.get('simplewiki_surfaces', 0)),
        'semantic_gap_atoms': int(summary.get('semantic_gap_atoms', 0)),
        'propagated_views': int(summary.get('propagated_views', 0)),
        'acquisition_obligations': int(summary.get('acquisition_obligations', 0)),
        'atoms_added_this_round': atoms_added,
        'qid_nodes_added_this_round': qids_added,
        'selected_actions_this_round': selected_actions,
        'prior_gap_atoms': int(flow.get('prior_gap_atoms', 0)),
        'contracted_gap_atoms': int(flow.get('contracted_gap_atoms', 0)),
        'persisting_gap_atoms': int(flow.get('persisting_gap_atoms', 0)),
        'new_gap_atoms': int(flow.get('new_gap_atoms', 0)),
        'net_gap_delta': int(flow.get('net_gap_delta', 0)),
        'prior_obligations': int(flow.get('prior_obligations', 0)),
        'retired_obligations': int(flow.get('retired_obligations', 0)),
        'persisting_obligations': int(flow.get('persisting_obligations', 0)),
        'new_obligations': int(flow.get('new_obligations', 0)),
    },
    'atoms_added_per_selected_qid': flow.get('atoms_added_per_selected_qid') or {},
    'next_acquisition_obligations': closure.get('acquisition_obligations') or [],
    'round_stop_reason': round_stop,
    'pareto_dimensions_scalarized': False,
    'net_gap_growth_implies_no_contraction': False,
    'consumer_closure_paid': False,
    'budget_exhaustion_is_consumer_closure': False,
    'frontier_rank_is_truth_rank': False,
    'propagated_evidence_rewrites_source': False,
    'source_unpaid_tranche_contributes_atoms': False,
    'candidate_only': True,
    'semantic_promotion': False,
}
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n', encoding='utf-8')
s = payload['summary']
print(
    'SLR_WORLD_RESEARCH_BUDGETED_ROUND_RECEIPT '
    f"schema=slr-world-research-iteration-v1 iteration={idx} selected_actions={selected_actions} "
    f"qid_nodes_added={qids_added} atoms_added={atoms_added} canonical_atoms={s['canonical_atoms']} "
    f"prior_gap_atoms={s['prior_gap_atoms']} contracted_gap_atoms={s['contracted_gap_atoms']} "
    f"persisting_gap_atoms={s['persisting_gap_atoms']} new_gap_atoms={s['new_gap_atoms']} net_gap_delta={s['net_gap_delta']} "
    f"prior_obligations={s['prior_obligations']} retired_obligations={s['retired_obligations']} "
    f"persisting_obligations={s['persisting_obligations']} new_obligations={s['new_obligations']} "
    f"semantic_gap_atoms={s['semantic_gap_atoms']} obligations={s['acquisition_obligations']} "
    f"round_stop_reason={round_stop} pareto_dimensions_scalarized=false net_gap_growth_implies_no_contraction=false "
    'consumer_closure_paid=false budget_exhaustion_is_consumer_closure=false frontier_rank_is_truth_rank=false '
    'candidate_only=true semantic_promotion=false',
    file=sys.stderr,
)
PY

cp "$HISTORY_NEXT" "$HISTORY"
cat "$PLAN_ERR"
[[ -s "$FOLLOW_ERR" ]] && cat "$FOLLOW_ERR"
cat "$MERGE_ERR"
cat "$CLOSURE_ERR"
cat "$GAP_FLOW_ERR"
cat "$ROUND_ERR"
printf 'round_dir=%s\nnext_iteration=%s\nmerged_graph=%s\nsemantic_gap_flow=%s\nmissing_surface_history=%s\n' \
  "$ROUND_DIR" "$NEXT_ITERATION" "$MERGED_GRAPH" "$GAP_FLOW" "$HISTORY"
