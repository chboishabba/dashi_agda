#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
OUT_DIR="${2:-$HANDOFF_ROOT/gwb-world}"
ITERATION_INDEX="${3:-3}"
INPUT_ITERATION="${4:-$OUT_DIR/world-research-rounds/round-$((ITERATION_INDEX-1))/world-research-iteration.json}"
BASE_GRAPH="${5:-$OUT_DIR/world-research-rounds/round-$((ITERATION_INDEX-1))/merged-wikimedia-world-graph.json}"
LANGUAGES="${6:-en,es,fr,de,simple}"
ARTICLE_PNF_LANGUAGES="${SLR_WORLD_ARTICLE_PNF_LANGUAGES:-en}"
MAX_TARGETS="${SLR_WORLD_MAX_TYPED_ROUTE_TARGETS:-4}"
MAX_MISSING="${SLR_WORLD_MAX_MISSING_SURFACES_PER_ITERATION:-4}"
ENV_FILE="${SLR_WORLD_ENV_FILE:-.env}"
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
ARTICLE_PNF="$ROUND_DIR/wikipedia-article-pnf-world-producer.json"
ARTICLE_PNF_ERR="$ROUND_DIR/wikipedia-article-pnf-world-producer.stderr"
ARTICLE_WELDED_CLOSURE="$ROUND_DIR/semantic-world-closure-with-article-pnf.json"
ARTICLE_WELD_ERR="$ROUND_DIR/article-pnf-semantic-weld.stderr"
ARTICLE_GAP_FLOW="$ROUND_DIR/semantic-gap-flow-with-article-pnf.json"
ARTICLE_GAP_FLOW_ERR="$ROUND_DIR/semantic-gap-flow-with-article-pnf.stderr"
PG_RECEIPT="$ROUND_DIR/postgres-world-persistence-receipt.json"
PG_ERR="$ROUND_DIR/postgres-world-persistence.stderr"

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

# The bounded round consumes the graph sidecar, not its copied CandidateWorldModel.
# Route the legacy output-model write to /dev/null so a large redundant JSON
# snapshot cannot fail the round before article -> spaCy -> PNF executes.
rm -f "$ROUND_DIR/wikimedia-delta-world.json"
ln -s /dev/null "$ROUND_DIR/wikimedia-delta-world.json"

SLR_WORLD_MAX_NEW_QIDS_PER_ITERATION="$SELECTED_TARGETS" \
SLR_WORLD_MAX_MISSING_SURFACES_PER_ITERATION="$MAX_MISSING" \
SLR_WORLD_FOLLOW_MAX_DEPTH=0 \
bash "$HERE/run_world_research_budgeted_round.sh" \
  "$HANDOFF_ROOT" "$OUT_DIR" "$ITERATION_INDEX" "$SYNTHETIC_ITERATION" "$BASE_GRAPH" "$LANGUAGES"

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

# Strong semantic producer: read the selected Wikipedia article revisions, run a
# trained spaCy dependency parser, project sentence-level candidate PNF, and
# weld those candidates into the same candidate semantic closure.
python3 "$HERE/slr_wikipedia_article_pnf_world_producer.py" --self-check 2> "$ROUND_DIR/wikipedia-article-pnf-self-check.stderr"
python3 "$HERE/slr_wikipedia_article_pnf_world_producer.py" \
  --route-plan "$ROUTE_PLAN" \
  --output "$ARTICLE_PNF" \
  --cache-dir "$OUT_DIR/article-pnf-http-cache" \
  --languages "$ARTICLE_PNF_LANGUAGES" \
  --retries "${WIKIMEDIA_MAX_RETRIES:-5}" \
  2> "$ARTICLE_PNF_ERR"

grep -q 'spacy_dependency_surface_explicit=true' "$ARTICLE_PNF_ERR" || { cat "$ARTICLE_PNF_ERR" >&2; exit 1; }
grep -q 'pnf_candidate_surface_explicit=true' "$ARTICLE_PNF_ERR" || { cat "$ARTICLE_PNF_ERR" >&2; exit 1; }
grep -q 'parser_output_creates_ontology_truth=false' "$ARTICLE_PNF_ERR" || { cat "$ARTICLE_PNF_ERR" >&2; exit 1; }

python3 "$HERE/slr_article_pnf_semantic_weld.py" --self-check 2> "$ROUND_DIR/article-pnf-semantic-weld-self-check.stderr"
python3 "$HERE/slr_article_pnf_semantic_weld.py" \
  --closure "$ROUND_DIR/semantic-world-closure.json" \
  --article-pnf "$ARTICLE_PNF" \
  --output "$ARTICLE_WELDED_CLOSURE" \
  2> "$ARTICLE_WELD_ERR"

grep -q 'article_pnf_creates_claim_truth=false' "$ARTICLE_WELD_ERR" || { cat "$ARTICLE_WELD_ERR" >&2; exit 1; }
grep -q 'cross_language_propagation_rewrites_source=false' "$ARTICLE_WELD_ERR" || { cat "$ARTICLE_WELD_ERR" >&2; exit 1; }

python3 "$HERE/slr_world_research_gap_flow.py" \
  --previous "$PREVIOUS_CLOSURE" \
  --current "$ARTICLE_WELDED_CLOSURE" \
  --plan "$ROUND_DIR/budget-plan.json" \
  --output "$ARTICLE_GAP_FLOW" \
  2> "$ARTICLE_GAP_FLOW_ERR"

python3 - "$ROUND_DIR/world-research-iteration.json" "$ARTICLE_WELDED_CLOSURE" "$ARTICLE_GAP_FLOW" <<'PY'
import json, sys
from pathlib import Path
iteration_path=Path(sys.argv[1])
closure_path=Path(sys.argv[2])
flow_path=Path(sys.argv[3])
it=json.loads(iteration_path.read_text(encoding='utf-8'))
cl=json.loads(closure_path.read_text(encoding='utf-8'))
flow=json.loads(flow_path.read_text(encoding='utf-8'))
s=cl.get('summary') or {}
it['semantic_closure_reference']=str(closure_path)
it['semantic_gap_flow_reference']=str(flow_path)
it['article_pnf_world_producer_reference']=str(iteration_path.parent / 'wikipedia-article-pnf-world-producer.json')
it['article_pnf_world_welded']=True
it['spacy_dependency_surface_explicit']=True
it['pnf_candidate_surface_explicit']=True
it['parser_output_creates_ontology_truth']=False
it['article_pnf_creates_claim_truth']=False
it['candidate_only']=True
it['semantic_promotion']=False
summary=it.setdefault('summary', {})
for key in ('canonical_atoms','surface_closure_atoms','semantic_gap_atoms','propagated_views','acquisition_obligations','article_pnf_atoms_added'):
    if key in s:
        summary[key]=int(s.get(key,0))
for key in ('prior_gap_atoms','contracted_gap_atoms','persisting_gap_atoms','new_gap_atoms','net_gap_delta','prior_obligations','retired_obligations','persisting_obligations','new_obligations'):
    if key in flow:
        summary[key]=int(flow.get(key,0))
it['next_acquisition_obligations']=cl.get('acquisition_obligations') or []
iteration_path.write_text(json.dumps(it, indent=2, sort_keys=True)+'\n', encoding='utf-8')
PY

# Canonical durable state: append/idempotently persist the source manifestations,
# PNF candidates, world atoms, route actions and iteration receipt into the
# existing DATABASE_URL Postgres substrate.  Credentials never enter receipts.
python3 "$HERE/slr_world_pg_store.py" persist-round \
  --article-pnf "$ARTICLE_PNF" \
  --closure "$ARTICLE_WELDED_CLOSURE" \
  --route-plan "$ROUTE_PLAN" \
  --iteration "$ROUND_DIR/world-research-iteration.json" \
  --env-file "$ENV_FILE" \
  --receipt "$PG_RECEIPT" \
  2> "$PG_ERR"

grep -q 'database_url_emitted=false' "$PG_ERR" || { cat "$PG_ERR" >&2; exit 1; }
grep -q 'postgres_persistence_is_semantic_authority=false' "$PG_ERR" || { cat "$PG_ERR" >&2; exit 1; }

GAP_FLOW="$ARTICLE_GAP_FLOW"
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
cat "$ARTICLE_PNF_ERR"
cat "$ARTICLE_WELD_ERR"
cat "$ARTICLE_GAP_FLOW_ERR"
cat "$PG_ERR"
[[ -s "$ROUND_DIR/typed-route-yield-history.stderr" ]] && cat "$ROUND_DIR/typed-route-yield-history.stderr"
printf 'typed_route_plan=%s\ntyped_route_history=%s\narticle_pnf=%s\narticle_pnf_closure=%s\narticle_pnf_gap_flow=%s\npostgres_receipt=%s\nround_dir=%s\n' \
  "$ROUTE_PLAN" "$ROUTE_HISTORY" "$ARTICLE_PNF" "$ARTICLE_WELDED_CLOSURE" "$ARTICLE_GAP_FLOW" "$PG_RECEIPT" "$ROUND_DIR"
