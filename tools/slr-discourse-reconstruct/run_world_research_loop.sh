#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
OUT_DIR="${2:-$HANDOFF_ROOT/gwb-world}"
LANGUAGES="${3:-en,es,fr,de,simple}"
MAX_ITERATIONS="${SLR_WORLD_MAX_ITERATIONS:-3}"
MAX_TOTAL_NEW_ATOMS="${SLR_WORLD_MAX_TOTAL_NEW_ATOMS:-5000}"
CURRENT_ITERATION="$OUT_DIR/slr-world-research-iteration.json"
CURRENT_GRAPH="$OUT_DIR/gwb-wikimedia-world-graph.json"
LOOP_DIR="$OUT_DIR/world-research-rounds"
LOOP_RECEIPT="$LOOP_DIR/world-research-loop.json"
LOOP_ERR="$LOOP_DIR/world-research-loop.stderr"
ARCHIVE="${SLR_WORLD_HANDOFF_ARCHIVE:-$HANDOFF_ROOT/gwb-world-handoff.tar.xz}"

mkdir -p "$LOOP_DIR"
[[ -s "$CURRENT_ITERATION" ]] || { echo "ERROR: missing initial iteration $CURRENT_ITERATION" >&2; exit 1; }
[[ -s "$CURRENT_GRAPH" ]] || { echo "ERROR: missing initial graph $CURRENT_GRAPH" >&2; exit 1; }

initial_atoms="$(python3 - "$CURRENT_ITERATION" <<'PY'
import json, sys
m=json.load(open(sys.argv[1], encoding='utf-8'))
print(int((m.get('summary') or {}).get('canonical_atoms', 0)))
PY
)"
rounds_run=0
stop_reason="max-iterations"

for ((i=1; i<=MAX_ITERATIONS; i++)); do
  mkdir -p "$LOOP_DIR/round-$i"
  bash "$HERE/run_world_research_budgeted_round.sh" \
    "$HANDOFF_ROOT" "$OUT_DIR" "$i" "$CURRENT_ITERATION" "$CURRENT_GRAPH" "$LANGUAGES" \
    > "$LOOP_DIR/round-$i/runner.stdout" 2> "$LOOP_DIR/round-$i/runner.stderr"
  CURRENT_ITERATION="$LOOP_DIR/round-$i/world-research-iteration.json"
  CURRENT_GRAPH="$LOOP_DIR/round-$i/merged-wikimedia-world-graph.json"
  rounds_run="$i"

  read -r round_stop current_atoms selected_actions <<<"$(python3 - "$CURRENT_ITERATION" <<'PY'
import json, sys
m=json.load(open(sys.argv[1], encoding='utf-8'))
s=m.get('summary') or {}
print(str(m.get('round_stop_reason','')), int(s.get('canonical_atoms',0)), int(s.get('selected_actions_this_round',0)))
PY
)"
  total_added="$((current_atoms - initial_atoms))"

  if [[ "$selected_actions" -eq 0 ]]; then
    stop_reason="frontier-exhausted-or-no-actionable-obligations"
    break
  fi
  if [[ "$round_stop" == "no-world-growth" ]]; then
    stop_reason="no-world-growth"
    break
  fi
  if [[ "$total_added" -ge "$MAX_TOTAL_NEW_ATOMS" ]]; then
    stop_reason="total-new-atom-budget-exhausted"
    break
  fi
done

python3 - "$LOOP_RECEIPT" "$CURRENT_ITERATION" "$CURRENT_GRAPH" "$rounds_run" "$MAX_ITERATIONS" "$MAX_TOTAL_NEW_ATOMS" "$initial_atoms" "$stop_reason" 2> "$LOOP_ERR" <<'PY'
import json, sys
from pathlib import Path
out=Path(sys.argv[1])
iteration=json.load(open(sys.argv[2], encoding='utf-8'))
graph=json.load(open(sys.argv[3], encoding='utf-8'))
rounds=int(sys.argv[4]); max_iterations=int(sys.argv[5]); max_atoms=int(sys.argv[6]); initial_atoms=int(sys.argv[7]); stop=sys.argv[8]
summary=iteration.get('summary') or {}
current_atoms=int(summary.get('canonical_atoms',0))
payload={
  'schema':'slr-world-research-loop-v1',
  'rounds_run':rounds,
  'max_iterations':max_iterations,
  'max_total_new_atoms':max_atoms,
  'initial_canonical_atoms':initial_atoms,
  'final_canonical_atoms':current_atoms,
  'total_new_atoms':current_atoms-initial_atoms,
  'final_semantic_gap_atoms':int(summary.get('semantic_gap_atoms',0)),
  'final_acquisition_obligations':int(summary.get('acquisition_obligations',0)),
  'final_qid_nodes':int((graph.get('summary') or {}).get('qid_node_count',0)),
  'stop_reason':stop,
  'consumer_closure_paid':False,
  'budget_exhaustion_is_consumer_closure':False,
  'frontier_rank_is_truth_rank':False,
  'candidate_only':True,
  'semantic_promotion':False,
}
out.write_text(json.dumps(payload, indent=2, sort_keys=True)+'\n', encoding='utf-8')
print(
  'SLR_WORLD_RESEARCH_LOOP_RECEIPT '
  f"schema=slr-world-research-loop-v1 rounds_run={rounds} total_new_atoms={payload['total_new_atoms']} "
  f"final_canonical_atoms={current_atoms} final_semantic_gap_atoms={payload['final_semantic_gap_atoms']} "
  f"final_obligations={payload['final_acquisition_obligations']} final_qid_nodes={payload['final_qid_nodes']} "
  f"stop_reason={stop} consumer_closure_paid=false budget_exhaustion_is_consumer_closure=false "
  'frontier_rank_is_truth_rank=false candidate_only=true semantic_promotion=false',
  file=sys.stderr,
)
PY

package_status="not-run"
if [[ "${SLR_WORLD_PACKAGE_HANDOFF:-1}" == "1" ]]; then
  bash "$HERE/package_gwb_world_handoff.sh" "$HANDOFF_ROOT" "$OUT_DIR" "$ARCHIVE" \
    > "$LOOP_DIR/handoff-package.stdout" 2> "$LOOP_DIR/handoff-package.stderr"
  package_status="passed"
fi

cat "$LOOP_ERR"
[[ -s "$LOOP_DIR/handoff-package.stderr" ]] && cat "$LOOP_DIR/handoff-package.stderr"
printf 'world_research_loop=%s\nfinal_iteration=%s\nfinal_graph=%s\npackage_status=%s\narchive=%s\n' \
  "$LOOP_RECEIPT" "$CURRENT_ITERATION" "$CURRENT_GRAPH" "$package_status" "$ARCHIVE"
