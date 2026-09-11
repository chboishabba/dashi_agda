#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
OUT_DIR="${2:-$HANDOFF_ROOT/gwb-world}"
LANGUAGES="${3:-en,es,fr,de,simple}"
TRANCHE_LEDGER="${4:-$REPO_ROOT/fixtures/slr/slr-world-research-tranches-v1.jsonl}"

TRANCHE_OUT="$OUT_DIR/slr-world-research-tranche-join.json"
TRANCHE_ERR="$OUT_DIR/slr-world-research-tranche-join.stderr"
CLOSURE_OUT="$OUT_DIR/gwb-semantic-world-closure.json"
CLOSURE_ERR="$OUT_DIR/gwb-semantic-world-closure.stderr"
ITERATION_OUT="$OUT_DIR/slr-world-research-iteration.json"
ITERATION_ERR="$OUT_DIR/slr-world-research-iteration.stderr"

mkdir -p "$OUT_DIR"
python3 "$HERE/slr_world_research_tranche_join.py" --self-check 2> "$OUT_DIR/slr-world-research-tranche-join-self-check.stderr"
python3 "$HERE/slr_world_research_tranche_join.py" \
  --ledger "$TRANCHE_LEDGER" \
  --output "$TRANCHE_OUT" \
  2> "$TRANCHE_ERR"

grep -q 'source_unpaid_contributes_atoms=false' "$TRANCHE_ERR" || {
  echo 'ERROR: tranche readiness allowed unpaid semantic atoms' >&2
  cat "$TRANCHE_ERR" >&2
  exit 1
}

bash "$HERE/run_semantic_world_closure.sh" "$OUT_DIR" "$LANGUAGES" >/dev/null

python3 - "$TRANCHE_OUT" "$CLOSURE_OUT" "$ITERATION_OUT" 2> "$ITERATION_ERR" <<'PY'
import json, sys
from pathlib import Path
tranches = json.load(open(sys.argv[1], encoding='utf-8'))
closure = json.load(open(sys.argv[2], encoding='utf-8'))
out = Path(sys.argv[3])
assert tranches['schema'] == 'slr-world-research-tranche-join-v1'
assert closure['schema'] == 'slr-semantic-world-closure-v1'
assert tranches['source_unpaid_contributes_semantic_atoms'] is False
assert closure['propagation_rewrites_target_surface'] is False
assert closure['candidate_only'] is True and closure['semantic_promotion'] is False
payload = {
    'schema': 'slr-world-research-iteration-v1',
    'tranche_join_schema': tranches['schema'],
    'semantic_closure_schema': closure['schema'],
    'tranches': tranches['tranches'],
    'semantic_closure_reference': str(Path(sys.argv[2])),
    'summary': {
        'tranches': tranches['summary']['tranches'],
        'world_ready_tranches': tranches['summary']['world_ready'],
        'retained_source_ready_tranches': tranches['summary']['retained_source_ready'],
        'source_unpaid_tranches': tranches['summary']['source_unpaid'],
        'canonical_atoms': closure['summary']['canonical_atoms'],
        'observed_surfaces': closure['summary']['observed_surfaces'],
        'simplewiki_surfaces': closure['summary']['simplewiki_surfaces'],
        'semantic_gap_atoms': closure['summary']['semantic_gap_atoms'],
        'propagated_views': closure['summary']['propagated_views'],
        'acquisition_obligations': closure['summary']['acquisition_obligations'],
    },
    'next_acquisition_obligations': closure['acquisition_obligations'],
    'propagated_evidence_rewrites_source': False,
    'source_unpaid_tranche_contributes_atoms': False,
    'candidate_only': True,
    'semantic_promotion': False,
}
out.write_text(json.dumps(payload, indent=2, sort_keys=True) + '\n', encoding='utf-8')
s = payload['summary']
print(
    'SLR_WORLD_RESEARCH_ITERATION_RECEIPT '
    f"schema=slr-world-research-iteration-v1 tranches={s['tranches']} "
    f"world_ready={s['world_ready_tranches']} retained_source_ready={s['retained_source_ready_tranches']} "
    f"source_unpaid={s['source_unpaid_tranches']} canonical_atoms={s['canonical_atoms']} "
    f"observed_surfaces={s['observed_surfaces']} simplewiki_surfaces={s['simplewiki_surfaces']} "
    f"semantic_gap_atoms={s['semantic_gap_atoms']} propagated_views={s['propagated_views']} "
    f"acquisition_obligations={s['acquisition_obligations']} propagated_rewrites_source=false "
    'source_unpaid_contributes_atoms=false candidate_only=true semantic_promotion=false',
    file=sys.stderr,
)
PY

cat "$TRANCHE_ERR"
cat "$CLOSURE_ERR"
cat "$ITERATION_ERR"
printf 'tranche_join=%s\nsemantic_closure=%s\nworld_research_iteration=%s\n' \
  "$TRANCHE_OUT" "$CLOSURE_OUT" "$ITERATION_OUT"
