#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
SENSIBLAW_ROOT="${2:-/home/c/Documents/code/SensibLaw}"
OUT_DIR="${3:-$HANDOFF_ROOT/gwb-world}"
PROJECTION="$HANDOFF_ROOT/gwb-projection/source_projection.json"
WORLD="$OUT_DIR/sensiblaw-gwb-candidate-world-model.json"
SEEDS="$OUT_DIR/gwb-wikimedia-seeds.jsonl"
SEED_ERR="$OUT_DIR/gwb-wikimedia-seeds.stderr"
FOLLOWED="$OUT_DIR/sensiblaw-gwb-candidate-world-model-wikimedia-followed.json"
GRAPH="$OUT_DIR/gwb-wikimedia-world-graph.json"
FOLLOW_ERR="$OUT_DIR/gwb-wikimedia-world-follow.stderr"
NORMALIZED="$OUT_DIR/sensiblaw-gwb-candidate-world-model-wikimedia-followed-normalized.json"
PARITY_ERR="$OUT_DIR/gwb-wikimedia-world-parity.stderr"

mkdir -p "$OUT_DIR"

# This also pays the base GWB SensibLaw normalization parity first.
bash "$HERE/run_gwb_candidate_world.sh" "$HANDOFF_ROOT" "$SENSIBLAW_ROOT" "$OUT_DIR" >/dev/null

python3 "$HERE/slr_gwb_wikimedia_seed_candidates.py" \
  --projection-manifest "$PROJECTION" \
  --output "$SEEDS" \
  2> "$SEED_ERR"

grep -q 'schema=slr-gwb-wikimedia-seed-candidates-v1' "$SEED_ERR" || {
  echo 'ERROR: GWB Wikimedia seed receipt missing/stale' >&2
  cat "$SEED_ERR" >&2
  exit 1
}

SEED_COUNT="$(python3 - "$SEEDS" <<'PY'
import sys
from pathlib import Path
p = Path(sys.argv[1])
print(sum(1 for line in p.read_text(encoding='utf-8').splitlines() if line.strip()))
PY
)"

if [[ "$SEED_COUNT" -eq 0 ]]; then
  cat "$SEED_ERR"
  printf 'SLR_GWB_WIKIMEDIA_WORLD_FOLLOW_SKIPPED reason=no-explicit-or-metadata-seeds broad_snowball_not_started=true semantic_promotion=false\n' >&2
  exit 0
fi

python3 "$HERE/slr_wikimedia_world_follow.py" \
  --world-model "$WORLD" \
  --seeds "$SEEDS" \
  --output-model "$FOLLOWED" \
  --output-graph "$GRAPH" \
  --max-depth 2 \
  --max-seed-search-results 3 \
  --max-item-properties 80 \
  --max-wikipedia-links 30 \
  2> "$FOLLOW_ERR"

grep -q 'schema=slr-wikimedia-world-follow-v1' "$FOLLOW_ERR" || {
  echo 'ERROR: Wikimedia world-follow receipt missing/stale' >&2
  cat "$FOLLOW_ERR" >&2
  exit 1
}
grep -q 'wikimedia_before_broad_snowball=true' "$FOLLOW_ERR" || {
  echo 'ERROR: Wikimedia-first acquisition order missing' >&2
  exit 1
}
grep -q 'ibrahim_exact=false' "$FOLLOW_ERR" || {
  echo 'ERROR: current first-link candidate was promoted to exact Ibrahim reproduction' >&2
  exit 1
}
grep -q 'semantic_promotion=false' "$FOLLOW_ERR" || {
  echo 'ERROR: Wikimedia follow attempted semantic promotion' >&2
  exit 1
}

PARITY_STATUS="not-run"
if [[ -d "$SENSIBLAW_ROOT/src" ]]; then
  PYTHONPATH="$SENSIBLAW_ROOT${PYTHONPATH:+:$PYTHONPATH}" \
  python3 - "$FOLLOWED" "$NORMALIZED" 2> "$PARITY_ERR" <<'PY'
import json, sys
from pathlib import Path
from src.policy.world_model import normalize_world_model

src = Path(sys.argv[1])
out = Path(sys.argv[2])
source = json.loads(src.read_text(encoding='utf-8'))
normalized = normalize_world_model(source)
out.write_text(json.dumps(normalized, indent=2, sort_keys=True) + '\n', encoding='utf-8')
for key in (
    'schema_version','model_id','lane_family','model_status','source_mode',
    'entities','claims','relations','events','timelines','authority_surfaces',
    'provenance_graph','conflicts','residuals','update_rules','projections',
    'external_graph_views','external_bridge_candidates','external_bridge_decisions',
    'external_pressure_results','metadata','summary','status_counts',
):
    assert normalized[key] == source[key], f'normalization drift in {key}'
print(
    'SLR_GWB_WIKIMEDIA_SENSIBLAW_PARITY_RECEIPT '
    f"target={normalized['schema_version']} external_graph_views={len(normalized['external_graph_views'])} "
    'normalization_drift=false candidate_only=true semantic_promotion=false',
    file=sys.stderr,
)
PY
  grep -q 'normalization_drift=false' "$PARITY_ERR" || {
    echo 'ERROR: GWB Wikimedia-followed model normalization parity failed' >&2
    cat "$PARITY_ERR" >&2
    exit 1
  }
  PARITY_STATUS="passed"
fi

cat "$SEED_ERR"
cat "$FOLLOW_ERR"
[[ -s "$PARITY_ERR" ]] && cat "$PARITY_ERR"
printf 'gwb_world=%s\nseeds=%s\nworld_graph=%s\nfollowed_world=%s\nnormalization_parity=%s\n' \
  "$WORLD" "$SEEDS" "$GRAPH" "$FOLLOWED" "$PARITY_STATUS"
