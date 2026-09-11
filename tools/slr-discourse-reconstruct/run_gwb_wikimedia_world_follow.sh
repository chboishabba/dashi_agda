#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
SENSIBLAW_ROOT="${2:-/home/c/Documents/code/SensibLaw}"
OUT_DIR="${3:-$HANDOFF_ROOT/gwb-world}"
REVIEWED_OVERLAY="${4:-$HERE/../../fixtures/slr/gwb-reviewed-wikimedia-identities-v1.jsonl}"
ARCHIVE="${5:-$HANDOFF_ROOT/gwb-world-handoff.tar.xz}"
PROJECTION="$HANDOFF_ROOT/gwb-projection/source_projection.json"
WORLD="$OUT_DIR/sensiblaw-gwb-candidate-world-model.json"
SEEDS="$OUT_DIR/gwb-wikimedia-seeds.jsonl"
SEED_ERR="$OUT_DIR/gwb-wikimedia-seeds.stderr"
FOLLOWED="$OUT_DIR/sensiblaw-gwb-candidate-world-model-wikimedia-followed.json"
GRAPH="$OUT_DIR/gwb-wikimedia-world-graph.json"
FOLLOW_ERR="$OUT_DIR/gwb-wikimedia-world-follow.stderr"
NORMALIZED="$OUT_DIR/sensiblaw-gwb-candidate-world-model-wikimedia-followed-normalized.json"
PARITY_ERR="$OUT_DIR/gwb-wikimedia-world-parity.stderr"
CACHE_DIR="$OUT_DIR/wikimedia-http-cache"
CONTRACTED="$OUT_DIR/sensiblaw-gwb-candidate-world-model-wikimedia-identity-contracted.json"
CONTRACTION_SIDECAR="$OUT_DIR/gwb-wikimedia-identity-contractions.json"
CONTRACTION_ERR="$OUT_DIR/gwb-wikimedia-identity-contraction.stderr"
CONTRACTED_NORMALIZED="$OUT_DIR/sensiblaw-gwb-candidate-world-model-wikimedia-identity-contracted-normalized.json"
CONTRACTION_PARITY_ERR="$OUT_DIR/gwb-wikimedia-identity-contraction-parity.stderr"
SOURCE_ROLE_WORLD="$OUT_DIR/sensiblaw-gwb-candidate-world-model-source-role-attached.json"
SOURCE_ROLE_SIDECAR="$OUT_DIR/gwb-source-role-attachment.json"
SOURCE_ROLE_ERR="$OUT_DIR/gwb-source-role-attachment.stderr"
SOURCE_ROLE_NORMALIZED="$OUT_DIR/sensiblaw-gwb-candidate-world-model-source-role-attached-normalized.json"
SOURCE_ROLE_PARITY_ERR="$OUT_DIR/gwb-source-role-attachment-parity.stderr"

mkdir -p "$OUT_DIR" "$CACHE_DIR"

package_on_exit() {
  status=$?
  trap - EXIT
  set +e
  bash "$HERE/package_gwb_world_handoff.sh" "$HANDOFF_ROOT" "$OUT_DIR" "$ARCHIVE"
  package_status=$?
  set -e
  if [[ "$status" -eq 0 && "$package_status" -ne 0 ]]; then
    status="$package_status"
  fi
  exit "$status"
}
trap package_on_exit EXIT

# This also pays the base GWB SensibLaw normalization parity first.
bash "$HERE/run_gwb_candidate_world.sh" "$HANDOFF_ROOT" "$SENSIBLAW_ROOT" "$OUT_DIR" >/dev/null

seed_args=(
  --projection-manifest "$PROJECTION"
  --output "$SEEDS"
)
if [[ -s "$REVIEWED_OVERLAY" ]]; then
  seed_args+=(--reviewed-overlay "$REVIEWED_OVERLAY")
fi
python3 "$HERE/slr_gwb_wikimedia_seed_candidates.py" "${seed_args[@]}" 2> "$SEED_ERR"

grep -q 'schema=slr-gwb-wikimedia-seed-candidates-v2' "$SEED_ERR" || {
  echo 'ERROR: GWB Wikimedia seed receipt missing/stale' >&2
  cat "$SEED_ERR" >&2
  exit 1
}
grep -q 'topic_anchor_is_source_object_identity=false' "$SEED_ERR" || {
  echo 'ERROR: topical identity overlay collapsed into source-object identity' >&2
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
  printf 'SLR_GWB_WIKIMEDIA_WORLD_FOLLOW_SKIPPED reason=no-explicit-or-reviewed-seeds broad_snowball_not_started=true semantic_promotion=false\n' >&2
  exit 0
fi

python3 "$HERE/slr_wikimedia_world_follow.py" \
  --world-model "$WORLD" \
  --seeds "$SEEDS" \
  --output-model "$FOLLOWED" \
  --output-graph "$GRAPH" \
  --cache-dir "$CACHE_DIR" \
  --max-depth 2 \
  --max-seed-search-results 3 \
  --max-item-properties 80 \
  --max-wikipedia-links 30 \
  --max-retries "${WIKIMEDIA_MAX_RETRIES:-5}" \
  --backoff-base "${WIKIMEDIA_BACKOFF_BASE:-2}" \
  --max-backoff "${WIKIMEDIA_MAX_BACKOFF:-60}" \
  --min-request-interval "${WIKIMEDIA_MIN_REQUEST_INTERVAL:-0.35}" \
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

# Contract only the identity dimension that the reviewed/live Wikimedia graph pays.
bash "$HERE/run_gwb_identity_residual_contraction.sh" "$HANDOFF_ROOT" "$OUT_DIR" >/dev/null

CONTRACTION_PARITY_STATUS="not-run"
if [[ -d "$SENSIBLAW_ROOT/src" ]]; then
  PYTHONPATH="$SENSIBLAW_ROOT${PYTHONPATH:+:$PYTHONPATH}" \
  python3 - "$CONTRACTED" "$CONTRACTED_NORMALIZED" 2> "$CONTRACTION_PARITY_ERR" <<'PY'
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
    'SLR_GWB_WIKIMEDIA_IDENTITY_CONTRACTION_SENSIBLAW_PARITY_RECEIPT '
    f"target={normalized['schema_version']} provenance={len(normalized['provenance_graph'])} "
    'normalization_drift=false candidate_only=true semantic_promotion=false',
    file=sys.stderr,
)
PY
  grep -q 'normalization_drift=false' "$CONTRACTION_PARITY_ERR" || {
    echo 'ERROR: GWB identity-contracted model normalization parity failed' >&2
    cat "$CONTRACTION_PARITY_ERR" >&2
    exit 1
  }
  CONTRACTION_PARITY_STATUS="passed"
fi

# Attach claim-relative source roles only to provenance/document records.
bash "$HERE/run_gwb_source_role_attachment.sh" "$HANDOFF_ROOT" "$OUT_DIR" >/dev/null

SOURCE_ROLE_PARITY_STATUS="not-run"
if [[ -d "$SENSIBLAW_ROOT/src" ]]; then
  PYTHONPATH="$SENSIBLAW_ROOT${PYTHONPATH:+:$PYTHONPATH}" \
  python3 - "$SOURCE_ROLE_WORLD" "$SOURCE_ROLE_NORMALIZED" 2> "$SOURCE_ROLE_PARITY_ERR" <<'PY'
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
    'SLR_GWB_SOURCE_ROLE_SENSIBLAW_PARITY_RECEIPT '
    f"target={normalized['schema_version']} provenance={len(normalized['provenance_graph'])} "
    'normalization_drift=false primaryness_is_claim_relative=true '
    'candidate_only=true semantic_promotion=false',
    file=sys.stderr,
)
PY
  grep -q 'normalization_drift=false' "$SOURCE_ROLE_PARITY_ERR" || {
    echo 'ERROR: GWB source-role-attached model normalization parity failed' >&2
    cat "$SOURCE_ROLE_PARITY_ERR" >&2
    exit 1
  }
  SOURCE_ROLE_PARITY_STATUS="passed"
fi

# Multilingual compatibility is diagnostic/opt-in because installed language
# models and network surfaces vary by environment. Any generated artifacts are
# still captured by the automatic handoff archive.
MULTILINGUAL_STATUS="not-run"
if [[ "${SLR_RUN_MULTILINGUAL_COMPAT:-0}" == "1" ]]; then
  bash "$HERE/run_multilingual_wikimedia_parser_compat.sh" \
    "$HANDOFF_ROOT" "$OUT_DIR" "${SLR_MULTILINGUAL_LANGUAGES:-en,es,fr,de}" >/dev/null
  MULTILINGUAL_STATUS="passed"
fi

cat "$SEED_ERR"
cat "$FOLLOW_ERR"
[[ -s "$PARITY_ERR" ]] && cat "$PARITY_ERR"
cat "$CONTRACTION_ERR"
[[ -s "$CONTRACTION_PARITY_ERR" ]] && cat "$CONTRACTION_PARITY_ERR"
cat "$SOURCE_ROLE_ERR"
[[ -s "$SOURCE_ROLE_PARITY_ERR" ]] && cat "$SOURCE_ROLE_PARITY_ERR"
printf 'gwb_world=%s\nreviewed_overlay=%s\nseeds=%s\nworld_graph=%s\nfollowed_world=%s\nidentity_contracted_world=%s\nidentity_sidecar=%s\nsource_role_world=%s\nsource_role_sidecar=%s\nhttp_cache=%s\nnormalization_parity=%s\nidentity_contraction_parity=%s\nsource_role_parity=%s\nmultilingual_compat=%s\narchive=%s\n' \
  "$WORLD" "$REVIEWED_OVERLAY" "$SEEDS" "$GRAPH" "$FOLLOWED" "$CONTRACTED" "$CONTRACTION_SIDECAR" "$SOURCE_ROLE_WORLD" "$SOURCE_ROLE_SIDECAR" "$CACHE_DIR" "$PARITY_STATUS" "$CONTRACTION_PARITY_STATUS" "$SOURCE_ROLE_PARITY_STATUS" "$MULTILINGUAL_STATUS" "$ARCHIVE"
