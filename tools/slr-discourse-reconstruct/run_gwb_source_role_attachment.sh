#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
HANDOFF_ROOT="${1:-/tmp/slr-validation-20260911}"
OUT_DIR="${2:-$HANDOFF_ROOT/gwb-world}"
ROLES="${3:-$HERE/../../fixtures/slr/gwb-claim-relative-source-roles-v1.jsonl}"
WORLD="$OUT_DIR/sensiblaw-gwb-candidate-world-model-wikimedia-identity-contracted.json"
OUTPUT="$OUT_DIR/sensiblaw-gwb-candidate-world-model-source-role-attached.json"
SIDECAR="$OUT_DIR/gwb-source-role-attachment.json"
ERR="$OUT_DIR/gwb-source-role-attachment.stderr"

for required in "$WORLD" "$ROLES"; do
  [[ -s "$required" ]] || { echo "ERROR: missing required input $required" >&2; exit 1; }
done

python3 "$HERE/slr_gwb_source_role_attachment.py" \
  --world-model "$WORLD" \
  --roles "$ROLES" \
  --output-model "$OUTPUT" \
  --output-sidecar "$SIDECAR" \
  2> "$ERR"

grep -q 'schema=slr-gwb-source-role-attachment-v1' "$ERR" || {
  echo 'ERROR: GWB source-role attachment receipt missing/stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'roles_attached=10' "$ERR" || { echo 'ERROR: not all ten GWB source roles attached' >&2; exit 1; }
grep -q 'primaryness_is_claim_relative=true' "$ERR" || { echo 'ERROR: source primaryness lost claim-relative boundary' >&2; exit 1; }
grep -q 'source_role_is_source_identity=false' "$ERR" || { echo 'ERROR: source role collapsed into source identity' >&2; exit 1; }
grep -q 'source_role_creates_claim_truth=false' "$ERR" || { echo 'ERROR: source role promoted claim truth' >&2; exit 1; }

python3 - "$SIDECAR" "$OUTPUT" <<'PY'
import json, sys
sidecar = json.load(open(sys.argv[1], encoding='utf-8'))
world = json.load(open(sys.argv[2], encoding='utf-8'))
assert sidecar['summary']['documents'] == 10
assert sidecar['summary']['roles_attached'] == 10
roles = {int(r['document_ordinal']): r['source_role'] for r in sidecar['roles']}
assert roles[8] == 'secondary-investigative-book'
assert roles[10] == 'first-person-presidential-memoir'
assert world['metadata']['gwb_claim_relative_source_roles']['roles_attached'] == 10
assert world['metadata']['semantic_promotion'] is False
print('SLR_GWB_SOURCE_ROLE_ATTACHMENT_VALIDATION documents=10 roles_attached=10 primaryness_is_claim_relative=true source_role_is_source_identity=false source_role_creates_claim_truth=false candidate_only=true semantic_promotion=false')
PY

cat "$ERR"
printf 'source_role_world=%s\nsource_role_sidecar=%s\n' "$OUTPUT" "$SIDECAR"
