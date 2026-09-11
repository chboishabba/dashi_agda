#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
SPECIMEN="${1:-$HERE/specimens/abc730-2026-09-09-primary}"
GATES="${2:-$SPECIMEN/c029-consumer-gates.json}"
WORLD_MODEL="$SPECIMEN/sensiblaw-candidate-world-model-constrained.json"
FIBRES="$SPECIMEN/world-constraint-fibres.json"
OUT="$SPECIMEN/review-dispositions.json"
ERR="$SPECIMEN/review-dispositions.stderr"

[[ -s "$GATES" ]] || { echo "ERROR: missing consumer gate state $GATES" >&2; exit 1; }
if [[ ! -s "$WORLD_MODEL" || ! -s "$FIBRES" ]]; then
  bash "$HERE/run_world_constraint_fibre.sh" "$SPECIMEN" >/dev/null
fi

python3 - "$GATES" <<'PY'
import json
import sys
from pathlib import Path

g = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
assert g.get("schema") == "c029-consumer-gates-v1"
assert g.get("gate_state_role") == "structural-consumer-admission-state-not-empirical-evidence"
assert g.get("candidate_only") is True
assert g.get("semantic_promotion") is False
assert g.get("truth_promoted") is False
assert g.get("evaluate_aptness_enabled") is False
PY

python3 "$HERE/slr_review_disposition.py" \
  --world-model "$WORLD_MODEL" \
  --fibres "$FIBRES" \
  --consumer-gates "$GATES" \
  --output "$OUT" \
  2> "$ERR"

grep -q 'schema=slr-review-disposition-v1' "$ERR" || {
  echo 'ERROR: review disposition receipt missing or stale' >&2
  cat "$ERR" >&2
  exit 1
}
grep -q 'promotion_performed=false' "$ERR" || { echo 'ERROR: promotion firewall missing' >&2; exit 1; }
grep -q 'semantic_promotion=false' "$ERR" || { echo 'ERROR: semantic-promotion firewall missing' >&2; exit 1; }
grep -q 'current_residual=settlementClassifierResidual' "$ERR" || {
  echo 'ERROR: C029 first residual drifted from settlementClassifierResidual' >&2
  cat "$ERR" >&2
  exit 1
}

python3 - "$OUT" <<'PY'
import json
import sys
from pathlib import Path

report = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
assert report["schema"] == "slr-review-disposition-v1"
assert report["current_residual"] == "settlementClassifierResidual"
assert report["promotion_performed"] is False
assert report["semantic_promotion"] is False
assert report["candidate_only"] is True
assert report["summary"].get("eligible-for-separate-promotion-review", 0) == 0
assert all(row["promotion_performed"] is False for row in report["dispositions"])
assert all(row["truth_promoted"] is False for row in report["dispositions"])
assert all(
    row["disposition"] in {"abstain-for-residual", "reject-by-consumer-veto"}
    for row in report["dispositions"]
)
print(
    "SLR_REVIEW_DISPOSITION_VALIDATION "
    f"candidates={len(report['dispositions'])} "
    f"reject={report['summary'].get('reject-by-consumer-veto',0)} "
    f"abstain={report['summary'].get('abstain-for-residual',0)} "
    "eligible=0 promotion_performed=false"
)
PY

cat "$ERR"
printf 'review_dispositions=%s\nstderr=%s\n' "$OUT" "$ERR"
