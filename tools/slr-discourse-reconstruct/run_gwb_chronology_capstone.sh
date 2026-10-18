#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"

HANDOFF_ROOT="\${1:-/tmp/slr-validation-20260911}"
SLR_ROOT="\${2:-/home/c/Documents/code/slr}"
DIOXUS_ROOT="\${3:-/home/c/Documents/code/itir-dioxus}"
REVIEWED_MANIFEST="\${4:-}"

PROJECTION="$HANDOFF_ROOT/gwb-projection/source_projection.json"
ROLES="$REPO_ROOT/fixtures/slr/gwb-claim-relative-source-roles-v1.jsonl"
PACKET="$HANDOFF_ROOT/gwb-chronology-capstone-review-packet.json"

[[ -s "$PROJECTION" ]] || {
  echo "ERROR: missing GWB projection manifest: $PROJECTION" >&2
  exit 1
}
[[ -s "$ROLES" ]] || {
  echo "ERROR: missing GWB source-role atlas: $ROLES" >&2
  exit 1
}

python3 "$HERE/prepare_gwb_chronology_capstone_review_packet.py" \
  --projection-manifest "$PROJECTION" \
  --source-roles "$ROLES" \
  --output "$PACKET"

printf 'review_packet=%s\n' "$PACKET"

if [[ -z "$REVIEWED_MANIFEST" ]]; then
  cat >&2 <<EOF
GWB chronology inventory prepared.

To materialize the empirical capstone, create an explicitly reviewed manifest
with schema:

  sensiblaw.gwb-heterogeneous-chronology-capstone.v0_1

using exact local retained source spans, then rerun:

  $0 "$HANDOFF_ROOT" "$SLR_ROOT" "$DIOXUS_ROOT" <reviewed-manifest.json>

No event, claim, date, or source-truth promotion has been performed.
EOF
  exit 0
fi

[[ -s "$REVIEWED_MANIFEST" ]] || {
  echo "ERROR: missing reviewed manifest: $REVIEWED_MANIFEST" >&2
  exit 1
}
[[ -d "$SLR_ROOT/crates/sl-pg-source-store" ]] || {
  echo "ERROR: SLR root does not contain sl-pg-source-store: $SLR_ROOT" >&2
  exit 1
}
[[ -f "$DIOXUS_ROOT/Cargo.toml" ]] || {
  echo "ERROR: Dioxus root missing Cargo.toml: $DIOXUS_ROOT" >&2
  exit 1
}
[[ -n "\${DATABASE_URL:-}" ]] || {
  echo "ERROR: DATABASE_URL is required for the live capstone" >&2
  exit 1
}

readarray -t EVENT_REFS < <(
  python3 - "$REVIEWED_MANIFEST" <<'PY'
import json, sys
m = json.load(open(sys.argv[1], encoding="utf-8"))
assert m["schema"] == "sensiblaw.gwb-heterogeneous-chronology-capstone.v0_1"
assert m["candidate_only"] is True
assert m["semantic_promotion"] is False
for row in m.get("event_joins", []):
    assert row["reviewed"] is True
    assert row["automatic_join"] is False
    print(row["event_ref"])
PY
)

if [[ "\${#EVENT_REFS[@]}" -eq 0 ]]; then
  echo "ERROR: reviewed manifest contains no event joins" >&2
  exit 1
fi

echo "== materialize reviewed GWB chronology capstone =="
cargo run \
  --manifest-path "$SLR_ROOT/Cargo.toml" \
  -p sensiblaw-pg-source-store \
  --example gwb_chronology_capstone \
  -- "$REVIEWED_MANIFEST"

echo "== M12 live semantic trace receipt =="
cargo run \
  --manifest-path "$DIOXUS_ROOT/Cargo.toml" \
  --no-default-features \
  --features production-data \
  --example m12_semantic_trace_receipt \
  -- "\${EVENT_REFS[0]}"

echo "== S28 timeline receipt =="
cargo run \
  --manifest-path "$DIOXUS_ROOT/Cargo.toml" \
  --no-default-features \
  --features production-data \
  --example s28_timeline_receipt \
  -- "\${EVENT_REFS[@]}"

echo "== S29 review queue receipt =="
cargo run \
  --manifest-path "$DIOXUS_ROOT/Cargo.toml" \
  --no-default-features \
  --features production-data \
  --example s29_review_queue_receipt

printf 'GWB_HETEROGENEOUS_CHRONOLOGY_CAPSTONE_RECEIPT events=%s m12=executed s28=executed s29=executed candidate_only=true semantic_promotion=false\n' \
  "\${#EVENT_REFS[@]}"
