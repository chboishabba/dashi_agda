#!/usr/bin/env bash
# Local authoritative smoke for the *economic observation* world and empirical
# scenario candidate; not the Lean/JMD proof-world builder or an Agda kernel run.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

python3 -m unittest discover -s tests \
  -p 'test_cybersyn_economic_world_and_scenarios.py' -v

fixture_root="${1:-}"
if [[ -z "$fixture_root" ]]; then
  fixture_root="$(mktemp -d)"
  trap 'rm -rf "$fixture_root"' EXIT
fi
mkdir -p "$fixture_root"
python3 scripts/generate_cybersyn_synthetic_fixture.py --out "$fixture_root"
python3 scripts/cybersyn_economic_observation_world.py \
  "$fixture_root/world.jsonl" \
  "$fixture_root/world-manifest.json" \
  --database "$fixture_root/economic-world.sqlite3" \
  > "$fixture_root/observation-world-receipt.json"
python3 scripts/cybersyn_world_scenario_handoff.py \
  --database "$fixture_root/economic-world.sqlite3" \
  --world-manifest "$fixture_root/world-manifest.json" \
  --world-snapshot "$fixture_root/world.jsonl" \
  --scenario-data "$fixture_root/scenario.csv" \
  --scenario-manifest "$fixture_root/scenario-manifest.json" \
  --cutoff 2026-02-17T00:00:00Z \
  > "$fixture_root/scenario-handoff-receipt.json"

python3 - "$fixture_root/scenario-handoff-receipt.json" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["matched_events"] == 64
assert r["validation"]["training_n"] == 47
assert r["validation"]["holdout_n"] == 17
for k in ("world_admitted","kernel_proof_certified","empirically_admitted"):
    assert r[k] is False
print("Economic source-world and scenario candidate smoke PASS; all proof/empirical promotions remain FALSE")
PY
echo "Local fixture and receipts: $fixture_root"
