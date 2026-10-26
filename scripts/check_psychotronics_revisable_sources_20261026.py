#!/usr/bin/env python3
"""Case-specific, fail-closed source-withdrawal tests; NOT a weather proof."""
from __future__ import annotations
import argparse
import csv
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORLD = ROOT / "docs/receipts/PsychotronicsEllsworthRevisableSourceWorld20261026.json"
SOURCES = ROOT / "docs/research/psychotronics-phase1-literature-landscape-20261025.csv"


def assess(world, withdrawn=()):
    roots = world["source_roots"]
    by_root = {sid: name for name, root in roots.items() for sid in root["members"]}
    if len(by_root) != sum(len(root["members"]) for root in roots.values()):
        raise ValueError("ambiguous source ownership")
    unknown = set(withdrawn) - set(by_root)
    if unknown:
        raise ValueError(f"unrecognized source withdrawals: {sorted(unknown)}")
    claims = world["claims"]
    if len({c["id"] for c in claims}) != len(claims):
        raise ValueError("claim identifier collision")
    for claim in claims:
        if set(claim["requires"]) - set(by_root):
            raise ValueError(f"unresolved dependency for {claim['id']}")
        if claim["status"] == "unpaid" and claim["requires"]:
            raise ValueError(f"unpaid source claim falsely attached to document {claim['id']}")
    result = {}
    for claim in claims:
        if claim["status"] == "unpaid":
            state = "unpaid"
        elif any(x in withdrawn for x in claim["requires"]):
            state = "reopen"
        else:
            state = claim["status"]
        result[claim["id"]] = state
    return result


def check_ledger(world, source_path):
    with source_path.open(encoding="utf-8", newline="") as file:
        rows = list(csv.DictReader(file))
    ids = [r["id"] for r in rows]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate source IDs in corpus")
    members = {sid for root in world["source_roots"].values() for sid in root["members"]}
    if not members <= set(ids):
        raise ValueError(f"source IDs absent from original ledger: {sorted(members - set(ids))}")
    return {"source_entries": len(rows), "referenced_sources_found": len(members)}


def self_test(world):
    baseline = assess(world)
    cases = {
        "P1-63": ("bangor_daily_rain_6to8", "reich_1953_reported_operation"),
        "P1-48": ("reich_1953_reported_operation", "bangor_daily_rain_6to8"),
        "P1-52": ("reddit_visualisation_claims", "bangor_daily_rain_6to8"),
        "P1-37": ("rodin_two_papers_same_printed_numbers", "bangor_daily_rain_6to8"),
        "P1-66": ("wrong_ellsworth_kansas", "reich_1953_reported_operation"),
        "P1-70": ("rvml_gentry_reich_device_claim", "bangor_daily_rain_6to8"),
    }
    for withdrawn, (reopen, preserve) in cases.items():
        newer = assess(world, {withdrawn})
        assert newer[reopen] == "reopen", (withdrawn, reopen)
        assert newer[preserve] == baseline[preserve], (withdrawn, preserve)
        assert newer["reich_device_caused_rain"] == "unpaid"
        assert newer["1953_ellsworth_hourly_gauge"] == "unpaid"
    assert assess(world, {"P1-63", "P1-67"})["bangor_daily_rain_6to8"] == "reopen"
    assert baseline["bangor_daily_rain_6to8"] == "observed_at_regional_station"
    try:
        assess(world, {"P1-99999"})
    except ValueError:
        pass
    else:
        raise AssertionError("unknown source was silently accepted")
    return {"cases": len(cases) + 2, "passed": True,
            "does_not_turn_unpaid_into_false": True,
            "does_not_erase_independent_claims": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--world", type=Path, default=WORLD)
    parser.add_argument("--sources", type=Path, default=SOURCES)
    parser.add_argument("--withdraw", action="append", default=[])
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    world = json.loads(args.world.read_text(encoding="utf-8"))
    report = {"case": world["title"], "documentary_only": True,
              "ledger": check_ledger(world, args.sources),
              "claims": assess(world, set(args.withdraw))}
    if args.self_test:
        report["self_test"] = self_test(world)
    print(json.dumps(report, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
