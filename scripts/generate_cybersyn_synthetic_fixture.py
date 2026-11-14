#!/usr/bin/env python3
"""Generate clearly synthetic Cybersyn world/scenario fixtures for offline smoke.

Never tag these generated records as real observations or as empirically
admitted. They exercise the actual economic source-store, cross-world exact
join and out-of-sample model-validation APIs.
"""
from __future__ import annotations

import argparse
import csv
from datetime import datetime, timedelta, timezone
from hashlib import sha256
import io
import json
from pathlib import Path

from cybersyn_empirical_scenario_validation import BASE, AMOUNTS
from cybersyn_economic_observation_world import canonical


def generate(folder: Path, count: int = 64) -> dict:
    if count < 32:
        raise ValueError("need >=32 synthetic events for chronological holdout")
    folder.mkdir(parents=True, exist_ok=True)
    scenario_rows, world_rows = [], []
    for i in range(count):
        event = {
            "region": "AU-QLD" if i % 2 else "AU-VIC",
            "time": (datetime(2026, 1, 1, tzinfo=timezone.utc) +
                     timedelta(days=i)).isoformat(),
            "event_id": f"synthetic-{i:05d}"
        }
        for j, name in enumerate(BASE):
            event[name] = int((i // (j + 2) + i * (j + 3)) % 5 < 2)
        event["outcome"] = int(
            event["energy"] * event["food"] or
            event["fx_funding"] * event["ai_credit"] or
            i % 11 == 0)
        event.update({
            "equity_loss": 2, "lender_loss": 3, "public_loss": i % 3,
            "total_loss": 5 + i % 3,
            "grid_ai": 5, "grid_households": 4, "grid_other": 3,
            "grid_unused": 2, "grid_total": 14,
            "labour_housing": 5, "labour_datacentre": 3,
            "labour_other": 4, "labour_total": 12
        })
        scenario_rows.append(event)
        world_rows.append({
            "region": event["region"], "time": event["time"],
            "event_id": event["event_id"], "source_id": "synthetic-scenarios",
            "source_layer": "synthetic", "source_locator": "DASHI fixture generator",
            "attribution_owner": "DASHI original synthetic fixture",
            "observation": json.dumps(
                {k: event[k] for k in (*BASE, "outcome", *AMOUNTS)},
                sort_keys=True),
            "claim_boundary": "synthetic demonstration only; no observations asserted",
            "authority_status": "unresolved", "empirically_admitted": False
        })

    buf = io.StringIO()
    writer = csv.DictWriter(buf, fieldnames=("region", "time", "event_id",
                           *BASE, "outcome", *AMOUNTS))
    writer.writeheader()
    writer.writerows(scenario_rows)
    scenario_raw = buf.getvalue().encode()
    world_raw = b"".join(canonical(row) + b"\n" for row in world_rows)
    scenario_manifest = {
        "schema": "dashi-cybersyn-empirical-scenario-v1",
        "dataset_id": "synthetic-scenarios", "version": "1",
        "sha256": sha256(scenario_raw).hexdigest(),
        "source_locator": "DASHI synthetic fixture generator",
        "licence": "DASHI repository fixture", "attribution_owner": "DASHI",
        "collection_method": "deterministic code-generated",
        "source_layer": "synthetic", "empirically_admitted": False
    }
    world_manifest = {
        "schema": "dashi-cybersyn-observation-snapshot-v1",
        "dataset_id": "synthetic-economic-world", "version": "1",
        "sha256": sha256(world_raw).hexdigest(),
        "source_locator": "DASHI synthetic fixture generator",
        "licence": "DASHI repository fixture", "attribution_owner": "DASHI",
        "collection_method": "deterministic code-generated",
        "empirically_admitted": False
    }
    for name, data in (
        ("scenario.csv", scenario_raw),
        ("world.jsonl", world_raw),
        ("scenario-manifest.json", canonical(scenario_manifest) + b"\n"),
        ("world-manifest.json", canonical(world_manifest) + b"\n"),
    ):
        (folder / name).write_bytes(data)
    return {"fixture": str(folder), "events": count, "empirically_admitted": False,
            "world_sha256": world_manifest["sha256"],
            "scenario_sha256": scenario_manifest["sha256"]}


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--count", type=int, default=64)
    args = p.parse_args()
    print(json.dumps(generate(args.out, args.count), sort_keys=True))


if __name__ == "__main__":
    main()
