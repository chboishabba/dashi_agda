#!/usr/bin/env python3
"""Join a provenance-checked economic event world to a scenario holdout.

The source world is the local economic observation store, NOT the Lean/JMD
proof world. Every scenario row must match exactly one immutable event and
the event's JSON observation. World admission and empirical causal validity
remain separate external obligations.
"""
from __future__ import annotations

import argparse
import csv
from datetime import datetime
from hashlib import sha256
import io
import json
from pathlib import Path
import sqlite3

import cybersyn_empirical_scenario_validation as validation
import cybersyn_economic_observation_world as economic


class CrossWorldError(ValueError):
    pass


def normalize_date(value: str) -> str:
    return validation.parse_time(value).isoformat()


def verify_cross_world(db: Path, world_manifest: dict,
                       scenario_manifest: dict, scenario_raw: bytes,
                       cutoff: str, *, world_snapshot_raw: bytes) -> dict:
    original_world_rows = economic.read_snapshot(world_manifest, world_snapshot_raw)
    expected_world = {
        (row["region"], row["time"], row["event_id"], row["source_id"]):
        economic.canonical(row).decode()
        for row in original_world_rows
    }
    # Validate dataset integrity, all physical and financial identities,
    # and strict chronological holdout BEFORE matching the world.
    report = validation.validate(scenario_raw, scenario_manifest, cutoff)
    rows = list(csv.DictReader(io.StringIO(scenario_raw.decode("utf-8"))))
    expected = {}
    for row in rows:
        key = (row["region"], normalize_date(row["time"]), row["event_id"])
        if key in expected:
            raise CrossWorldError("duplicate scenario key")
        expected[key] = row

    if world_manifest.get("empirically_admitted") is not False:
        raise CrossWorldError("world manifest self-promotion")
    with sqlite3.connect(db) as con:
        con.row_factory = sqlite3.Row
        result = con.execute(
            "SELECT sha256,manifest FROM economic_world_source "
            "WHERE dataset_id=? AND version=?",
            (world_manifest["dataset_id"], world_manifest["version"])).fetchone()
        if result is None or result["manifest"] != economic.canonical(world_manifest).decode():
            raise CrossWorldError("unrecognized immutable source manifest")
        if result["sha256"] != world_manifest["sha256"]:
            raise CrossWorldError("world snapshot digest mismatch")
        events = list(con.execute(
            "SELECT * FROM economic_world_event WHERE dataset_id=? AND version=?",
            (world_manifest["dataset_id"], world_manifest["version"])))
    matched = set()
    for record in events:
        payload = record["payload"]
        if sha256(payload.encode()).hexdigest() != record["payload_sha256"]:
            raise CrossWorldError("world event payload changed")
        event = json.loads(payload)
        original_key = (event["region"], event["time"], event["event_id"],
                        event["source_id"])
        if expected_world.get(original_key) != payload:
            raise CrossWorldError("database event differs from pinned source bytes")
        if event.get("empirically_admitted") is not False:
            raise CrossWorldError("event self-promotion")
        if event["source_id"] != scenario_manifest["dataset_id"]:
            raise CrossWorldError("source identity mismatch")
        if event["source_layer"] != scenario_manifest["source_layer"]:
            raise CrossWorldError("source layer mismatch")
        key = (event["region"], normalize_date(event["time"]), event["event_id"])
        if key in matched or key not in expected:
            raise CrossWorldError("extra or duplicate world event")
        try:
            observation = json.loads(event["observation"])
        except (ValueError, TypeError) as exc:
            raise CrossWorldError("world observation is not a typed JSON measurement") from exc
        required = (*validation.BASE, "outcome", *validation.AMOUNTS)
        if not isinstance(observation, dict):
            raise CrossWorldError("invalid typed world observation")
        if {k: str(observation.get(k)) for k in required} != {
                k: expected[key][k] for k in required}:
            raise CrossWorldError("scenario/model measurement changed across world join")
        matched.add(key)
    if matched != set(expected) or len(matched) != len(expected_world):
        raise CrossWorldError("world missing scenario observations")
    return {
        "schema": "dashi-cybersyn-world-scenario-handoff-v1",
        "world_snapshot_sha256": world_manifest["sha256"],
        "scenario_snapshot_sha256": scenario_manifest["sha256"],
        "matched_events": len(matched),
        "status": "exact-source-world-scenario-observation-match",
        "world_admitted": False, "kernel_proof_certified": False,
        "empirically_admitted": False,
        "validation": report,
        "unpaid_gates": ["authoritative JMD proof world builder",
                         "original Agda kernel check",
                         "independent empirical source verification",
                         "causal and policy counterfactual identification"]
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--database", type=Path, required=True)
    p.add_argument("--world-manifest", type=Path, required=True)
    p.add_argument("--scenario-manifest", type=Path, required=True)
    p.add_argument("--scenario-data", type=Path, required=True)
    p.add_argument("--world-snapshot", type=Path, required=True)
    p.add_argument("--cutoff", required=True)
    args = p.parse_args()
    print(json.dumps(verify_cross_world(
        args.database,
        json.loads(args.world_manifest.read_text()),
        json.loads(args.scenario_manifest.read_text()),
        args.scenario_data.read_bytes(), args.cutoff,
        world_snapshot_raw=args.world_snapshot.read_bytes()),
        indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
