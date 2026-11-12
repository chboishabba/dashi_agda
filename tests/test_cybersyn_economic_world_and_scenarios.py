"""Offline fail-closed regression for Cybersyn economic event and scenario runners."""
from __future__ import annotations

import csv
from datetime import datetime, timedelta, timezone
import hashlib
import io
import json
from pathlib import Path
import sqlite3
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import cybersyn_economic_observation_world as world
import cybersyn_empirical_scenario_validation as scenarios


def event_fixture():
    records = []
    for i in range(2):
        records.append({
            "region": "AU-QLD", "time": f"2026-01-0{i+1}T00:00:00Z",
            "event_id": f"demo-{i}", "source_id": "toy-data",
            "source_layer": "synthetic", "source_locator": "test fixture",
            "attribution_owner": "DASHI synthetic tests",
            "observation": "Illustrative, not a verified historical event",
            "claim_boundary": "No empirical promotion", "authority_status": "unresolved",
            "empirically_admitted": False
        })
    raw = b"".join(world.canonical(row) + b"\n" for row in records)
    manifest = {"schema": "dashi-cybersyn-observation-snapshot-v1",
                "dataset_id": "toy-01", "version": "a",
                "sha256": world.sha(raw), "source_locator": "synthetic:test",
                "licence": "test-only", "attribution_owner": "DASHI",
                "collection_method": "deterministic generator",
                "empirically_admitted": False}
    return raw, manifest


COLUMNS = ("region", "time", "event_id", *scenarios.BASE, "outcome",
           *scenarios.AMOUNTS)


def scenario_fixture():
    records = []
    for i in range(64):
        event = {
            "region": "AU-QLD" if i % 2 else "AU-VIC",
            "time": (datetime(2026, 1, 1, tzinfo=timezone.utc) +
                     timedelta(days=i)).isoformat(),
            "event_id": f"scenario-{i:03d}"
        }
        for j, name in enumerate(scenarios.BASE):
            event[name] = int((i // (j+2) + i * (j+3)) % 5 < 2)
        # Interaction contributes predictive signal without forcing a theorem
        # about empirical reality. Deterministic synthetic validation only.
        event["outcome"] = int(
            event["energy"] * event["food"] or
            event["fx_funding"] * event["ai_credit"] or
            (i % 11 == 0))
        event.update({
            "equity_loss": 2, "lender_loss": 3, "public_loss": i % 3,
            "total_loss": 5 + i % 3,
            "grid_ai": 5, "grid_households": 4, "grid_other": 3,
            "grid_unused": 2, "grid_total": 14,
            "labour_housing": 5, "labour_datacentre": 3,
            "labour_other": 4, "labour_total": 12
        })
        records.append(event)
    def encode(rows):
        buffer = io.StringIO()
        writer = csv.DictWriter(buffer, fieldnames=COLUMNS)
        writer.writeheader()
        writer.writerows(rows)
        return buffer.getvalue().encode()
    raw = encode(records)
    manifest = {
        "schema": "dashi-cybersyn-empirical-scenario-v1",
        "dataset_id": "toy-scenario-01", "version": "a",
        "sha256": hashlib.sha256(raw).hexdigest(),
        "source_locator": "synthetic:test", "licence": "test-only",
        "attribution_owner": "DASHI",
        "collection_method": "deterministic generator",
        "source_layer": "synthetic", "empirically_admitted": False
    }
    return raw, manifest, records, encode


class EconomicWorldTests(unittest.TestCase):
    def test_idempotent_and_exact_count(self):
        raw, manifest = event_fixture()
        with tempfile.TemporaryDirectory() as d:
            db = Path(d) / "world.sqlite3"
            a = world.ingest(db, manifest, raw)
            b = world.ingest(db, manifest, raw)
            self.assertEqual(a, b)
            self.assertFalse(a["world_admitted"])
            with sqlite3.connect(db) as con:
                self.assertEqual(con.execute("SELECT COUNT(*) FROM economic_world_event").fetchone()[0], 2)

    def test_rejects_changed_bytes(self):
        raw, manifest = event_fixture()
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(world.WorldAdmissionError):
                world.ingest(Path(d) / "db", manifest, raw + b"\n")

    def test_rejects_self_certification(self):
        raw, manifest = event_fixture()
        manifest["empirically_admitted"] = True
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(world.WorldAdmissionError):
                world.ingest(Path(d) / "db", manifest, raw)

    def test_no_relabelled_snapshot_version(self):
        raw, manifest = event_fixture()
        with tempfile.TemporaryDirectory() as d:
            db = Path(d) / "db"
            world.ingest(db, manifest, raw)
            altered = dict(manifest, licence="forged")
            with self.assertRaises(world.WorldAdmissionError):
                world.ingest(db, altered, raw)

    def test_same_id_two_times_not_same_origin(self):
        raw, manifest = event_fixture()
        rows = world.read_snapshot(manifest, raw)
        self.assertNotEqual((rows[0]["time"], rows[0]["event_id"]),
                            (rows[1]["time"], rows[1]["event_id"]))


class ScenarioValidationTests(unittest.TestCase):
    def test_chronological_holdout_with_no_empirical_promotion(self):
        raw, manifest, _, _ = scenario_fixture()
        result = scenarios.validate(raw, manifest, "2026-02-17T00:00:00Z")
        self.assertEqual(result["training_n"], 47)
        self.assertEqual(result["holdout_n"], 17)
        self.assertTrue(result["synthetic_data"])
        self.assertFalse(result["empirically_admitted"])
        self.assertGreater(result["additive_brier"], 0)
        self.assertEqual(result["region_count"], 2)

    def test_hash_tampering_blocked(self):
        raw, manifest, _, _ = scenario_fixture()
        with self.assertRaises(scenarios.ScenarioError):
            scenarios.validate(raw + b"\n", manifest, "2026-02-17T00:00:00Z")

    def test_invalid_loss_waterfall_rejected(self):
        _, manifest, records, encode = scenario_fixture()
        records[0]["total_loss"] = 5000
        raw = encode(records)
        manifest["sha256"] = hashlib.sha256(raw).hexdigest()
        with self.assertRaisesRegex(scenarios.ScenarioError, "loss waterfall"):
            scenarios.validate(raw, manifest, "2026-02-17T00:00:00Z")

    def test_invalid_grid_and_labour_rejected(self):
        _, manifest, records, encode = scenario_fixture()
        for field in ("grid_total", "labour_total"):
            changed = [dict(r) for r in records]
            changed[0][field] += 1
            raw = encode(changed)
            m = dict(manifest, sha256=hashlib.sha256(raw).hexdigest())
            with self.assertRaises(scenarios.ScenarioError):
                scenarios.validate(raw, m, "2026-02-17T00:00:00Z")

    def test_nonchrono_holdout_rejected(self):
        raw, manifest, _, _ = scenario_fixture()
        with self.assertRaises(scenarios.ScenarioError):
            scenarios.validate(raw, manifest, "2027-01-01T00:00:00Z")

    def test_admission_claim_rejected(self):
        raw, manifest, _, _ = scenario_fixture()
        manifest["empirically_admitted"] = True
        with self.assertRaisesRegex(scenarios.ScenarioError, "self-certified"):
            scenarios.validate(raw, manifest, "2026-02-17T00:00:00Z")


if __name__ == "__main__":
    unittest.main()
