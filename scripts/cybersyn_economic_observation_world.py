#!/usr/bin/env python3
"""Cybersyn time-indexed economic observation world (not Lean proof world).

The immutable event source is a pinned JSONL snapshot with an SHA-256 manifest.
This is an economic-observation world-builder, not the JMD authoritative Lean
builder or a certification of source claims. No admission level is inferred.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sqlite3

HEX64 = re.compile(r"[0-9a-f]{64}\Z")
SOURCE_LAYERS = {"primary", "secondary", "community", "synthetic"}
REQUIRED = ("region", "time", "event_id", "source_id", "source_layer",
            "source_locator", "attribution_owner", "observation",
            "claim_boundary", "authority_status")
AUTHORITY = {"unresolved", "candidate", "mandate-verified"}


class WorldAdmissionError(ValueError):
    pass


def canonical(row: dict) -> bytes:
    return json.dumps(row, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False, allow_nan=False).encode("utf-8")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def timestamp(text: str) -> datetime:
    if not isinstance(text, str):
        raise WorldAdmissionError("invalid UTC timestamp")
    try:
        parsed = datetime.fromisoformat(text.replace("Z", "+00:00"))
    except ValueError as exc:
        raise WorldAdmissionError("invalid ISO timestamp") from exc
    if parsed.tzinfo is None or parsed.utcoffset() != timezone.utc.utcoffset(None):
        raise WorldAdmissionError("timestamp must be explicitly UTC")
    return parsed


def check_manifest(manifest: dict, raw: bytes) -> None:
    if (not isinstance(manifest, dict) or
            manifest.get("schema") != "dashi-cybersyn-observation-snapshot-v1"):
        raise WorldAdmissionError("unsupported manifest")
    if not isinstance(manifest.get("sha256"), str) or not HEX64.fullmatch(manifest["sha256"]):
        raise WorldAdmissionError("invalid snapshot hash")
    if sha(raw) != manifest["sha256"]:
        raise WorldAdmissionError("snapshot bytes changed")
    for key in ("dataset_id", "version", "source_locator",
                "licence", "attribution_owner", "collection_method"):
        if not isinstance(manifest.get(key), str) or not manifest[key].strip():
            raise WorldAdmissionError("missing provenance field: " + key)
    if manifest.get("empirically_admitted") is not False:
        raise WorldAdmissionError("snapshot cannot self-certify empirical admission")


def read_snapshot(manifest: dict, raw: bytes) -> list[dict]:
    check_manifest(manifest, raw)
    rows = []
    origins = set()
    for line in raw.splitlines():
        if not line or len(line) > 2_000_000:
            raise WorldAdmissionError("blank or oversized record")
        try:
            row = json.loads(line)
        except (ValueError, UnicodeError) as exc:
            raise WorldAdmissionError("invalid JSONL observation") from exc
        if not isinstance(row, dict) or any(not isinstance(row.get(k), str)
                                           or not row[k].strip() for k in REQUIRED):
            raise WorldAdmissionError("missing typed observation fields")
        timestamp(row["time"])
        if row["source_layer"] not in SOURCE_LAYERS or row["authority_status"] not in AUTHORITY:
            raise WorldAdmissionError("unrecognised evidence or authority status")
        if row.get("empirically_admitted") is not False:
            raise WorldAdmissionError("observation self-promotion rejected")
        origin = (row["region"], row["time"], row["event_id"], row["source_id"])
        if origin in origins:
            raise WorldAdmissionError("duplicated origin within snapshot")
        origins.add(origin)
        if not isinstance(row["observation"], str):
            raise WorldAdmissionError("invalid observation")
        rows.append(row)
    if not rows:
        raise WorldAdmissionError("empty event snapshot")
    return rows


def initialise(connection: sqlite3.Connection) -> None:
    connection.execute("""CREATE TABLE IF NOT EXISTS economic_world_source (
        dataset_id TEXT NOT NULL, version TEXT NOT NULL,
        sha256 TEXT NOT NULL, manifest TEXT NOT NULL,
        PRIMARY KEY(dataset_id, version))""")
    connection.execute("""CREATE TABLE IF NOT EXISTS economic_world_event (
        dataset_id TEXT NOT NULL, version TEXT NOT NULL,
        region TEXT NOT NULL, time TEXT NOT NULL,
        event_id TEXT NOT NULL, source_id TEXT NOT NULL,
        payload_sha256 TEXT NOT NULL, payload TEXT NOT NULL,
        PRIMARY KEY(dataset_id,version,region,time,event_id,source_id),
        FOREIGN KEY(dataset_id,version) REFERENCES economic_world_source(dataset_id,version))""")


def ingest(database: Path, manifest: dict, raw: bytes) -> dict:
    rows = read_snapshot(manifest, raw)
    database.parent.mkdir(parents=True, exist_ok=True)
    con = sqlite3.connect(database)
    try:
        con.execute("PRAGMA foreign_keys=ON")
        initialise(con)
        with con:
            key = (manifest["dataset_id"], manifest["version"])
            original = con.execute(
                "SELECT sha256,manifest FROM economic_world_source "
                "WHERE dataset_id=? AND version=?", key).fetchone()
            encoded = canonical(manifest).decode()
            if original is not None and original != (sha(raw), encoded):
                raise WorldAdmissionError("conflicting pinned version")
            con.execute("INSERT OR IGNORE INTO economic_world_source VALUES (?,?,?,?)",
                        (*key, sha(raw), encoded))
            for row in rows:
                identity = (*key, row["region"], row["time"], row["event_id"], row["source_id"])
                payload = canonical(row).decode()
                prior = con.execute(
                    "SELECT payload_sha256,payload FROM economic_world_event "
                    "WHERE dataset_id=? AND version=? AND region=? AND time=? "
                    "AND event_id=? AND source_id=?", identity).fetchone()
                if prior is not None and prior != (sha(payload.encode()), payload):
                    raise WorldAdmissionError("conflicting immutable event occurrence")
                con.execute("INSERT OR IGNORE INTO economic_world_event VALUES (?,?,?,?,?,?,?,?)",
                            (*identity, sha(payload.encode()), payload))
        return {"schema": "dashi-cybersyn-economic-world-receipt-v1",
                "dataset_id": key[0], "version": key[1],
                "snapshot_sha256": sha(raw), "events": len(rows),
                "status": "source-verified-economic-observation-world",
                "world_admitted": False, "kernel_proof_certified": False,
                "empirically_admitted": False}
    finally:
        con.close()


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("snapshot", type=Path)
    p.add_argument("manifest", type=Path)
    p.add_argument("--database", required=True, type=Path)
    a = p.parse_args()
    result = ingest(a.database, json.loads(a.manifest.read_text()),
                    a.snapshot.read_bytes())
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
