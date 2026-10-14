from __future__ import annotations

from collections import defaultdict
import json
from pathlib import Path
import re
import sqlite3
from typing import Optional

from . import discovery_catalog
from .discovery import classify_surface_role, make_fingerprint
from .repo_index_bridge import RepoIndexReader


_STAMP_KEY = "semantic_repo_signature_overlay_stamp"
_COUNT_KEY = "semantic_repo_signature_overlay_count"
_IDENT_RE = re.compile(r"[A-Za-z][A-Za-z0-9']*")


def _repo_stamp(reader: RepoIndexReader) -> Optional[str]:
    if reader.connection is None:
        return None
    try:
        rows = reader.connection.execute(
            "SELECT key, value FROM meta WHERE key IN ('schema_version', 'generated_at')"
        ).fetchall()
    except sqlite3.DatabaseError:
        return None
    values = {row["key"]: row["value"] for row in rows}
    schema = values.get("schema_version")
    generated = values.get("generated_at")
    if schema is None:
        return None
    return "{}:{}".format(schema, generated or "unknown")


def _overlay_count(connection: sqlite3.Connection) -> int:
    row = connection.execute(
        "SELECT count(*) FROM semantic_symbols WHERE kind = 'repo-signature'"
    ).fetchone()
    return int(row[0])


def overlay_is_fresh(reader: RepoIndexReader, connection: sqlite3.Connection) -> bool:
    stamp = _repo_stamp(reader)
    if stamp is None:
        return False
    rows = connection.execute(
        "SELECT key, value FROM meta WHERE key IN (?, ?)",
        (_STAMP_KEY, _COUNT_KEY),
    ).fetchall()
    values = {row["key"]: row["value"] for row in rows}
    try:
        expected_count = int(values.get(_COUNT_KEY, "-1"))
    except ValueError:
        expected_count = -1
    return (
        values.get(_STAMP_KEY) == stamp
        and expected_count >= 0
        and _overlay_count(connection) == expected_count
    )


def _signature_text(root: Path, item: dict) -> str:
    kind = item.get("kind")
    if kind not in {"function", "data", "record", "postulate"}:
        return ""
    path = root / item["file"]
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return ""
    start = max(0, int(item.get("line_start", 1)) - 1)
    end = max(start + 1, min(len(lines), int(item.get("line_end", start + 1))))
    block = lines[start:end]
    if not block:
        return ""
    if kind == "function":
        name = re.escape(str(item["name"]))
        collected = []
        started = False
        for line in block:
            if not started:
                match = re.match(r"^\s*{}\s*:\s*(.*)$".format(name), line)
                if match:
                    started = True
                    collected.append(match.group(1).strip())
                continue
            if line and not line[0].isspace():
                break
            collected.append(line.strip())
        return " ".join(part for part in collected if part)
    first = block[0].strip()
    # For declaration-level similarity the local declaration name is noise.
    if kind in {"data", "record"}:
        first = re.sub(
            r"^{}\s+{}\b".format(kind, re.escape(str(item["name"]))),
            kind + " _",
            first,
        )
    return first


def _refs(signature: str, own_name: str) -> list[str]:
    return sorted({token for token in _IDENT_RE.findall(signature) if token != own_name})


def sync_repo_signatures(
    root: Path,
    reader: RepoIndexReader,
    connection: sqlite3.Connection,
    *,
    force: bool = False,
) -> dict:
    """Persist shallow type signatures for repo-index symbols into preflight.

    This overlay is derived from source locations already owned by repo-index;
    it adds type-shape searchability without duplicating repo identity/status.
    """

    discovery_catalog.ensure_catalog_schema(connection)
    stamp = _repo_stamp(reader)
    if not force and stamp is not None and overlay_is_fresh(reader, connection):
        return {
            "updated": False,
            "symbols_with_signatures": _overlay_count(connection),
            "stamp": stamp,
        }

    if not reader.available:
        return {"updated": False, "symbols_with_signatures": 0, "stamp": None}

    connection.execute("DELETE FROM semantic_symbols WHERE kind = 'repo-signature'")
    by_file = defaultdict(list)
    for item in reader.all_agda_symbols(include_history=True):
        if item.get("kind") in {"function", "data", "record", "postulate"}:
            by_file[item["file"]].append(item)

    inserted = 0
    for _file, items in by_file.items():
        for item in items:
            signature = _signature_text(root, item)
            if not signature:
                continue
            fingerprint = make_fingerprint(signature)
            refs = _refs(signature, item["name"])
            connection.execute(
                """
                INSERT INTO semantic_symbols(
                    module_name, path, name, qualified_name, kind,
                    signature, normalized_signature, signature_sha256,
                    body_sha256, refs_json, surface_role
                ) VALUES(?, ?, ?, ?, 'repo-signature', ?, ?, ?, '', ?, ?)
                """,
                (
                    item["module_name"], item["file"], item["name"],
                    item["qualified_name"], signature,
                    fingerprint.normalized_signature, fingerprint.signature_sha256,
                    json.dumps(refs), classify_surface_role(item["module_name"]),
                ),
            )
            inserted += 1

    if stamp is not None:
        connection.execute(
            "INSERT INTO meta(key, value) VALUES(?, ?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (_STAMP_KEY, stamp),
        )
    connection.execute(
        "INSERT INTO meta(key, value) VALUES(?, ?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
        (_COUNT_KEY, str(inserted)),
    )
    connection.commit()
    return {"updated": True, "symbols_with_signatures": inserted, "stamp": stamp}
