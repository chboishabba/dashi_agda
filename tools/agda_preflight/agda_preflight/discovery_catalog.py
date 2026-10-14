from __future__ import annotations

import json
import sqlite3
from typing import Iterable

from .discovery import classify_surface_role, make_fingerprint, similarity_score
from .lineage import compute_round_lineage


def ensure_catalog_schema(connection: sqlite3.Connection) -> None:
    connection.executescript(
        """
        CREATE TABLE IF NOT EXISTS semantic_symbols (
            module_name TEXT NOT NULL,
            path TEXT NOT NULL,
            name TEXT NOT NULL,
            qualified_name TEXT NOT NULL,
            kind TEXT NOT NULL,
            signature TEXT NOT NULL,
            normalized_signature TEXT NOT NULL,
            signature_sha256 TEXT NOT NULL,
            body_sha256 TEXT NOT NULL,
            refs_json TEXT NOT NULL,
            surface_role TEXT NOT NULL,
            PRIMARY KEY(module_name, qualified_name, kind)
        ) WITHOUT ROWID;

        CREATE INDEX IF NOT EXISTS semantic_symbols_by_name
            ON semantic_symbols(name);
        CREATE INDEX IF NOT EXISTS semantic_symbols_by_qualified
            ON semantic_symbols(qualified_name);
        CREATE INDEX IF NOT EXISTS semantic_symbols_by_signature
            ON semantic_symbols(signature_sha256);
        CREATE INDEX IF NOT EXISTS semantic_symbols_by_surface
            ON semantic_symbols(surface_role);
        """
    )


def _iter_interface_symbols(module_name: str, interface: dict) -> Iterable[dict]:
    collection_kinds = {
        "functions": "function",
        "records": "record",
        "data": "data",
        "datatypes": "data",
        "constructors": "constructor",
        "projections": "projection",
        "postulates": "postulate",
        "fields": "field",
    }
    for key, kind in collection_kinds.items():
        values = interface.get(key, ())
        if isinstance(values, dict):
            values = values.values()
        if not isinstance(values, (list, tuple, dict_values_type())):
            continue
        for value in values:
            if isinstance(value, str):
                name = value
                signature = ""
                body = ""
                refs: list[str] = []
            elif isinstance(value, dict):
                name = str(value.get("name") or value.get("field") or value.get("constructor") or "")
                signature = str(
                    value.get("type")
                    or value.get("signature")
                    or value.get("type_text")
                    or ""
                )
                body = str(value.get("body") or value.get("definition") or "")
                raw_refs = value.get("refs") or value.get("references") or ()
                refs = [str(item) for item in raw_refs] if isinstance(raw_refs, (list, tuple)) else []
            else:
                continue
            if not name:
                continue
            qualified_name = name if "." in name else f"{module_name}.{name}"
            fingerprint = make_fingerprint(signature, body)
            yield {
                "name": name.rsplit(".", 1)[-1],
                "qualified_name": qualified_name,
                "kind": kind,
                "signature": signature,
                "normalized_signature": fingerprint.normalized_signature,
                "signature_sha256": fingerprint.signature_sha256,
                "body_sha256": fingerprint.body_sha256,
                "refs": refs,
            }

    exports = interface.get("exports", ())
    if isinstance(exports, dict):
        for name, payload in exports.items():
            if isinstance(payload, dict):
                signature = str(payload.get("type") or payload.get("signature") or "")
                kind = str(payload.get("kind") or "export")
            else:
                signature = ""
                kind = "export"
            fingerprint = make_fingerprint(signature)
            qualified_name = str(name) if "." in str(name) else f"{module_name}.{name}"
            yield {
                "name": str(name).rsplit(".", 1)[-1],
                "qualified_name": qualified_name,
                "kind": kind,
                "signature": signature,
                "normalized_signature": fingerprint.normalized_signature,
                "signature_sha256": fingerprint.signature_sha256,
                "body_sha256": "",
                "refs": [],
            }


def dict_values_type():
    return type({}.values())


def refresh_catalog(connection: sqlite3.Connection) -> int:
    ensure_catalog_schema(connection)
    connection.execute("DELETE FROM semantic_symbols")
    rows = connection.execute(
        "SELECT path, module_name, interface_json FROM modules WHERE interface_json != ''"
    ).fetchall()
    inserted = 0
    seen: set[tuple[str, str, str]] = set()
    for row in rows:
        try:
            interface = json.loads(row["interface_json"])
        except (TypeError, ValueError, json.JSONDecodeError):
            continue
        if not isinstance(interface, dict):
            continue
        role = classify_surface_role(row["module_name"])
        for symbol in _iter_interface_symbols(row["module_name"], interface):
            key = (row["module_name"], symbol["qualified_name"], symbol["kind"])
            if key in seen:
                continue
            seen.add(key)
            connection.execute(
                """
                INSERT INTO semantic_symbols(
                    module_name, path, name, qualified_name, kind,
                    signature, normalized_signature, signature_sha256,
                    body_sha256, refs_json, surface_role
                ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    row["module_name"], row["path"], symbol["name"],
                    symbol["qualified_name"], symbol["kind"], symbol["signature"],
                    symbol["normalized_signature"], symbol["signature_sha256"],
                    symbol["body_sha256"], json.dumps(symbol["refs"]), role,
                ),
            )
            inserted += 1
    connection.commit()
    return inserted


def _row_dict(row: sqlite3.Row) -> dict:
    result = dict(row)
    try:
        result["refs"] = json.loads(result.pop("refs_json", "[]"))
    except (TypeError, ValueError, json.JSONDecodeError):
        result["refs"] = []
    return result


def search_symbols(
    connection: sqlite3.Connection,
    query: str,
    *,
    include_history: bool = False,
    limit: int = 50,
) -> list[dict]:
    ensure_catalog_schema(connection)
    query = query.strip()
    if not query:
        return []
    role_clause = "" if include_history else "AND surface_role != 'historical_snapshot'"
    rows = connection.execute(
        f"""
        SELECT * FROM semantic_symbols
        WHERE (
            qualified_name = ? OR name = ? OR qualified_name LIKE ?
        ) {role_clause}
        ORDER BY
            CASE WHEN qualified_name = ? THEN 0 WHEN name = ? THEN 1 ELSE 2 END,
            CASE WHEN surface_role = 'canonical' THEN 0
                 WHEN surface_role = 'current' THEN 1
                 WHEN surface_role = 'historical_snapshot' THEN 9
                 ELSE 5 END,
            length(qualified_name), qualified_name
        LIMIT ?
        """,
        (query, query, f"%.{query}", query, query, limit),
    ).fetchall()
    return [_row_dict(row) for row in rows]


def related_symbols(
    connection: sqlite3.Connection,
    symbol: str,
    *,
    include_history: bool = False,
    limit: int = 50,
) -> dict:
    matches = search_symbols(connection, symbol, include_history=include_history, limit=limit)
    if not matches:
        return {"query_symbol": None, "exact": [], "signature_equivalent": [], "body_equivalent": [], "similar": []}
    target = matches[0]
    role_clause = "" if include_history else "WHERE surface_role != 'historical_snapshot'"
    rows = connection.execute(
        f"SELECT * FROM semantic_symbols {role_clause} ORDER BY qualified_name"
    ).fetchall()
    candidates = [_row_dict(row) for row in rows]
    exact = [item for item in matches if item["qualified_name"] == symbol or item["name"] == symbol]
    signature_equivalent = [
        item for item in candidates
        if item["qualified_name"] != target["qualified_name"]
        and target["signature_sha256"]
        and item["signature_sha256"] == target["signature_sha256"]
    ]
    body_equivalent = [
        item for item in candidates
        if item["qualified_name"] != target["qualified_name"]
        and target["body_sha256"]
        and item["body_sha256"] == target["body_sha256"]
    ]
    excluded = {item["qualified_name"] for item in exact + signature_equivalent + body_equivalent}
    excluded.add(target["qualified_name"])
    similar = []
    for item in candidates:
        if item["qualified_name"] in excluded:
            continue
        score = similarity_score(
            name_a=target["name"],
            signature_a=target["signature"],
            refs_a=target.get("refs", ()),
            name_b=item["name"],
            signature_b=item["signature"],
            refs_b=item.get("refs", ()),
        )
        if score < 0.35:
            continue
        enriched = dict(item)
        enriched["similarity"] = score
        similar.append(enriched)
    similar.sort(key=lambda item: (-item["similarity"], item["qualified_name"]))
    return {
        "query_symbol": target,
        "exact": exact,
        "signature_equivalent": signature_equivalent[:limit],
        "body_equivalent": body_equivalent[:limit],
        "similar": similar[:limit],
    }


def discovery_receipt(connection: sqlite3.Connection, query: str, *, limit: int = 50) -> dict:
    live = search_symbols(connection, query, include_history=False, limit=limit)
    all_matches = search_symbols(connection, query, include_history=True, limit=limit * 2)
    historical = [item for item in all_matches if item["surface_role"] == "historical_snapshot"]
    related = related_symbols(connection, query, include_history=True, limit=limit)
    related_nonempty = any(related[key] for key in ("signature_equivalent", "body_equivalent", "similar"))
    permitted = not live and not historical and not related_nonempty
    return {
        "query": query,
        "live_matches": live,
        "historical_matches": historical,
        "related": related,
        "absence_claim_permitted": permitted,
        "coverage": {
            "exact_names_checked": True,
            "qualified_suffixes_checked": True,
            "signature_equivalence_checked": related["query_symbol"] is not None,
            "structural_similarity_checked": related["query_symbol"] is not None,
            "historical_surfaces_checked": True,
        },
    }


def round_lineage(connection: sqlite3.Connection, prefix: str | None = None) -> dict:
    ensure_catalog_schema(connection)
    if prefix:
        module_rows = connection.execute(
            "SELECT DISTINCT module_name FROM semantic_symbols WHERE module_name LIKE ? ORDER BY module_name",
            (f"{prefix}%",),
        ).fetchall()
    else:
        module_rows = connection.execute(
            "SELECT DISTINCT module_name FROM semantic_symbols ORDER BY module_name"
        ).fetchall()
    modules = []
    for module_row in module_rows:
        name = module_row["module_name"]
        symbols = connection.execute(
            "SELECT qualified_name, signature_sha256 FROM semantic_symbols WHERE module_name = ?",
            (name,),
        ).fetchall()
        modules.append({"module_name": name, "symbols": [dict(row) for row in symbols]})
    return compute_round_lineage(modules)
