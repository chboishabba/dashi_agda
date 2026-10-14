from __future__ import annotations

from difflib import SequenceMatcher
from pathlib import Path
import re
import sqlite3
from typing import Optional

from . import discovery_catalog


_TOKEN_RE = re.compile(r"[A-Za-z0-9]+")
_EXCLUDED_PARTS = {".git", ".cache", "_build", "build", "dist", ".venv", "venv"}


def _tokens(text: str) -> set[str]:
    return {item.lower() for item in _TOKEN_RE.findall(text) if len(item) > 1}


def _query_score(query: str, row: dict) -> float:
    q = query.lower().strip()
    name = row["name"].lower()
    qualified = row["qualified_name"].lower()
    signature = row.get("signature", "").lower()
    q_tokens = _tokens(q)
    haystack_tokens = _tokens(" ".join((name, qualified, signature)))
    if q_tokens and haystack_tokens:
        token_score = len(q_tokens & haystack_tokens) / len(q_tokens | haystack_tokens)
    else:
        token_score = 0.0
    name_score = max(
        SequenceMatcher(None, q, name).ratio(),
        SequenceMatcher(None, q, qualified).ratio(),
    )
    substring = 1.0 if q and (q in name or q in qualified) else 0.0
    return min(1.0, 0.50 * name_score + 0.35 * token_score + 0.15 * substring)


def fuzzy_query_candidates(
    connection: sqlite3.Connection,
    query: str,
    *,
    include_history: bool = True,
    limit: int = 50,
    threshold: float = 0.34,
) -> list[dict]:
    discovery_catalog.ensure_catalog_fresh(connection)
    if include_history:
        rows = connection.execute(
            "SELECT * FROM semantic_symbols ORDER BY qualified_name"
        ).fetchall()
    else:
        rows = connection.execute(
            "SELECT * FROM semantic_symbols WHERE surface_role != 'historical_snapshot' ORDER BY qualified_name"
        ).fetchall()
    ranked = []
    for row in rows:
        item = discovery_catalog._row_dict(row)
        score = _query_score(query, item)
        if score < threshold:
            continue
        item["query_similarity"] = score
        ranked.append(item)
    ranked.sort(
        key=lambda item: (
            item["surface_role"] == "historical_snapshot",
            -item["query_similarity"],
            item["qualified_name"],
        )
    )
    return ranked[:limit]


def _object_family(exact: list[dict], fuzzy: list[dict], related: dict) -> dict:
    members: dict[str, dict] = {}
    for item in exact:
        members[item["qualified_name"]] = item
    for key in ("signature_equivalent", "body_equivalent", "similar"):
        for item in related.get(key, ()):
            members[item["qualified_name"]] = item
    for item in fuzzy:
        members[item["qualified_name"]] = item
    ordered = sorted(
        members.values(),
        key=lambda item: (
            item["surface_role"] == "historical_snapshot",
            0 if item["surface_role"] == "canonical" else 1,
            item["qualified_name"],
        ),
    )
    canonical = [item for item in ordered if item["surface_role"] == "canonical"]
    live = [item for item in ordered if item["surface_role"] != "historical_snapshot"]
    historical = [item for item in ordered if item["surface_role"] == "historical_snapshot"]
    return {
        "canonical_candidates": canonical,
        "live_members": live,
        "historical_members": historical,
        "complete": bool(live),
        "inference": "structural/indexed; not proof equivalence",
    }


def _repository_coverage(root: Path, connection: sqlite3.Connection) -> dict:
    indexed_paths = {
        str(row["path"])
        for row in connection.execute("SELECT path FROM modules").fetchall()
        if str(row["path"]).endswith(".agda")
    }
    repo_paths = set()
    for path in root.rglob("*.agda"):
        try:
            relative = path.resolve().relative_to(root.resolve())
        except ValueError:
            continue
        if any(part in _EXCLUDED_PARTS for part in relative.parts):
            continue
        repo_paths.add(relative.as_posix())
    missing = sorted(repo_paths - indexed_paths)
    return {
        "repository_agda_files": len(repo_paths),
        "indexed_agda_files": len(indexed_paths & repo_paths),
        "repository_index_complete": not missing,
        "missing_indexed_files": missing[:100],
        "missing_indexed_files_truncated": len(missing) > 100,
    }


def discovery_receipt(
    connection: sqlite3.Connection,
    query: str,
    *,
    limit: int = 50,
    root: Optional[Path] = None,
) -> dict:
    live = discovery_catalog.search_symbols(
        connection, query, include_history=False, limit=limit
    )
    all_exact = discovery_catalog.search_symbols(
        connection, query, include_history=True, limit=limit * 2
    )
    historical = [
        item for item in all_exact
        if item["surface_role"] == "historical_snapshot"
    ]
    related = discovery_catalog.related_symbols(
        connection, query, include_history=True, limit=limit
    )
    fuzzy = fuzzy_query_candidates(
        connection, query, include_history=True, limit=limit
    )
    exact_names = {match["qualified_name"] for match in all_exact}
    fuzzy_nonexact = [
        item for item in fuzzy
        if item["qualified_name"] not in exact_names
    ]
    related_nonempty = any(
        related.get(key)
        for key in ("signature_equivalent", "body_equivalent", "similar")
    )
    candidate_exists = bool(live or historical or related_nonempty or fuzzy_nonexact)
    coverage = {
        "exact_names_checked": True,
        "qualified_suffixes_checked": True,
        "signature_equivalence_checked": related["query_symbol"] is not None,
        "structural_similarity_checked": True,
        "query_similarity_checked": True,
        "historical_surfaces_checked": True,
    }

    provisional_absence = not candidate_exists
    if provisional_absence and root is not None:
        repo_coverage = _repository_coverage(root, connection)
        coverage.update(repo_coverage)
        absence_permitted = repo_coverage["repository_index_complete"]
        absence_status = (
            "confirmed_no_indexed_candidate"
            if absence_permitted
            else "search_incomplete"
        )
    elif provisional_absence:
        coverage["repository_index_complete"] = False
        absence_permitted = False
        absence_status = "search_incomplete"
    else:
        absence_permitted = False
        absence_status = "candidate_or_partial_object_exists"

    return {
        "query": query,
        "live_matches": live,
        "historical_matches": historical,
        "query_similar": fuzzy_nonexact,
        "related": related,
        "object_family": _object_family(all_exact, fuzzy_nonexact, related),
        "absence_claim_permitted": absence_permitted,
        "absence_status": absence_status,
        "coverage": coverage,
    }
