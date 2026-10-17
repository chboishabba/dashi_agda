from __future__ import annotations

from collections import defaultdict
from typing import Optional

from .discovery import round_family, similarity_score
from .lineage import compute_round_lineage
from .query_discovery import _query_score


class RepositoryDiscovery:
    """Canonical DB-native discovery over normalized repository tables.

    The repo inventory owns whole-repo identity/source coverage. Signatures and
    bodies are produced by the preflight parser into relational tables. No
    serialized interface or narrative handoff participates in this path.
    """

    def __init__(self, root, source_index, repo_index) -> None:
        self.root = root
        self.source_index = source_index
        self.repo_index = repo_index
        self.connection = source_index.connection

    def _signature(self, symbol_id: str) -> dict:
        try:
            row = self.connection.execute(
                """
                SELECT signature, normalized_signature, signature_sha256, body_sha256
                FROM repo_symbol_signatures WHERE symbol_id=?
                """,
                (symbol_id,),
            ).fetchone()
        except Exception:
            row = None
        if row is None:
            return {
                "signature": "",
                "normalized_signature": "",
                "signature_sha256": "",
                "body_sha256": "",
            }
        return {
            "signature": str(row[0] or ""),
            "normalized_signature": str(row[1] or ""),
            "signature_sha256": str(row[2] or ""),
            "body_sha256": str(row[3] or ""),
        }

    def _refs(self, symbol_id: str) -> list[str]:
        try:
            rows = self.connection.execute(
                "SELECT DISTINCT to_symbol FROM repo_refs WHERE from_symbol=? ORDER BY to_symbol",
                (symbol_id,),
            ).fetchall()
        except Exception:
            return []
        return [str(row[0]) for row in rows]

    def _enrich(self, item: dict) -> dict:
        result = dict(item)
        result.update(self._signature(item["qualified_name"]))
        result["refs"] = self._refs(item["qualified_name"])
        result["preflight_indexed"] = bool(result.get("signature") or result.get("kind") in {"record", "data", "module"})
        result["signature_source"] = "repository-db/preflight-parser"
        return result

    def search_symbols(
        self,
        query: str,
        *,
        include_history: bool = False,
        limit: int = 50,
    ) -> list[dict]:
        return [
            self._enrich(item)
            for item in self.repo_index.search_symbols(
                query,
                include_history=include_history,
                limit=limit,
            )
        ]

    def _all(self, *, include_history: bool) -> list[dict]:
        return [
            self._enrich(item)
            for item in self.repo_index.all_agda_symbols(
                include_history=include_history
            )
        ]

    def _fuzzy(
        self,
        query: str,
        *,
        include_history: bool = True,
        limit: int = 50,
        threshold: float = 0.34,
    ) -> list[dict]:
        ranked = []
        for item in self._all(include_history=include_history):
            if item.get("kind") == "module":
                continue
            score = _query_score(query, item)
            if score < threshold:
                continue
            candidate = dict(item)
            candidate["query_similarity"] = score
            ranked.append(candidate)
        ranked.sort(
            key=lambda item: (
                item.get("surface_role") == "historical_snapshot",
                -float(item["query_similarity"]),
                item["qualified_name"],
            )
        )
        return ranked[:limit]

    def _by_signature_hash(
        self,
        column: str,
        value: str,
        *,
        exclude: str,
        include_history: bool,
        limit: int,
    ) -> list[dict]:
        if not value:
            return []
        role_clause = "" if include_history else "AND s.module NOT GLOB '*Round[0-9]*'"
        rows = self.connection.execute(
            """
            SELECT s.symbol_id
            FROM repo_symbol_signatures sig
            JOIN repo_symbols s ON s.symbol_id = sig.symbol_id
            WHERE sig.{column} = ? AND sig.symbol_id != ?
              AND s.language='agda' {role_clause}
            ORDER BY s.symbol_id LIMIT ?
            """.format(column=column, role_clause=role_clause),
            (value, exclude, limit),
        ).fetchall()
        result = []
        for row in rows:
            detail = self.repo_index.object_detail(str(row[0]))
            if detail.get("symbol") is not None:
                result.append(self._enrich(detail["symbol"]))
        return result

    def related_symbols(
        self,
        symbol: str,
        *,
        include_history: bool = False,
        limit: int = 50,
    ) -> dict:
        exact = self.search_symbols(
            symbol,
            include_history=include_history,
            limit=limit,
        )
        if not exact:
            return {
                "query_symbol": None,
                "exact": [],
                "signature_equivalent": [],
                "body_equivalent": [],
                "similar": self._fuzzy(
                    symbol,
                    include_history=include_history,
                    limit=limit,
                ),
            }
        target = exact[0]
        target_id = target["qualified_name"]
        signature_equivalent = (
            self._by_signature_hash(
                "signature_sha256",
                target.get("signature_sha256", "") if target.get("signature") else "",
                exclude=target_id,
                include_history=include_history,
                limit=limit,
            )
        )
        body_equivalent = self._by_signature_hash(
            "body_sha256",
            target.get("body_sha256", ""),
            exclude=target_id,
            include_history=include_history,
            limit=limit,
        ) if target.get("body_sha256") else []

        seen = {target_id}
        seen.update(item["qualified_name"] for item in signature_equivalent)
        seen.update(item["qualified_name"] for item in body_equivalent)
        similar = []
        for item in self._all(include_history=include_history):
            candidate_id = item["qualified_name"]
            if candidate_id in seen or item.get("kind") == "module":
                continue
            score = similarity_score(
                name_a=target.get("name", ""),
                signature_a=target.get("signature", ""),
                refs_a=target.get("refs", ()),
                name_b=item.get("name", ""),
                signature_b=item.get("signature", ""),
                refs_b=item.get("refs", ()),
            )
            query_score = _query_score(target.get("name", symbol), item)
            score = max(score, min(0.69, query_score))
            if score < 0.34:
                continue
            candidate = dict(item)
            candidate["similarity"] = score
            similar.append(candidate)
        similar.sort(
            key=lambda item: (
                item.get("surface_role") == "historical_snapshot",
                -float(item.get("similarity", 0.0)),
                item["qualified_name"],
            )
        )
        return {
            "query_symbol": target,
            "exact": exact,
            "signature_equivalent": signature_equivalent[:limit],
            "body_equivalent": body_equivalent[:limit],
            "similar": similar[:limit],
        }

    @staticmethod
    def _object_family(exact: list[dict], fuzzy: list[dict], related: dict) -> dict:
        members = {}
        for item in exact + fuzzy:
            members[item["qualified_name"]] = item
        for key in ("signature_equivalent", "body_equivalent", "similar"):
            for item in related.get(key, ()):
                members[item["qualified_name"]] = item
        ordered = sorted(
            members.values(),
            key=lambda item: (
                item.get("surface_role") == "historical_snapshot",
                0 if item.get("surface_role") == "canonical" else 1,
                item["qualified_name"],
            ),
        )
        return {
            "canonical_candidates": [item for item in ordered if item.get("surface_role") == "canonical"],
            "live_members": [item for item in ordered if item.get("surface_role") != "historical_snapshot"],
            "historical_members": [item for item in ordered if item.get("surface_role") == "historical_snapshot"],
            "inference": "repository DB discovery; equivalence/similarity remain structural evidence, not proof authority",
        }

    def discovery_receipt(self, query: str, *, limit: int = 50) -> dict:
        live = self.search_symbols(query, include_history=False, limit=limit)
        all_exact = self.search_symbols(query, include_history=True, limit=limit * 2)
        historical = [
            item for item in all_exact
            if item.get("surface_role") == "historical_snapshot"
        ]
        related = self.related_symbols(query, include_history=True, limit=limit)
        fuzzy = self._fuzzy(query, include_history=True, limit=limit)
        exact_ids = {item["qualified_name"] for item in all_exact}
        fuzzy = [item for item in fuzzy if item["qualified_name"] not in exact_ids]
        candidate_exists = bool(
            live
            or historical
            or fuzzy
            or any(
                related.get(key)
                for key in ("signature_equivalent", "body_equivalent", "similar")
            )
        )
        coverage = self.repo_index.coverage_status()
        if candidate_exists:
            absence_status = "candidate_or_partial_object_exists"
            absence_permitted = False
        elif coverage.get("complete"):
            absence_status = "confirmed_no_indexed_candidate"
            absence_permitted = True
        else:
            absence_status = "search_incomplete"
            absence_permitted = False
        return {
            "query": query,
            "live_matches": live,
            "historical_matches": historical,
            "query_similar": fuzzy,
            "related": related,
            "object_family": self._object_family(all_exact, fuzzy, related),
            "absence_claim_permitted": absence_permitted,
            "absence_status": absence_status,
            "coverage": {
                "repository_db": coverage,
                "exact_names_checked": True,
                "signature_equivalence_checked": True,
                "structural_similarity_checked": True,
                "historical_surfaces_checked": True,
            },
        }

    def object_detail(self, symbol_id: str) -> dict:
        base = self.repo_index.object_detail(symbol_id)
        if base.get("symbol") is None:
            matches = self.search_symbols(symbol_id, include_history=True, limit=1)
            return {"symbol": matches[0] if matches else None, "refs": []}
        base["symbol"] = self._enrich(base["symbol"])
        return base

    def round_lineage(self, prefix: Optional[str] = None) -> dict:
        grouped = defaultdict(list)
        for item in self._all(include_history=True):
            module = item.get("module_name") or ""
            family, number = round_family(module)
            if family is None or number is None:
                continue
            if prefix and not module.startswith(prefix):
                continue
            if item["kind"] == "module":
                continue
            grouped[module].append(item)
        modules = []
        for module, items in grouped.items():
            symbols = []
            for item in items:
                signature_hash = item.get("signature_sha256") or "kind:" + item["kind"]
                symbols.append(
                    {
                        "qualified_name": item["qualified_name"],
                        "signature_sha256": signature_hash,
                    }
                )
            modules.append({"module_name": module, "symbols": symbols})
        report = compute_round_lineage(modules)
        report["inventory_source"] = "repository-db/preflight-parser"
        report["coverage"] = self.repo_index.coverage_status()
        return report
