from __future__ import annotations

from collections import defaultdict
from typing import Optional

from . import discovery_catalog
from .discovery import round_family
from .lineage import compute_round_lineage
from .query_discovery import _query_score
from .repo_index_bridge import RepoIndexReader


class UnifiedDiscovery:
    """Join repo-wide identity with preflight's incremental type surface.

    Repo-index owns identity, source spans, refs, requirements, explicit status
    and repository completeness. Preflight contributes persisted interface
    signatures/fingerprints and structural similarity. Neither layer replaces
    Agda typechecking.
    """

    def __init__(self, root, source_index, repo_index: RepoIndexReader) -> None:
        self.root = root
        self.source_index = source_index
        self.repo_index = repo_index

    def _overlay_map(self, include_history: bool = True) -> dict[str, dict]:
        discovery_catalog.ensure_catalog_fresh(self.source_index.connection)
        if include_history:
            rows = self.source_index.connection.execute(
                "SELECT * FROM semantic_symbols ORDER BY qualified_name"
            ).fetchall()
        else:
            rows = self.source_index.connection.execute(
                "SELECT * FROM semantic_symbols WHERE surface_role != 'historical_snapshot' ORDER BY qualified_name"
            ).fetchall()
        result = {}
        for row in rows:
            item = discovery_catalog._row_dict(row)
            prior = result.get(item["qualified_name"])
            if prior is None or prior.get("kind") == "reexport":
                result[item["qualified_name"]] = item
        return result

    @staticmethod
    def _merge(base: dict, overlay: Optional[dict]) -> dict:
        merged = dict(base)
        if overlay is not None:
            for key in (
                "signature", "normalized_signature", "signature_sha256",
                "body_sha256", "refs",
            ):
                if overlay.get(key):
                    merged[key] = overlay[key]
            merged["preflight_indexed"] = True
        else:
            merged["preflight_indexed"] = False
        return merged

    def search_symbols(
        self,
        query: str,
        *,
        include_history: bool = False,
        limit: int = 50,
    ) -> list[dict]:
        overlay = self._overlay_map(include_history=True)
        if self.repo_index.available:
            matches = self.repo_index.search_symbols(
                query, include_history=include_history, limit=limit
            )
            return [self._merge(item, overlay.get(item["qualified_name"])) for item in matches]
        return discovery_catalog.search_symbols(
            self.source_index.connection,
            query,
            include_history=include_history,
            limit=limit,
        )

    def _repo_fuzzy(
        self,
        query: str,
        *,
        include_history: bool = True,
        limit: int = 50,
        threshold: float = 0.34,
    ) -> list[dict]:
        overlay = self._overlay_map(include_history=True)
        candidates = self.repo_index.all_agda_symbols(include_history=include_history)
        ranked = []
        for base in candidates:
            if base["kind"] == "module":
                continue
            score = _query_score(query, base)
            if score < threshold:
                continue
            item = self._merge(base, overlay.get(base["qualified_name"]))
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

    def related_symbols(
        self,
        symbol: str,
        *,
        include_history: bool = False,
        limit: int = 50,
    ) -> dict:
        exact = self.search_symbols(symbol, include_history=include_history, limit=limit)
        if not exact:
            return {
                "query_symbol": None,
                "exact": [],
                "signature_equivalent": [],
                "body_equivalent": [],
                "similar": self._repo_fuzzy(
                    symbol, include_history=include_history, limit=limit
                ) if self.repo_index.available else [],
            }
        target = exact[0]
        overlay_report = discovery_catalog.related_symbols(
            self.source_index.connection,
            target["qualified_name"],
            include_history=include_history,
            limit=limit,
        )
        repo_by_id = {
            item["qualified_name"]: item
            for item in self.repo_index.all_agda_symbols(include_history=include_history)
        } if self.repo_index.available else {}

        def enrich(items):
            out = []
            for item in items:
                base = repo_by_id.get(item["qualified_name"])
                if base is not None:
                    merged = self._merge(base, item)
                else:
                    merged = dict(item)
                    merged.setdefault("inventory_source", "preflight-overlay")
                    merged["preflight_indexed"] = True
                if "similarity" in item:
                    merged["similarity"] = item["similarity"]
                out.append(merged)
            return out

        signature_equivalent = enrich(overlay_report.get("signature_equivalent", ()))
        body_equivalent = enrich(overlay_report.get("body_equivalent", ()))
        seen = {target["qualified_name"]}
        seen.update(item["qualified_name"] for item in signature_equivalent)
        seen.update(item["qualified_name"] for item in body_equivalent)
        similar = enrich(overlay_report.get("similar", ()))
        seen.update(item["qualified_name"] for item in similar)
        if self.repo_index.available:
            for item in self._repo_fuzzy(
                target["name"], include_history=include_history, limit=max(limit * 2, 50)
            ):
                if item["qualified_name"] in seen or item["qualified_name"] == target["qualified_name"]:
                    continue
                score = item.pop("query_similarity", 0.0)
                item["similarity"] = min(0.69, score)
                similar.append(item)
                seen.add(item["qualified_name"])
        similar.sort(key=lambda item: (-float(item.get("similarity", 0.0)), item["qualified_name"]))
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
            "inference": "indexed discovery; equivalence labels remain structural, not proof authority",
        }

    def discovery_receipt(self, query: str, *, limit: int = 50) -> dict:
        live = self.search_symbols(query, include_history=False, limit=limit)
        all_exact = self.search_symbols(query, include_history=True, limit=limit * 2)
        historical = [item for item in all_exact if item.get("surface_role") == "historical_snapshot"]
        related = self.related_symbols(query, include_history=True, limit=limit)
        fuzzy = self._repo_fuzzy(query, include_history=True, limit=limit) if self.repo_index.available else []
        exact_ids = {item["qualified_name"] for item in all_exact}
        fuzzy = [item for item in fuzzy if item["qualified_name"] not in exact_ids]
        candidate_exists = bool(
            live
            or historical
            or fuzzy
            or any(related.get(key) for key in ("signature_equivalent", "body_equivalent", "similar"))
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
                "repo_index": coverage,
                "exact_names_checked": True,
                "signature_equivalence_checked": related.get("query_symbol") is not None,
                "structural_similarity_checked": True,
                "historical_surfaces_checked": True,
            },
        }

    def object_detail(self, symbol_id: str) -> dict:
        base = self.repo_index.object_detail(symbol_id)
        if base.get("symbol") is None:
            matches = self.search_symbols(symbol_id, include_history=True, limit=1)
            return {"symbol": matches[0] if matches else None, "refs": []}
        overlay = self._overlay_map(include_history=True).get(symbol_id)
        base["symbol"] = self._merge(base["symbol"], overlay)
        return base

    def round_lineage(self, prefix: Optional[str] = None) -> dict:
        if not self.repo_index.available:
            return discovery_catalog.round_lineage(self.source_index.connection, prefix=prefix)
        overlay = self._overlay_map(include_history=True)
        grouped = defaultdict(list)
        for item in self.repo_index.all_agda_symbols(include_history=True):
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
                enriched = overlay.get(item["qualified_name"])
                signature_hash = (
                    enriched.get("signature_sha256")
                    if enriched is not None and enriched.get("signature_sha256")
                    else "kind:" + item["kind"]
                )
                symbols.append({
                    "qualified_name": item["qualified_name"],
                    "signature_sha256": signature_hash,
                })
            modules.append({"module_name": module, "symbols": symbols})
        report = compute_round_lineage(modules)
        report["inventory_source"] = "repo-index"
        report["signature_change_detection"] = "preflight-signature where indexed; otherwise kind-level only"
        report["coverage"] = self.repo_index.coverage_status()
        return report
