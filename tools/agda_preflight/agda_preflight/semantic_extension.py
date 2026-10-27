from __future__ import annotations

from typing import Any, Optional

from . import discovery_catalog
from .narrative_cache import NarrativeCache, apply_narrative_gate
from .repo_index_bridge import RepoIndexReader
from .repository_coverage import repository_inventory_coverage
from .repository_discovery import RepositoryDiscovery
from .repository_inventory import ensure_inventory_schema
from .repository_store import sync_legacy_repo_index


def install_source_index_semantic_extension(source_index_cls: type) -> None:
    if getattr(source_index_cls, "_semantic_discovery_installed", False):
        return

    original_init = source_index_cls.__init__

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        original_init(self, *args, **kwargs)
        ensure_inventory_schema(self.connection)
        producer = self.connection.execute(
            "SELECT value FROM repository_meta WHERE key='inventory_producer'"
        ).fetchone()
        if producer is None or str(producer[0]) != "agda-preflight":
            sync_legacy_repo_index(self.root, self.connection)
        self.connection.commit()

    def _unified(self) -> RepositoryDiscovery:
        return RepositoryDiscovery(
            self.root,
            self,
            RepoIndexReader(self.root, connection=self.connection),
        )

    def refresh_semantic_catalog(self) -> int:
        """Legacy compatibility refresh; canonical `dashi-repo index` is DB-native."""
        return discovery_catalog.refresh_catalog(self.connection)

    def search_symbols(self, query: str, *, include_history: bool = False, limit: int = 50) -> list[dict]:
        discovery = _unified(self)
        try:
            return discovery.search_symbols(
                query,
                include_history=include_history,
                limit=limit,
            )
        finally:
            discovery.repo_index.close()

    def related_symbols(self, symbol: str, *, include_history: bool = False, limit: int = 50) -> dict:
        discovery = _unified(self)
        try:
            return discovery.related_symbols(
                symbol,
                include_history=include_history,
                limit=limit,
            )
        finally:
            discovery.repo_index.close()

    def narrative_archaeology(self, query: str, *, limit: int = 50) -> dict:
        return NarrativeCache(
            self.root,
            connection=self.connection,
        ).search(query, limit=limit)

    def _candidate_exists(receipt: dict) -> bool:
        related = receipt.get("related", {})
        return bool(
            receipt.get("live_matches")
            or receipt.get("historical_matches")
            or receipt.get("query_similar")
            or any(
                related.get(key)
                for key in ("signature_equivalent", "body_equivalent", "similar")
            )
        )

    def discovery_receipt(self, query: str, *, limit: int = 50) -> dict:
        discovery = _unified(self)
        try:
            receipt = discovery.discovery_receipt(query, limit=limit)
        finally:
            discovery.repo_index.close()

        native_coverage = repository_inventory_coverage(self.root, self.connection)
        if native_coverage.get("available"):
            coverage = dict(receipt.get("coverage", {}))
            coverage["repository_db"] = native_coverage
            receipt["coverage"] = coverage
            if _candidate_exists(receipt):
                receipt["absence_claim_permitted"] = False
                receipt["absence_status"] = "candidate_or_partial_object_exists"
            elif native_coverage.get("complete"):
                receipt["absence_claim_permitted"] = True
                receipt["absence_status"] = "confirmed_no_indexed_candidate"
            else:
                receipt["absence_claim_permitted"] = False
                receipt["absence_status"] = "search_incomplete"

        narrative = narrative_archaeology(self, query, limit=limit)
        return apply_narrative_gate(receipt, narrative)

    def object_detail(self, symbol_id: str) -> dict:
        discovery = _unified(self)
        try:
            return discovery.object_detail(symbol_id)
        finally:
            discovery.repo_index.close()

    def round_lineage(self, prefix: Optional[str] = None) -> dict:
        discovery = _unified(self)
        try:
            report = discovery.round_lineage(prefix=prefix)
        finally:
            discovery.repo_index.close()
        native_coverage = repository_inventory_coverage(self.root, self.connection)
        if native_coverage.get("available"):
            report["coverage"] = native_coverage
        return report

    source_index_cls.__init__ = __init__
    source_index_cls.refresh_semantic_catalog = refresh_semantic_catalog
    source_index_cls.search_symbols = search_symbols
    source_index_cls.related_symbols = related_symbols
    source_index_cls.narrative_archaeology = narrative_archaeology
    source_index_cls.discovery_receipt = discovery_receipt
    source_index_cls.object_detail = object_detail
    source_index_cls.round_lineage = round_lineage
    source_index_cls._semantic_discovery_installed = True
