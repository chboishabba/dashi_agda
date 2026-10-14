from __future__ import annotations

from typing import Optional


def install_service_semantic_extension(service_cls: type) -> None:
    if getattr(service_cls, "_semantic_discovery_installed", False):
        return

    def refresh_semantic_catalog(self) -> dict:
        count = self.index.refresh_semantic_catalog()
        return {"symbols_indexed": count}

    def symbol_search(self, query: str, *, include_history: bool = False, limit: int = 50) -> dict:
        return {
            "query": query,
            "include_history": include_history,
            "results": self.index.search_symbols(
                query,
                include_history=include_history,
                limit=limit,
            ),
        }

    def related_symbols(self, symbol: str, *, include_history: bool = False, limit: int = 50) -> dict:
        return self.index.related_symbols(
            symbol,
            include_history=include_history,
            limit=limit,
        )

    def discover(self, query: str, *, limit: int = 50) -> dict:
        return self.index.discovery_receipt(query, limit=limit)

    def round_lineage(self, prefix: Optional[str] = None) -> dict:
        return self.index.round_lineage(prefix=prefix)

    service_cls.refresh_semantic_catalog = refresh_semantic_catalog
    service_cls.symbol_search = symbol_search
    service_cls.related_symbols = related_symbols
    service_cls.discover = discover
    service_cls.round_lineage = round_lineage
    service_cls._semantic_discovery_installed = True
