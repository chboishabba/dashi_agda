from __future__ import annotations

from typing import Any

from . import discovery_catalog
from . import query_discovery


def install_source_index_semantic_extension(source_index_cls: type) -> None:
    if getattr(source_index_cls, "_semantic_discovery_installed", False):
        return

    original_init = source_index_cls.__init__

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        original_init(self, *args, **kwargs)
        discovery_catalog.ensure_catalog_schema(self.connection)
        self.connection.commit()

    def refresh_semantic_catalog(self) -> int:
        return discovery_catalog.refresh_catalog(self.connection)

    def search_symbols(self, query: str, *, include_history: bool = False, limit: int = 50) -> list[dict]:
        return discovery_catalog.search_symbols(
            self.connection,
            query,
            include_history=include_history,
            limit=limit,
        )

    def related_symbols(self, symbol: str, *, include_history: bool = False, limit: int = 50) -> dict:
        return discovery_catalog.related_symbols(
            self.connection,
            symbol,
            include_history=include_history,
            limit=limit,
        )

    def discovery_receipt(self, query: str, *, limit: int = 50) -> dict:
        return query_discovery.discovery_receipt(self.connection, query, limit=limit)

    def round_lineage(self, prefix: str | None = None) -> dict:
        return discovery_catalog.round_lineage(self.connection, prefix=prefix)

    source_index_cls.__init__ = __init__
    source_index_cls.refresh_semantic_catalog = refresh_semantic_catalog
    source_index_cls.search_symbols = search_symbols
    source_index_cls.related_symbols = related_symbols
    source_index_cls.discovery_receipt = discovery_receipt
    source_index_cls.round_lineage = round_lineage
    source_index_cls._semantic_discovery_installed = True
