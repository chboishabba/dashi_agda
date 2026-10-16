from __future__ import annotations

from typing import Any, Optional


def install_mcp_adapter_semantic_extension(adapter_cls: type) -> None:
    if getattr(adapter_cls, "_semantic_discovery_installed", False):
        return

    def symbol_search(self, query: str, include_history: bool = False, limit: int = 50):
        return self.service.symbol_search(query, include_history=include_history, limit=limit)

    def related_symbols(self, symbol: str, include_history: bool = False, limit: int = 50):
        return self.service.related_symbols(symbol, include_history=include_history, limit=limit)

    def object_detail(self, symbol_id: str):
        return self.service.object_detail(symbol_id)

    def narrative_archaeology(self, query: str, limit: int = 50):
        return self.service.narrative_archaeology(query, limit=limit)

    def narrative_history(self, query: str, limit: int = 50):
        return self.service.narrative_history(query, limit=limit)

    def narrative_frontier(self, query: str, limit: int = 100):
        return self.service.narrative_frontier(query, limit=limit)

    def narrative_stale(self, query: str, limit: int = 100):
        return self.service.narrative_stale(query, limit=limit)

    def narrative_explain(self, query: str, limit: int = 50):
        return self.service.narrative_explain(query, limit=limit)

    def discover(self, query: str, limit: int = 50):
        return self.service.discover(query, limit=limit)

    def round_lineage(self, prefix: Optional[str] = None):
        return self.service.round_lineage(prefix=prefix)

    adapter_cls.symbol_search = symbol_search
    adapter_cls.related_symbols = related_symbols
    adapter_cls.object_detail = object_detail
    adapter_cls.narrative_archaeology = narrative_archaeology
    adapter_cls.narrative_history = narrative_history
    adapter_cls.narrative_frontier = narrative_frontier
    adapter_cls.narrative_stale = narrative_stale
    adapter_cls.narrative_explain = narrative_explain
    adapter_cls.discover = discover
    adapter_cls.round_lineage = round_lineage
    adapter_cls._semantic_discovery_installed = True


def install_mcp_server_semantic_extension(module) -> None:
    if getattr(module, "_semantic_discovery_installed", False):
        return
    original = module.register_mcp_tools

    def register_mcp_tools(server, tools):
        original(server, tools)

        @server.tool()
        async def symbol_search(
            query: str,
            include_history: bool = False,
            limit: int = 50,
        ) -> dict[str, Any]:
            """Search repository symbols; numbered Round snapshots are hidden by default."""
            return tools.symbol_search(query, include_history=include_history, limit=limit)

        @server.tool()
        async def related_symbols(
            symbol: str,
            include_history: bool = False,
            limit: int = 50,
        ) -> dict[str, Any]:
            """Return exact, signature-equivalent and structurally similar symbols."""
            return tools.related_symbols(symbol, include_history=include_history, limit=limit)

        @server.tool()
        async def object_detail(symbol_id: str) -> dict[str, Any]:
            """Return one indexed object with source/status/requirements and references."""
            return tools.object_detail(symbol_id)

        @server.tool()
        async def narrative_archaeology(query: str, limit: int = 50) -> dict[str, Any]:
            """Search PR/commit development narrative without promoting it to truth authority."""
            return tools.narrative_archaeology(query, limit=limit)

        @server.tool()
        async def narrative_history(query: str, limit: int = 50) -> dict[str, Any]:
            """Return time-ordered development events relevant to an object/concept."""
            return tools.narrative_history(query, limit=limit)

        @server.tool()
        async def narrative_frontier(query: str, limit: int = 100) -> dict[str, Any]:
            """Return paid/open/nonclaim frontier genealogy from development history."""
            return tools.narrative_frontier(query, limit=limit)

        @server.tool()
        async def narrative_stale(query: str, limit: int = 100) -> dict[str, Any]:
            """Return heuristic older frontier statements potentially superseded later."""
            return tools.narrative_stale(query, limit=limit)

        @server.tool()
        async def narrative_explain(query: str, limit: int = 50) -> dict[str, Any]:
            """Return bounded plain-language development context and current frontier."""
            return tools.narrative_explain(query, limit=limit)

        @server.tool()
        async def discover(query: str, limit: int = 50) -> dict[str, Any]:
            """Return fail-closed semantic + narrative discovery/absence receipt."""
            return tools.discover(query, limit=limit)

        @server.tool()
        async def round_lineage(prefix: Optional[str] = None) -> dict[str, Any]:
            """Report read-only RoundNNN lineage, novelty and snapshot-noise ratios."""
            return tools.round_lineage(prefix=prefix)

    module.register_mcp_tools = register_mcp_tools
    module._semantic_discovery_installed = True
