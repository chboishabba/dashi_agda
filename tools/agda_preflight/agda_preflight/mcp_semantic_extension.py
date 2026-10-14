from __future__ import annotations


def install_mcp_adapter_semantic_extension(adapter_cls: type) -> None:
    if getattr(adapter_cls, "_semantic_discovery_installed", False):
        return

    def symbol_search(self, query: str, include_history: bool = False, limit: int = 50):
        return self.service.symbol_search(query, include_history=include_history, limit=limit)

    def related_symbols(self, symbol: str, include_history: bool = False, limit: int = 50):
        return self.service.related_symbols(symbol, include_history=include_history, limit=limit)

    def discover(self, query: str, limit: int = 50):
        return self.service.discover(query, limit=limit)

    def round_lineage(self, prefix: str | None = None):
        return self.service.round_lineage(prefix=prefix)

    adapter_cls.symbol_search = symbol_search
    adapter_cls.related_symbols = related_symbols
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
        async def symbol_search(query: str, include_history: bool = False, limit: int = 50):
            """Search indexed Agda symbols; historical RoundNNN snapshots are hidden by default."""
            return tools.symbol_search(query, include_history=include_history, limit=limit)

        @server.tool()
        async def related_symbols(symbol: str, include_history: bool = False, limit: int = 50):
            """Return exact, signature-equivalent, body-equivalent and structurally similar symbols."""
            return tools.related_symbols(symbol, include_history=include_history, limit=limit)

        @server.tool()
        async def discover(query: str, limit: int = 50):
            """Return a repository discovery receipt and whether an absence claim is justified."""
            return tools.discover(query, limit=limit)

        @server.tool()
        async def round_lineage(prefix: str | None = None):
            """Report read-only RoundNNN lineage, novelty and snapshot-noise ratios."""
            return tools.round_lineage(prefix=prefix)

    module.register_mcp_tools = register_mcp_tools
    module._semantic_discovery_installed = True
