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

    def proof_route(self, query: str, **kwargs):
        return self.service.proof_route(query, **kwargs)

    def proof_route_for_obligation(self, query: str, **kwargs):
        return self.service.proof_route_for_obligation(query, **kwargs)

    def formal_evidence_for_obligation(
        self,
        *,
        demand_ref: str,
        external_obligation_ref: str,
        statement_digest: str,
    ):
        return self.service.formal_evidence_for_obligation(
            demand_ref=demand_ref,
            external_obligation_ref=external_obligation_ref,
            statement_digest=statement_digest,
        )

    def proof_route_history(
        self,
        query: Optional[str] = None,
        da51_address: Optional[str] = None,
        limit: int = 50,
    ):
        return self.service.proof_route_history(
            query=query,
            da51_address=da51_address,
            limit=limit,
        )

    def da51_resolve(self, address: str):
        return self.service.da51_resolve(address)

    def da51_evidence(self, address: str):
        return self.service.da51_evidence(address)

    def da51_frontier(self, address: str):
        return self.service.da51_frontier(address)

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
    adapter_cls.proof_route = proof_route
    adapter_cls.proof_route_for_obligation = proof_route_for_obligation
    adapter_cls.formal_evidence_for_obligation = formal_evidence_for_obligation
    adapter_cls.proof_route_history = proof_route_history
    adapter_cls.da51_resolve = da51_resolve
    adapter_cls.da51_evidence = da51_evidence
    adapter_cls.da51_frontier = da51_frontier
    adapter_cls._semantic_discovery_installed = True


def register_repository_mcp_tools(server, tools) -> None:
    """Add repository-intelligence tools to an already-created MCP server."""

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

    @server.tool()
    async def proof_route(
        query: str,
        target_prover: str = "lean",
        claim_kind: str = "deductive",
        mathematical_status: str = "novel-open",
        statement_status: str = "not-transcribed",
        certification_status: str = "uncertified",
        da51_address: Optional[str] = None,
        source_declaration: Optional[str] = None,
        current_source_hash: Optional[str] = None,
        limit: int = 50,
    ) -> dict[str, Any]:
        """Discover-before-prove and return an authority-neutral backend route."""
        return tools.proof_route(
            query,
            target_prover=target_prover,
            claim_kind=claim_kind,
            mathematical_status=mathematical_status,
            statement_status=statement_status,
            certification_status=certification_status,
            da51_address=da51_address,
            source_declaration=source_declaration,
            current_source_hash=current_source_hash,
            limit=limit,
        )

    @server.tool()
    async def proof_route_for_obligation(
        query: str,
        demand_ref: str,
        external_obligation_ref: str,
        statement_digest: str,
        target_prover: str = "lean",
        claim_kind: str = "deductive",
        mathematical_status: str = "novel-open",
        statement_status: str = "not-transcribed",
        certification_status: str = "uncertified",
        da51_address: Optional[str] = None,
        source_declaration: Optional[str] = None,
        current_source_hash: Optional[str] = None,
        limit: int = 50,
    ) -> dict[str, Any]:
        """Route one external SLR/formal obligation without copying its semantic payload."""
        return tools.proof_route_for_obligation(
            query,
            demand_ref=demand_ref,
            external_obligation_ref=external_obligation_ref,
            statement_digest=statement_digest,
            target_prover=target_prover,
            claim_kind=claim_kind,
            mathematical_status=mathematical_status,
            statement_status=statement_status,
            certification_status=certification_status,
            da51_address=da51_address,
            source_declaration=source_declaration,
            current_source_hash=current_source_hash,
            limit=limit,
        )

    @server.tool()
    async def formal_evidence_for_obligation(
        demand_ref: str,
        external_obligation_ref: str,
        statement_digest: str,
    ) -> dict[str, Any]:
        """Return exact evidence joins for one demand/obligation/statement digest."""
        return tools.formal_evidence_for_obligation(
            demand_ref=demand_ref,
            external_obligation_ref=external_obligation_ref,
            statement_digest=statement_digest,
        )

    @server.tool()
    async def proof_route_history(
        query: Optional[str] = None,
        da51_address: Optional[str] = None,
        limit: int = 50,
    ) -> dict[str, Any]:
        """Return persisted routing receipts; these are scheduling evidence only."""
        return tools.proof_route_history(
            query=query,
            da51_address=da51_address,
            limit=limit,
        )

    @server.tool()
    async def da51_resolve(address: str) -> dict[str, Any]:
        """Resolve canonical DA51 wire metadata, links and evidence without authority promotion."""
        return tools.da51_resolve(address)

    @server.tool()
    async def da51_evidence(address: str) -> dict[str, Any]:
        """Return producer/artifact evidence edges for a DA51 identity."""
        return tools.da51_evidence(address)

    @server.tool()
    async def da51_frontier(address: str) -> dict[str, Any]:
        """Return proof-routing debt/history attached to a DA51 identity."""
        return tools.da51_frontier(address)


def install_mcp_server_semantic_extension(module) -> None:
    """Expose the additive registry without mutating legacy register_mcp_tools."""

    if getattr(module, "_repository_intelligence_tools_installed", False):
        return
    module.register_repository_mcp_tools = register_repository_mcp_tools
    module._repository_intelligence_tools_installed = True
