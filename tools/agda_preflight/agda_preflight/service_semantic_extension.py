from __future__ import annotations

from typing import Optional

from .development_history import (
    NarrativeEvent,
    archaeology,
    frontier_genealogy,
    stale_frontiers,
)
from .external_proof_bridge import ExternalProofDemand, ExternalProofRouter
from .proof_router import ProofRouteRequest, ProofRouter
from .repository_store import load_narrative_events


def install_service_semantic_extension(service_cls: type) -> None:
    if getattr(service_cls, "_semantic_discovery_installed", False):
        return

    def _events(self):
        return [
            NarrativeEvent.from_record(item)
            for item in load_narrative_events(self.index.connection)
        ]

    def _proof_router(self):
        return ProofRouter(
            discovery=self.discover,
            semantic_catalog=getattr(self, "semantic", None),
            connection=self.index.connection,
        )

    def _external_router(self):
        return ExternalProofRouter(_proof_router(self), self.index.connection)

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

    def object_detail(self, symbol_id: str) -> dict:
        return self.index.object_detail(symbol_id)

    def narrative_archaeology(self, query: str, *, limit: int = 50) -> dict:
        return self.index.narrative_archaeology(query, limit=limit)

    def narrative_history(self, query: str, *, limit: int = 50) -> dict:
        ranked = archaeology(_events(self), query, limit=max(limit * 3, 60))
        selected = [item["event"] for item in ranked[:limit]]
        selected.sort(key=lambda event: (event.timestamp, event.event_id))
        return {
            "query": query,
            "authority": "development-narrative",
            "events": [event.as_record() for event in selected],
        }

    def narrative_frontier(self, query: str, *, limit: int = 100) -> dict:
        return {
            "query": query,
            "authority": "development-narrative",
            "genealogy": frontier_genealogy(_events(self), query, limit=limit),
        }

    def narrative_stale(self, query: str, *, limit: int = 100) -> dict:
        return {
            "query": query,
            "authority": "development-narrative-heuristic",
            "potentially_stale_frontiers": stale_frontiers(
                _events(self), query, limit=limit
            ),
        }

    def narrative_explain(self, query: str, *, limit: int = 50) -> dict:
        events = _events(self)
        ranked = archaeology(events, query, limit=max(limit, 80))
        latest = (
            max(
                (item["event"] for item in ranked),
                key=lambda event: (event.timestamp, event.event_id),
            )
            if ranked
            else None
        )
        genealogy = frontier_genealogy(events, query, limit=120)
        current_frontier = []
        for row in reversed(genealogy):
            if row["frontier"]:
                current_frontier = list(row["frontier"])
                break
        return {
            "query": query,
            "authority": "development-narrative",
            "may_establish_formal_fact": False,
            "may_establish_empirical_fact": False,
            "latest_event": latest.as_record() if latest else None,
            "current_frontier": current_frontier,
            "frontier_genealogy": genealogy,
            "potentially_stale_frontiers": stale_frontiers(events, query, limit=120),
        }

    def discover(self, query: str, *, limit: int = 50) -> dict:
        return self.index.discovery_receipt(query, limit=limit)

    def round_lineage(self, prefix: Optional[str] = None) -> dict:
        return self.index.round_lineage(prefix=prefix)

    def proof_route(
        self,
        query: str,
        *,
        target_prover: str = "lean",
        claim_kind: str = "deductive",
        mathematical_status: str = "novel-open",
        statement_status: str = "not-transcribed",
        certification_status: str = "uncertified",
        da51_address: Optional[str] = None,
        source_declaration: Optional[str] = None,
        current_source_hash: Optional[str] = None,
        limit: int = 50,
    ) -> dict:
        return _proof_router(self).route(
            ProofRouteRequest(
                query=query,
                target_prover=target_prover,
                claim_kind=claim_kind,
                mathematical_status=mathematical_status,
                statement_status=statement_status,
                certification_status=certification_status,
                da51_address=da51_address,
                source_declaration=source_declaration,
                current_source_hash=current_source_hash,
            ),
            limit=limit,
        )

    def proof_route_for_obligation(
        self,
        query: str,
        *,
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
    ) -> dict:
        return _external_router(self).route(
            ExternalProofDemand(
                demand_ref=demand_ref,
                external_obligation_ref=external_obligation_ref,
                statement_digest=statement_digest,
                query=query,
                target_prover=target_prover,
                claim_kind=claim_kind,
                mathematical_status=mathematical_status,
                statement_status=statement_status,
                certification_status=certification_status,
                da51_address=da51_address,
                source_declaration=source_declaration,
                current_source_hash=current_source_hash,
            ),
            limit=limit,
        )

    def formal_evidence_for_obligation(
        self,
        *,
        demand_ref: str,
        external_obligation_ref: str,
        statement_digest: str,
    ) -> dict:
        return {
            "demand_ref": demand_ref,
            "external_obligation_ref": external_obligation_ref,
            "statement_digest": statement_digest,
            "evidence": _external_router(self).evidence_for_obligation(
                demand_ref=demand_ref,
                external_obligation_ref=external_obligation_ref,
                statement_digest=statement_digest,
            ),
            "authority": "evidence-only",
            "establishes_proof": False,
        }

    def proof_route_history(
        self,
        *,
        query: Optional[str] = None,
        da51_address: Optional[str] = None,
        limit: int = 50,
    ) -> dict:
        return {
            "routes": _proof_router(self).route_history(
                query=query,
                address=da51_address,
                limit=limit,
            ),
            "authority": "routing-only",
        }

    def da51_resolve(self, address: str) -> dict:
        return _proof_router(self).resolve_da51(address)

    def da51_evidence(self, address: str) -> dict:
        router = _proof_router(self)
        resolved = router.resolve_da51(address)
        return {
            "address": resolved["address"],
            "evidence": resolved["evidence"],
            "authority": "evidence-only",
        }

    def da51_frontier(self, address: str) -> dict:
        return _proof_router(self).frontier_for(address)

    service_cls.refresh_semantic_catalog = refresh_semantic_catalog
    service_cls.symbol_search = symbol_search
    service_cls.related_symbols = related_symbols
    service_cls.object_detail = object_detail
    service_cls.narrative_archaeology = narrative_archaeology
    service_cls.narrative_history = narrative_history
    service_cls.narrative_frontier = narrative_frontier
    service_cls.narrative_stale = narrative_stale
    service_cls.narrative_explain = narrative_explain
    service_cls.discover = discover
    service_cls.round_lineage = round_lineage
    service_cls.proof_route = proof_route
    service_cls.proof_route_for_obligation = proof_route_for_obligation
    service_cls.formal_evidence_for_obligation = formal_evidence_for_obligation
    service_cls.proof_route_history = proof_route_history
    service_cls.da51_resolve = da51_resolve
    service_cls.da51_evidence = da51_evidence
    service_cls.da51_frontier = da51_frontier
    service_cls._semantic_discovery_installed = True
