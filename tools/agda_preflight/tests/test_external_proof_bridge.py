from __future__ import annotations

import sqlite3

from agda_preflight.external_proof_bridge import (
    ExternalFormalEvidence,
    ExternalProofDemand,
    ExternalProofRouter,
)
from agda_preflight.proof_router import ProofRouter


def complete_absence(query: str, limit: int = 50):
    return {
        "query": query,
        "live_matches": [],
        "related": {},
        "query_similar": [],
        "historical_matches": [],
        "absence_status": "confirmed_absent",
        "absence_claim_permitted": True,
    }


def exact_match(query: str, limit: int = 50):
    return {
        "query": query,
        "live_matches": [{"qualified_name": "DASHI.Existing.theorem"}],
        "related": {},
        "query_similar": [],
        "historical_matches": [],
        "absence_status": "not_absent",
        "absence_claim_permitted": False,
    }


def demand(digest: str = "sha256:statement-a") -> ExternalProofDemand:
    return ExternalProofDemand(
        demand_ref="formal-demand:smith:1",
        external_obligation_ref="proof-obligation:smith:1",
        statement_digest=digest,
        query="Smith direct-assistance construction formal premise",
        target_prover="lean",
        mathematical_status="source-established",
        statement_status="source-aligned",
        certification_status="uncertified",
        da51_address="0xDA51831100800000",
    )


def test_changed_statement_digest_changes_external_route_identity():
    conn = sqlite3.connect(":memory:")
    conn.row_factory = sqlite3.Row
    bridge = ExternalProofRouter(ProofRouter(discovery=complete_absence, connection=conn), conn)
    first = bridge.route(demand("sha256:a"))
    second = bridge.route(demand("sha256:b"))
    assert first["external_route_id"] != second["external_route_id"]
    assert first["establishes_proof"] is False
    assert second["establishes_proof"] is False


def test_exact_repository_match_suppresses_generation_without_becoming_proof():
    conn = sqlite3.connect(":memory:")
    conn.row_factory = sqlite3.Row
    bridge = ExternalProofRouter(ProofRouter(discovery=exact_match, connection=conn), conn)
    route = bridge.route(demand())
    assert route["recommended_backend"] == "repository-reuse-review"
    assert route["generation_permitted"] is False
    assert route["establishes_proof"] is False


def test_evidence_lookup_is_exact_to_demand_obligation_and_digest():
    conn = sqlite3.connect(":memory:")
    conn.row_factory = sqlite3.Row
    bridge = ExternalProofRouter(ProofRouter(discovery=complete_absence, connection=conn), conn)
    bridge.route(demand())
    bridge.record_evidence(
        ExternalFormalEvidence(
            evidence_ref="formal-evidence:smith:1",
            demand_ref="formal-demand:smith:1",
            external_obligation_ref="proof-obligation:smith:1",
            statement_digest="sha256:statement-a",
            da51_address="0xDA51831100800000",
            producer="lean-kernel",
            artifact_ref="artifact:smith-proof:1",
            artifact_digest="sha256:artifact-a",
            checker="lean",
            checker_revision="lean:head",
            result_kind="formal-proof",
            certification_state="kernel-certified",
        )
    )
    assert len(bridge.evidence_for_obligation(
        demand_ref="formal-demand:smith:1",
        external_obligation_ref="proof-obligation:smith:1",
        statement_digest="sha256:statement-a",
    )) == 1
    assert bridge.evidence_for_obligation(
        demand_ref="formal-demand:smith:1",
        external_obligation_ref="proof-obligation:smith:1",
        statement_digest="sha256:other",
    ) == []
