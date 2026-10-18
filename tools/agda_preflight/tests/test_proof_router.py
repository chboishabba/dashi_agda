import sqlite3
from pathlib import Path

import pytest

from agda_preflight.proof_router import (
    ProofRouteRequest,
    ProofRouter,
    parse_da51,
)
from agda_preflight.repository_store import ensure_repository_schema


class DiscoveryStub:
    def __init__(self, receipt):
        self.receipt = receipt

    def __call__(self, query, *, limit=50):
        return dict(self.receipt, query=query)


class CapabilityStub:
    def __init__(self, mapping_mode=None):
        self.mapping_mode = mapping_mode

    def declaration_capability(self, declaration, *, current_source_hash=None):
        if self.mapping_mode is None:
            return None
        return {
            "declaration_name": declaration,
            "module_name": "DASHI.Example",
            "mapping_mode": self.mapping_mode,
            "freshness": "fresh",
            "object_hash": "abc",
            "checked_source_sha256": "a" * 64,
            "current_source_sha256": current_source_hash,
        }


def _absence(*, permitted=True):
    return {
        "live_matches": [],
        "historical_matches": [],
        "query_similar": [],
        "related": {
            "signature_equivalent": [],
            "body_equivalent": [],
            "similar": [],
        },
        "absence_claim_permitted": permitted,
        "absence_status": (
            "confirmed_no_indexed_candidate" if permitted else "search_incomplete"
        ),
    }


def _router(receipt=None, capability=None, conn=None):
    return ProofRouter(
        discovery=DiscoveryStub(receipt or _absence()),
        semantic_catalog=capability,
        connection=conn,
    )


def _connection(tmp_path: Path):
    conn = sqlite3.connect(tmp_path / "repository.sqlite3")
    conn.row_factory = sqlite3.Row
    ensure_repository_schema(conn)
    return conn


def test_da51_atlas_parse_is_wire_metadata_not_authority():
    parsed = parse_da51("0xDA51853000A00000")
    assert parsed["address"] == "0xDA51853000A00000"
    assert parsed["type_code"] == 8
    assert parsed["atlas"] == {
        "level": 5,
        "biome": 3,
        "status": 0,
        "serial": 10,
        "reserved": 0,
    }
    assert parsed["authority"] == "identity-only"


def test_da51_atlas_reserved_bits_fail_closed():
    with pytest.raises(ValueError, match="reserved"):
        parse_da51("0xDA51800100000001")


def test_incomplete_discovery_blocks_generation():
    route = _router(_absence(permitted=False)).route(
        ProofRouteRequest(query="missing theorem", target_prover="lean")
    )
    assert route["recommended_backend"] == "repository-discovery"
    assert route["generation_permitted"] is False


def test_existing_candidate_routes_to_reuse_review():
    receipt = _absence()
    receipt["absence_claim_permitted"] = False
    receipt["absence_status"] = "candidate_or_partial_object_exists"
    receipt["live_matches"] = [{"qualified_name": "DASHI.Foo.existing"}]
    route = _router(receipt).route(
        ProofRouteRequest(query="existing", target_prover="lean")
    )
    assert route["recommended_backend"] == "repository-reuse-review"
    assert route["generation_permitted"] is False


def test_novel_deductive_absence_routes_aristotle_lean():
    route = _router().route(
        ProofRouteRequest(
            query="new theorem",
            target_prover="lean",
            claim_kind="deductive",
            mathematical_status="novel-open",
        )
    )
    assert route["debt_kind"] == "mathematical-debt"
    assert route["recommended_backend"] == "aristotle+lean"
    assert route["generation_permitted"] is True


def test_source_established_aligned_exact_agda2lean_routes_translation():
    route = _router(capability=CapabilityStub("Exact")).route(
        ProofRouteRequest(
            query="source theorem",
            target_prover="lean",
            claim_kind="deductive",
            mathematical_status="source-established",
            statement_status="source-aligned",
            certification_status="proof-deferred",
            source_declaration="DASHI.Example.sourceTheorem",
        )
    )
    assert route["debt_kind"] == "certification-debt"
    assert route["agda2lean_mapping_mode"] == "Exact"
    assert route["recommended_backend"] == "agda2lean"


def test_reconstruct_mapping_routes_agda2lean_then_aristotle():
    route = _router(capability=CapabilityStub("Reconstruct")).route(
        ProofRouteRequest(
            query="source theorem",
            target_prover="lean",
            mathematical_status="source-established",
            statement_status="source-aligned",
            certification_status="proof-deferred",
            source_declaration="DASHI.Example.sourceTheorem",
        )
    )
    assert route["recommended_backend"] == "agda2lean+aristotle-lean"


def test_unsupported_mapping_never_promotes_translation_to_proof_authority():
    route = _router(capability=CapabilityStub("Unsupported")).route(
        ProofRouteRequest(
            query="source theorem",
            target_prover="lean",
            mathematical_status="source-established",
            statement_status="source-aligned",
            certification_status="proof-deferred",
            source_declaration="DASHI.Example.sourceTheorem",
        )
    )
    assert route["recommended_backend"] == "aristotle-lean"
    assert route["authority"] == "routing-only"
    assert route["translation_establishes_proof"] is False


def test_da51_status_one_does_not_change_debt_or_backend():
    route = _router().route(
        ProofRouteRequest(
            query="status-one theorem",
            target_prover="lean",
            mathematical_status="novel-open",
            da51_address="0xDA51800100000000",
        )
    )
    assert route["da51"]["atlas"]["status"] == 1
    assert route["debt_kind"] == "mathematical-debt"
    assert route["recommended_backend"] == "aristotle+lean"
    assert route["authority"] == "routing-only"


def test_route_receipt_is_persisted_relationally(tmp_path: Path):
    conn = _connection(tmp_path)
    route = _router(conn=conn).route(
        ProofRouteRequest(query="new theorem", target_prover="lean")
    )

    stored = conn.execute(
        "SELECT query, debt_kind, recommended_backend, authority FROM proof_routes WHERE route_id=?",
        (route["route_id"],),
    ).fetchone()
    assert tuple(stored) == (
        "new theorem",
        "mathematical-debt",
        "aristotle+lean",
        "routing-only",
    )
    columns = [row[1] for row in conn.execute("PRAGMA table_info(proof_routes)")]
    assert not any("json" in column.lower() for column in columns)
    conn.close()


def test_da51_links_and_evidence_remain_authority_neutral(tmp_path: Path):
    conn = _connection(tmp_path)
    router = _router(conn=conn)
    router.link_da51(
        "0xDA51853000A00000",
        "DASHI.Example.sourceTheorem",
        relation="statement",
        source="dashi_agda",
    )
    evidence = router.add_evidence(
        "0xDA51853000A00000",
        producer="zkperf",
        artifact="sha256:abc",
        evidence_kind="benchmark",
        revision="r1",
        digest="abc",
    )
    resolved = router.resolve_da51("0xDA51853000A00000")

    assert evidence["authority"] == "evidence-only"
    assert resolved["authority"] == "identity-only"
    assert resolved["symbol_links"] == [
        {
            "symbol_id": "DASHI.Example.sourceTheorem",
            "relation": "statement",
            "source": "dashi_agda",
        }
    ]
    assert resolved["evidence"][0]["producer"] == "zkperf"
    assert resolved["evidence"][0]["authority"] == "evidence-only"
    conn.close()


def test_da51_frontier_contains_only_attached_routing_receipts(tmp_path: Path):
    conn = _connection(tmp_path)
    router = _router(conn=conn)
    route = router.route(
        ProofRouteRequest(
            query="atlas-linked goal",
            target_prover="lean",
            da51_address="0xDA51853000A00000",
        )
    )
    frontier = router.frontier_for("0xDA51853000A00000")

    assert frontier["authority"] == "routing-only"
    assert [item["route_id"] for item in frontier["routes"]] == [route["route_id"]]
    assert frontier["routes"][0]["recommended_backend"] == "aristotle+lean"
    conn.close()
