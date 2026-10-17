from __future__ import annotations

import sqlite3

import pytest

from agda_preflight.external_proof_bridge import (
    ExternalFormalEvidence,
    ExternalProofDemand,
    ExternalProofRouter,
)
from agda_preflight.proof_router import ProofRouter


DIGEST = "a" * 64


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


def demand() -> ExternalProofDemand:
    return ExternalProofDemand(
        demand_ref="formal-demand:mabo:1",
        external_obligation_ref="proof-obligation:mabo:1",
        statement_digest="sha256:statement-a",
        query="Mabo formal premise",
        target_prover="lean",
        mathematical_status="source-established",
        statement_status="source-aligned",
        certification_status="uncertified",
        da51_address="0xDA51831100800000",
    )


def artifact_receipt() -> dict:
    return {
        "schemaVersion": "artifact-resolution-receipt/v1",
        "logicalContractVersion": "shared-shard-artifact/v1",
        "logicalArtifactRef": "mabo-formal-proof@rev-1#proof-1",
        "artifactId": "mabo-formal-proof",
        "artifactRevision": "rev-1",
        "shardId": "proof-1",
        "contentDigest": f"sha256:{DIGEST}",
        "payloadDigest": f"sha256:{DIGEST}",
        "payloadSizeBytes": 12,
        "objectRef": {
            "sink": "ipfs",
            "uri": "ipfs://bafy-demo-erdfa-tar",
            "memberPath": "payload/proof-1.olean",
            "sizeBytes": 12,
            "contentDigest": f"sha256:{DIGEST}",
        },
        "transport": {
            "sink": "ipfs",
            "uri": "ipfs://bafy-demo-erdfa-tar",
            "cid": "bafy-demo-erdfa-tar",
            "memberPath": "payload/proof-1.olean",
        },
        "verified": True,
        "authority": "transport-only",
        "establishesProof": False,
    }


def bridge() -> ExternalProofRouter:
    conn = sqlite3.connect(":memory:")
    conn.row_factory = sqlite3.Row
    result = ExternalProofRouter(ProofRouter(discovery=complete_absence, connection=conn), conn)
    result.route(demand())
    return result


def evidence(*, artifact_digest: str = f"sha256:{DIGEST}") -> ExternalFormalEvidence:
    return ExternalFormalEvidence(
        evidence_ref="formal-evidence:mabo:1",
        demand_ref="formal-demand:mabo:1",
        external_obligation_ref="proof-obligation:mabo:1",
        statement_digest="sha256:statement-a",
        da51_address="0xDA51831100800000",
        producer="lean-kernel",
        artifact_ref="mabo-formal-proof@rev-1#proof-1",
        artifact_digest=artifact_digest,
        checker="lean",
        checker_revision="lean:head",
        result_kind="formal-proof",
        certification_state="kernel-certified",
        artifact_resolution_receipt=artifact_receipt(),
    )


def test_verified_artifact_resolution_is_persisted_with_formal_evidence() -> None:
    router = bridge()
    recorded = router.record_evidence(evidence())

    assert recorded["artifact_resolution"]["verified"] is True
    assert recorded["artifact_resolution"]["sink"] == "ipfs"
    assert recorded["artifact_resolution"]["cid"] == "bafy-demo-erdfa-tar"
    rows = router.evidence_for_obligation(
        demand_ref="formal-demand:mabo:1",
        external_obligation_ref="proof-obligation:mabo:1",
        statement_digest="sha256:statement-a",
    )
    assert rows[0]["artifact_resolution"]["logical_artifact_ref"] == "mabo-formal-proof@rev-1#proof-1"
    assert rows[0]["artifact_resolution"]["authority"] == "transport-only"
    assert rows[0]["artifact_resolution"]["establishes_proof"] is False


def test_formal_evidence_rejects_artifact_digest_that_does_not_match_resolution_receipt() -> None:
    router = bridge()

    with pytest.raises(ValueError, match="artifact digest"):
        router.record_evidence(evidence(artifact_digest=f"sha256:{'b' * 64}"))


def test_formal_evidence_rejects_logical_artifact_ref_mismatch() -> None:
    router = bridge()
    item = evidence()
    bad = ExternalFormalEvidence(**{**item.__dict__, "artifact_ref": "artifact:other"})

    with pytest.raises(ValueError, match="artifact ref"):
        router.record_evidence(bad)
