from __future__ import annotations

import sqlite3

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


def test_artifact_transport_metadata_survives_evidence_round_trip() -> None:
    conn = sqlite3.connect(":memory:")
    conn.row_factory = sqlite3.Row
    bridge = ExternalProofRouter(ProofRouter(discovery=complete_absence, connection=conn), conn)
    bridge.route(
        ExternalProofDemand(
            demand_ref="formal-demand:mabo:metadata",
            external_obligation_ref="proof-obligation:mabo:metadata",
            statement_digest="sha256:statement-metadata",
            query="Mabo formal premise metadata",
            mathematical_status="source-established",
            statement_status="source-aligned",
            da51_address="0xDA51831100800000",
        )
    )
    bridge.record_evidence(
        ExternalFormalEvidence(
            evidence_ref="formal-evidence:mabo:metadata",
            demand_ref="formal-demand:mabo:metadata",
            external_obligation_ref="proof-obligation:mabo:metadata",
            statement_digest="sha256:statement-metadata",
            da51_address="0xDA51831100800000",
            producer="lean-kernel",
            artifact_ref="mabo@rev#proof",
            artifact_digest=f"sha256:{DIGEST}",
            checker="lean",
            checker_revision="lean:head",
            result_kind="formal-proof",
            certification_state="kernel-certified",
            artifact_resolution_receipt={
                "schemaVersion": "artifact-resolution-receipt/v1",
                "logicalContractVersion": "shared-shard-artifact/v1",
                "logicalArtifactRef": "mabo@rev#proof",
                "artifactId": "mabo",
                "artifactRevision": "rev",
                "shardId": "proof",
                "contentDigest": f"sha256:{DIGEST}",
                "payloadDigest": f"sha256:{DIGEST}",
                "payloadSizeBytes": 12,
                "objectRef": {
                    "sink": "ipfs",
                    "uri": "ipfs://bafy-demo",
                    "sizeBytes": 12,
                    "contentDigest": f"sha256:{DIGEST}",
                },
                "transport": {
                    "sink": "ipfs",
                    "uri": "ipfs://bafy-demo",
                    "cid": "bafy-demo",
                    "metadata": {
                        "gatewayUrl": "http://127.0.0.1:8080/ipfs/bafy-demo",
                        "statusCode": 200,
                        "finalUrl": "http://127.0.0.1:8080/ipfs/bafy-demo",
                        "sha256": "b" * 64,
                    },
                },
                "verified": True,
                "authority": "transport-only",
                "establishesProof": False,
            },
        )
    )

    rows = bridge.evidence_for_obligation(
        demand_ref="formal-demand:mabo:metadata",
        external_obligation_ref="proof-obligation:mabo:metadata",
        statement_digest="sha256:statement-metadata",
    )

    metadata = rows[0]["artifact_resolution"]["transport_metadata"]
    assert metadata["statusCode"] == 200
    assert metadata["gatewayUrl"] == "http://127.0.0.1:8080/ipfs/bafy-demo"
    assert metadata["sha256"] == "b" * 64
