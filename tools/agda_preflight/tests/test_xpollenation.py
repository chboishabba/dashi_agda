from __future__ import annotations

import sqlite3

import pytest

from agda_preflight.xpollenation import XPollenationStore


DIGEST = "sha256:" + "a" * 64
CID = "bafybeigdyrztxpollinationfixture"


def _neighbourhood() -> dict:
    return {
        "schema": "dashi.xpollenation-neighbourhood/v1",
        "subject": {"namespace": "rhea", "identifier": "RHEA:19897"},
        "edges": [
            {
                "edgeId": "edge:nos2",
                "relation": "catalysed-by",
                "object": {"namespace": "uniprot", "identifier": "P35228"},
                "sourceRef": "Rhea/SABIO crosswalk",
                "sourceRevision": "2026-10-17",
                "acquisitionReceipt": "receipt:nos2",
                "status": "identity-paid",
                "sameObjectClaimed": False,
                "sameObjectVerified": False,
                "contextEquivalent": False,
                "promotionAllowed": False,
            },
            {
                "edgeId": "edge:qid",
                "relation": "candidate-neighbour",
                "object": {"namespace": "wikidata-qid", "identifier": "Q000000"},
                "sourceRef": "Wikidata candidate lookup",
                "sourceRevision": "2026-10-17",
                "acquisitionReceipt": "receipt:qid",
                "status": "discovered",
                "sameObjectClaimed": False,
                "sameObjectVerified": False,
                "contextEquivalent": False,
                "promotionAllowed": False,
            },
        ],
        "authority": "navigation-enrichment-only",
        "establishesProof": False,
        "establishesPayment": False,
    }


def _resolution_receipt() -> dict:
    return {
        "schemaVersion": "artifact-resolution-receipt/v1",
        "logicalContractVersion": "shared-shard-artifact/v1",
        "logicalArtifactRef": "xpollenation:bh4:RHEA-19897@rev-1#neighbourhood",
        "artifactId": "xpollenation:bh4:RHEA-19897",
        "artifactRevision": "rev-1",
        "shardId": "neighbourhood",
        "contentDigest": DIGEST,
        "payloadDigest": DIGEST,
        "payloadSizeBytes": 128,
        "objectRef": {
            "sink": "ipfs",
            "uri": f"ipfs://{CID}",
            "sizeBytes": 128,
            "contentDigest": DIGEST,
        },
        "transport": {
            "sink": "ipfs",
            "uri": f"ipfs://{CID}",
            "cid": CID,
            "metadata": {"gatewayVerified": True},
        },
        "verified": True,
        "authority": "transport-only",
        "establishesProof": False,
    }


def _store() -> XPollenationStore:
    conn = sqlite3.connect(":memory:")
    conn.row_factory = sqlite3.Row
    return XPollenationStore(conn)


def test_ingest_persists_typed_edges_da51_join_and_ipfs_artifact() -> None:
    store = _store()
    result = store.ingest_neighbourhood(
        _neighbourhood(),
        da51_address="0xDA51800100000000",
        artifact_resolution_receipt=_resolution_receipt(),
    )

    assert result["subject"] == {"namespace": "rhea", "identifier": "RHEA:19897"}
    assert result["edge_count"] == 2
    assert result["da51_address"] == "0xDA51800100000000"
    assert result["artifact"]["cid"] == CID
    assert result["authority"] == "navigation-enrichment-only"
    assert result["establishes_proof"] is False
    assert result["establishes_payment"] is False

    fetched = store.neighbourhood("rhea", "RHEA:19897")
    assert fetched is not None
    assert fetched["artifact"]["logical_artifact_ref"] == (
        "xpollenation:bh4:RHEA-19897@rev-1#neighbourhood"
    )
    assert [edge["edge_id"] for edge in fetched["edges"]] == ["edge:nos2", "edge:qid"]


def test_ingest_rejects_promotion_authority() -> None:
    item = _neighbourhood()
    item["edges"][1]["promotionAllowed"] = True
    with pytest.raises(ValueError, match="promotion"):
        _store().ingest_neighbourhood(item)


def test_ingest_rejects_verified_same_object_without_claim() -> None:
    item = _neighbourhood()
    item["edges"][0]["sameObjectVerified"] = True
    with pytest.raises(ValueError, match="same-object"):
        _store().ingest_neighbourhood(item)


def test_ingest_rejects_authority_escalation_at_neighbourhood_level() -> None:
    item = _neighbourhood()
    item["establishesPayment"] = True
    with pytest.raises(ValueError, match="authority"):
        _store().ingest_neighbourhood(item)
