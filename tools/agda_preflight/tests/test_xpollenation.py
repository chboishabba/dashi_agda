from __future__ import annotations

import copy
import sqlite3

import pytest

from agda_preflight.xpollenation import XPollenationStore


DIGEST = "sha256:" + "a" * 64
CID = "bafybeigdyrztxpollinationfixture"


def _neighbourhood(reaction: str = "RHEA:19897") -> dict:
    return {
        "schema": "dashi.xpollenation-neighbourhood/v1",
        "subject": {"namespace": "rhea", "identifier": reaction},
        "edges": [
            {
                "edgeId": f"edge:catalyst:{reaction}",
                "subject": {"namespace": "rhea", "identifier": reaction},
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
                "subject": {"namespace": "uniprot", "identifier": "P35228"},
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


def _resolution_receipt(revision: str = "rev-1", digest: str = DIGEST, cid: str = CID) -> dict:
    return {
        "schemaVersion": "artifact-resolution-receipt/v1",
        "logicalContractVersion": "shared-shard-artifact/v1",
        "logicalArtifactRef": f"xpollenation:bh4:RHEA-19897@{revision}#neighbourhood",
        "artifactId": "xpollenation:bh4:RHEA-19897",
        "artifactRevision": revision,
        "shardId": "neighbourhood",
        "contentDigest": digest,
        "payloadDigest": digest,
        "payloadSizeBytes": 128,
        "objectRef": {
            "sink": "ipfs",
            "uri": f"ipfs://{cid}",
            "sizeBytes": 128,
            "contentDigest": digest,
        },
        "transport": {
            "sink": "ipfs",
            "uri": f"ipfs://{cid}",
            "cid": cid,
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
    assert [edge["edge_id"] for edge in fetched["edges"]] == [
        "edge:catalyst:RHEA:19897",
        "edge:qid",
    ]
    assert fetched["edges"][1]["subject_namespace"] == "uniprot"
    assert fetched["edges"][1]["subject_identifier"] == "P35228"


def test_one_global_edge_can_belong_to_multiple_neighbourhoods() -> None:
    store = _store()
    store.ingest_neighbourhood(_neighbourhood("RHEA:19897"))
    store.ingest_neighbourhood(_neighbourhood("RHEA:17473"))

    first = store.neighbourhood("rhea", "RHEA:19897")
    second = store.neighbourhood("rhea", "RHEA:17473")
    assert first is not None and second is not None
    assert "edge:qid" in {edge["edge_id"] for edge in first["edges"]}
    assert "edge:qid" in {edge["edge_id"] for edge in second["edges"]}


def test_new_artifact_revision_is_retained_and_becomes_current() -> None:
    store = _store()
    store.ingest_neighbourhood(_neighbourhood(), artifact_resolution_receipt=_resolution_receipt())
    digest2 = "sha256:" + "b" * 64
    cid2 = "bafybeinewrevision"
    store.ingest_neighbourhood(
        _neighbourhood(),
        artifact_resolution_receipt=_resolution_receipt("rev-2", digest2, cid2),
    )
    fetched = store.neighbourhood("rhea", "RHEA:19897")
    assert fetched is not None
    assert fetched["artifact"]["artifact_revision"] == "rev-2"
    assert fetched["artifact"]["cid"] == cid2
    assert len(store.artifact_history("rhea", "RHEA:19897")) == 2


def test_reingest_replaces_current_neighbourhood_membership_not_global_edge_history() -> None:
    store = _store()
    store.ingest_neighbourhood(_neighbourhood())
    updated = copy.deepcopy(_neighbourhood())
    updated["edges"] = [updated["edges"][0]]
    store.ingest_neighbourhood(updated)
    fetched = store.neighbourhood("rhea", "RHEA:19897")
    assert fetched is not None
    assert [edge["edge_id"] for edge in fetched["edges"]] == ["edge:catalyst:RHEA:19897"]


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
