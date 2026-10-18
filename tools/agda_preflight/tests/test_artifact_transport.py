from __future__ import annotations

import pytest

from agda_preflight.artifact_transport import ArtifactResolutionReceipt


DIGEST = "a" * 64


def receipt() -> dict:
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


def test_artifact_resolution_receipt_preserves_logical_identity_without_proof_authority() -> None:
    parsed = ArtifactResolutionReceipt.from_mapping(receipt())

    assert parsed.logical_artifact_ref == "mabo-formal-proof@rev-1#proof-1"
    assert parsed.sink == "ipfs"
    assert parsed.uri == "ipfs://bafy-demo-erdfa-tar"
    assert parsed.cid == "bafy-demo-erdfa-tar"
    assert parsed.content_digest == f"sha256:{DIGEST}"
    assert parsed.verified is True
    assert parsed.authority == "transport-only"
    assert parsed.establishes_proof is False


def test_artifact_resolution_receipt_rejects_digest_mismatch() -> None:
    item = receipt()
    item["payloadDigest"] = f"sha256:{'b' * 64}"

    with pytest.raises(ValueError, match="digest"):
        ArtifactResolutionReceipt.from_mapping(item)


def test_artifact_resolution_receipt_rejects_authority_escalation() -> None:
    item = receipt()
    item["establishesProof"] = True

    with pytest.raises(ValueError, match="proof authority"):
        ArtifactResolutionReceipt.from_mapping(item)


def test_artifact_resolution_receipt_rejects_boolean_payload_size() -> None:
    item = receipt()
    item["payloadSizeBytes"] = True
    item["objectRef"]["sizeBytes"] = True

    with pytest.raises(ValueError, match="payloadSizeBytes"):
        ArtifactResolutionReceipt.from_mapping(item)


def test_artifact_resolution_receipt_requires_object_ref_digest() -> None:
    item = receipt()
    del item["objectRef"]["contentDigest"]

    with pytest.raises(ValueError, match="objectRef.contentDigest"):
        ArtifactResolutionReceipt.from_mapping(item)
