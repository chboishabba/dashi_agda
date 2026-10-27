from __future__ import annotations

from agda_preflight.artifact_transport import ArtifactResolutionReceipt


DIGEST = "a" * 64


def test_artifact_resolution_preserves_gateway_metadata_as_transport_provenance() -> None:
    item = {
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
    }

    receipt = ArtifactResolutionReceipt.from_mapping(item)
    record = receipt.as_record()

    assert record["transport_metadata"]["statusCode"] == 200
    assert record["transport_metadata"]["gatewayUrl"].startswith("http://127.0.0.1")
    assert record["authority"] == "transport-only"
    assert record["establishes_proof"] is False
