from __future__ import annotations

from agda_preflight.kernel_evidence_handoff import validate_kernel_handoff


def _artifact() -> dict:
    digest = "sha256:" + "22" * 32
    return {
        "schemaVersion": "artifact-resolution-receipt/v1",
        "logicalArtifactRef": "formal-proof:demo@rev#formal-proof-source",
        "contentDigest": digest,
        "verified": True,
        "authority": "transport-only",
        "establishesProof": False,
    }


def _kernel() -> dict:
    return {
        "schemaVersion": "kernel-certification-receipt/v1",
        "demandRef": "formal-demand:mabo:1",
        "obligationRef": "legal-obligation:mabo:1",
        "statementDigest": "sha256:" + "11" * 32,
        "da51Address": "0xDA51831100800000",
        "producer": "agda-kernel",
        "artifactRef": _artifact()["logicalArtifactRef"],
        "artifactDigest": _artifact()["contentDigest"],
        "checker": "agda",
        "checkerRevision": "Agda version 2.8.0",
        "sourceRevision": "git:abc123",
        "resultKind": "formal-proof",
        "certificationState": "kernel-certified",
        "dependencies": ["DASHI.Law.MaboRevisionReopenExact"],
        "authority": "formal-checker-only",
        "certifiesFormalResult": True,
        "createsLegalAuthority": False,
        "applicabilityPromoted": False,
        "claimTruthPromoted": False,
    }


def test_valid_handoff_preserves_exact_coordinates() -> None:
    normalized = validate_kernel_handoff(_kernel(), _artifact())
    assert normalized["artifact_ref"] == _artifact()["logicalArtifactRef"]
    assert normalized["artifact_digest"] == _artifact()["contentDigest"]
    assert normalized["source_revision"] == "git:abc123"
    assert normalized["dependencies"] == ["DASHI.Law.MaboRevisionReopenExact"]


def test_artifact_digest_mismatch_fails_closed() -> None:
    kernel = _kernel()
    kernel["artifactDigest"] = "sha256:" + "99" * 32
    try:
        validate_kernel_handoff(kernel, _artifact())
    except ValueError as error:
        assert "artifact digest" in str(error)
    else:
        raise AssertionError("mismatched kernel/artifact digest must fail closed")
