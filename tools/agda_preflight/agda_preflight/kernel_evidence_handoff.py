from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from .external_proof_bridge import ExternalFormalEvidence


def _required(name: str, value: Any) -> str:
    text = str(value or "").strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    return text


def validate_kernel_handoff(
    kernel_receipt: dict[str, Any], artifact_receipt: dict[str, Any]
) -> dict[str, Any]:
    if kernel_receipt.get("schemaVersion") != "kernel-certification-receipt/v1":
        raise ValueError("unsupported kernel certification receipt schema")
    if artifact_receipt.get("schemaVersion") != "artifact-resolution-receipt/v1":
        raise ValueError("unsupported artifact-resolution receipt schema")
    if artifact_receipt.get("verified") is not True:
        raise ValueError("artifact resolution must be verified")
    if artifact_receipt.get("authority") != "transport-only" or artifact_receipt.get("establishesProof") is not False:
        raise ValueError("artifact resolution must remain transport-only and non-proof")
    if kernel_receipt.get("authority") != "formal-checker-only":
        raise ValueError("kernel receipt has wrong authority class")
    if kernel_receipt.get("certifiesFormalResult") is not True:
        raise ValueError("kernel receipt does not certify a formal result")
    if kernel_receipt.get("certificationState") != "kernel-certified":
        raise ValueError("kernel receipt is not kernel-certified")
    if kernel_receipt.get("createsLegalAuthority") or kernel_receipt.get("applicabilityPromoted") or kernel_receipt.get("claimTruthPromoted"):
        raise ValueError("kernel receipt crosses a legal/truth promotion boundary")

    artifact_ref = _required("artifactRef", kernel_receipt.get("artifactRef"))
    artifact_digest = _required("artifactDigest", kernel_receipt.get("artifactDigest"))
    if artifact_ref != _required("logicalArtifactRef", artifact_receipt.get("logicalArtifactRef")):
        raise ValueError("kernel/artifact logical artifact ref mismatch")
    if artifact_digest != _required("contentDigest", artifact_receipt.get("contentDigest")):
        raise ValueError("kernel/artifact digest mismatch")

    dependencies = [
        _required("dependency", value)
        for value in list(kernel_receipt.get("dependencies") or [])
    ]
    return {
        "demand_ref": _required("demandRef", kernel_receipt.get("demandRef")),
        "obligation_ref": _required("obligationRef", kernel_receipt.get("obligationRef")),
        "statement_digest": _required("statementDigest", kernel_receipt.get("statementDigest")),
        "da51_address": kernel_receipt.get("da51Address"),
        "producer": _required("producer", kernel_receipt.get("producer")),
        "artifact_ref": artifact_ref,
        "artifact_digest": artifact_digest,
        "checker": _required("checker", kernel_receipt.get("checker")),
        "checker_revision": _required("checkerRevision", kernel_receipt.get("checkerRevision")),
        "source_revision": _required("sourceRevision", kernel_receipt.get("sourceRevision")),
        "result_kind": _required("resultKind", kernel_receipt.get("resultKind")),
        "certification_state": "kernel-certified",
        "dependencies": dependencies,
    }


def stable_evidence_ref(normalized: dict[str, Any]) -> str:
    parts = [
        "dashi-external-formal-evidence:v2",
        normalized["demand_ref"],
        normalized["obligation_ref"],
        normalized["statement_digest"],
        normalized.get("da51_address") or "",
        normalized["producer"],
        normalized["artifact_ref"],
        normalized["artifact_digest"],
        normalized["checker"],
        normalized["checker_revision"],
        normalized["source_revision"],
        normalized["result_kind"],
        normalized["certification_state"],
        *normalized["dependencies"],
    ]
    hasher = hashlib.sha256()
    for part in parts:
        data = part.encode("utf-8")
        hasher.update(len(data).to_bytes(8, "big"))
        hasher.update(data)
    return "formal-evidence:sha256:" + hasher.hexdigest()


def as_external_formal_evidence(
    normalized: dict[str, Any], evidence_ref: str
) -> ExternalFormalEvidence:
    return ExternalFormalEvidence(
        evidence_ref=_required("evidence_ref", evidence_ref),
        demand_ref=normalized["demand_ref"],
        external_obligation_ref=normalized["obligation_ref"],
        statement_digest=normalized["statement_digest"],
        da51_address=normalized.get("da51_address"),
        producer=normalized["producer"],
        artifact_ref=normalized["artifact_ref"],
        artifact_digest=normalized["artifact_digest"],
        checker=normalized["checker"],
        checker_revision=normalized["checker_revision"],
        result_kind=normalized["result_kind"],
        certification_state=normalized["certification_state"],
    )


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))
