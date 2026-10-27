from __future__ import annotations

from dataclasses import dataclass
import re
from typing import Any, Mapping, Optional
from urllib.parse import urlparse


ARTIFACT_RESOLUTION_SCHEMA = "artifact-resolution-receipt/v1"
SHARED_SHARD_CONTRACT = "shared-shard-artifact/v1"
_ALLOWED_SINKS = frozenset({"file", "hf", "ipfs"})
_SHA256_RE = re.compile(r"^[0-9a-fA-F]{64}$")


def _require_text(name: str, value: Any) -> str:
    """Return one required non-empty text field."""
    text = str(value or "").strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    return text


def _sha256(name: str, value: Any) -> str:
    """Normalize one strict SHA-256 value to the canonical prefixed form."""
    text = _require_text(name, value)
    body = text.split(":", 1)[1] if text.lower().startswith("sha256:") else text
    if not _SHA256_RE.fullmatch(body):
        raise ValueError(f"{name} must be a sha256 digest")
    return f"sha256:{body.lower()}"


def _cid_from_ipfs_uri(uri: str) -> str:
    """Extract the CID from a required `ipfs://` URI."""
    if not uri.startswith("ipfs://"):
        raise ValueError("IPFS object ref must use ipfs:// URI")
    parsed = urlparse(uri)
    cid = parsed.netloc or parsed.path.lstrip("/").split("/", 1)[0]
    if not cid:
        raise ValueError("IPFS object ref has no CID")
    return cid


@dataclass(frozen=True)
class ArtifactResolutionReceipt:
    """Validated, authority-neutral artifact transport provenance."""

    schema_version: str
    logical_contract_version: str
    logical_artifact_ref: str
    artifact_id: str
    artifact_revision: str
    shard_id: str
    content_digest: str
    payload_digest: str
    payload_size_bytes: int
    sink: str
    uri: str
    cid: Optional[str]
    member_path: Optional[str]
    transport_metadata: dict[str, Any]
    verified: bool
    authority: str
    establishes_proof: bool

    @classmethod
    def from_mapping(cls, item: Mapping[str, Any]) -> "ArtifactResolutionReceipt":
        """Validate and normalize an ITIR `artifact-resolution-receipt/v1`."""
        schema_version = _require_text("schemaVersion", item.get("schemaVersion"))
        if schema_version != ARTIFACT_RESOLUTION_SCHEMA:
            raise ValueError(f"unsupported artifact resolution schema: {schema_version}")
        logical_contract_version = _require_text(
            "logicalContractVersion", item.get("logicalContractVersion")
        )
        if logical_contract_version != SHARED_SHARD_CONTRACT:
            raise ValueError(
                f"unsupported logical artifact contract: {logical_contract_version}"
            )

        artifact_id = _require_text("artifactId", item.get("artifactId"))
        artifact_revision = _require_text(
            "artifactRevision", item.get("artifactRevision")
        )
        shard_id = _require_text("shardId", item.get("shardId"))
        logical_artifact_ref = _require_text(
            "logicalArtifactRef", item.get("logicalArtifactRef")
        )
        expected_ref = f"{artifact_id}@{artifact_revision}#{shard_id}"
        if logical_artifact_ref != expected_ref:
            raise ValueError("logical artifact ref does not match artifact coordinates")

        content_digest = _sha256("contentDigest", item.get("contentDigest"))
        payload_digest = _sha256("payloadDigest", item.get("payloadDigest"))
        if content_digest != payload_digest:
            raise ValueError("artifact resolution digest mismatch")

        payload_size = item.get("payloadSizeBytes")
        if type(payload_size) is not int or payload_size < 0:
            raise ValueError("payloadSizeBytes must be a non-negative integer")

        object_ref = item.get("objectRef") or {}
        transport = item.get("transport") or {}
        sink = _require_text("objectRef.sink", object_ref.get("sink"))
        if sink not in _ALLOWED_SINKS:
            raise ValueError(f"unsupported artifact sink: {sink}")
        uri = _require_text("objectRef.uri", object_ref.get("uri"))
        transport_sink = _require_text("transport.sink", transport.get("sink"))
        transport_uri = _require_text("transport.uri", transport.get("uri"))
        if transport_sink != sink:
            raise ValueError("transport sink does not match object ref")
        if transport_uri != uri:
            raise ValueError("transport URI does not match object ref")

        object_digest = _sha256(
            "objectRef.contentDigest", object_ref.get("contentDigest")
        )
        if object_digest != content_digest:
            raise ValueError("object-ref digest does not match logical artifact digest")
        object_size = object_ref.get("sizeBytes")
        if type(object_size) is not int or object_size < 0:
            raise ValueError("objectRef.sizeBytes must be a non-negative integer")
        if object_size != payload_size:
            raise ValueError("object-ref size does not match payload size")

        cid: Optional[str] = None
        if sink == "ipfs":
            cid = _cid_from_ipfs_uri(uri)
            receipt_cid = _require_text("transport.cid", transport.get("cid"))
            if receipt_cid != cid:
                raise ValueError("artifact resolution IPFS CID mismatch")

        metadata_value = transport.get("metadata") or {}
        if not isinstance(metadata_value, Mapping):
            raise ValueError("transport.metadata must be an object when present")
        transport_metadata = dict(metadata_value)

        verified = item.get("verified") is True
        authority = _require_text("authority", item.get("authority"))
        establishes_proof = item.get("establishesProof") is True
        if not verified:
            raise ValueError("artifact resolution receipt is not verified")
        if authority != "transport-only" or establishes_proof:
            raise ValueError("artifact resolution receipt attempts proof authority escalation")

        member_path_value = transport.get("memberPath") or object_ref.get("memberPath")
        member_path = str(member_path_value) if member_path_value else None
        return cls(
            schema_version=schema_version,
            logical_contract_version=logical_contract_version,
            logical_artifact_ref=logical_artifact_ref,
            artifact_id=artifact_id,
            artifact_revision=artifact_revision,
            shard_id=shard_id,
            content_digest=content_digest,
            payload_digest=payload_digest,
            payload_size_bytes=payload_size,
            sink=sink,
            uri=uri,
            cid=cid,
            member_path=member_path,
            transport_metadata=transport_metadata,
            verified=True,
            authority="transport-only",
            establishes_proof=False,
        )

    def as_record(self) -> dict[str, Any]:
        """Return a normalized record suitable for persistence or display."""
        return {
            "schema_version": self.schema_version,
            "logical_contract_version": self.logical_contract_version,
            "logical_artifact_ref": self.logical_artifact_ref,
            "artifact_id": self.artifact_id,
            "artifact_revision": self.artifact_revision,
            "shard_id": self.shard_id,
            "content_digest": self.content_digest,
            "payload_digest": self.payload_digest,
            "payload_size_bytes": self.payload_size_bytes,
            "sink": self.sink,
            "uri": self.uri,
            "cid": self.cid,
            "member_path": self.member_path,
            "transport_metadata": dict(self.transport_metadata),
            "verified": self.verified,
            "authority": self.authority,
            "establishes_proof": self.establishes_proof,
        }
