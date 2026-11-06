from __future__ import annotations

from dataclasses import dataclass
import base64
import hashlib
import json
from typing import Any, Mapping


SCHEMA_VERSION = "ao-fleet-pnf-logical-shard/v1"
LANE = "ao.fleet.dynamic.048de098571f"
ORCHESTRATOR_ID = "ao-fleet-conductor-leaf-048de098571f"
MACROSCOPIC_EIGEN_MOTIF = (
    "actor:parsed:NominalSubject · "
    "temporal:now:TemporalModifier · "
    "patient:collapse:DirectObject"
)

NO_TYPED_MEET = "noTypedMeet"
SAME_SHARD = "sameShard"


@dataclass(frozen=True)
class LogicalShardRef:
    shard_id: str
    uri: str


def _canonical_json_bytes(value: Mapping[str, Any]) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def _cid_v1_raw_sha256(payload: bytes) -> str:
    digest = hashlib.sha256(payload).digest()
    cid_bytes = bytes((0x01, 0x55, 0x12, 0x20)) + digest
    return "b" + base64.b32encode(cid_bytes).decode("ascii").lower().rstrip("=")


def deterministic_ipfs_ref(shard_id: str, payload: Mapping[str, Any]) -> LogicalShardRef:
    shard = str(shard_id).strip()
    if not shard:
        raise ValueError("shard_id must be non-empty")

    envelope = {
        "schemaVersion": SCHEMA_VERSION,
        "lane": LANE,
        "orchestratorId": ORCHESTRATOR_ID,
        "shardId": shard,
        "payload": dict(payload),
    }
    cid = _cid_v1_raw_sha256(_canonical_json_bytes(envelope))
    return LogicalShardRef(shard_id=shard, uri=f"ipfs://{cid}")


def emit_logical_shard_refs(
    shards: Mapping[str, Mapping[str, Any]],
) -> tuple[LogicalShardRef, ...]:
    return tuple(
        deterministic_ipfs_ref(shard_id, shards[shard_id])
        for shard_id in sorted(shards)
    )


def pairwise_typed_relation(left_shard_id: str, right_shard_id: str) -> str:
    if left_shard_id == right_shard_id:
        return SAME_SHARD
    return NO_TYPED_MEET


def canonical_leaf_shards() -> dict[str, dict[str, str]]:
    return {
        "actor": {
            "slot": "actor",
            "value": "parsed",
            "role": "NominalSubject",
        },
        "temporal": {
            "slot": "temporal",
            "value": "now",
            "role": "TemporalModifier",
        },
        "patient": {
            "slot": "patient",
            "value": "collapse",
            "role": "DirectObject",
        },
        "macroscopic-eigen-motif": {
            "motif": MACROSCOPIC_EIGEN_MOTIF,
        },
    }


def canonical_leaf_refs() -> tuple[LogicalShardRef, ...]:
    return emit_logical_shard_refs(canonical_leaf_shards())


def canonical_leaf_ref_map() -> dict[str, str]:
    return {item.shard_id: item.uri for item in canonical_leaf_refs()}
