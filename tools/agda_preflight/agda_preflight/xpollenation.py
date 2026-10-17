from __future__ import annotations

from dataclasses import dataclass
import sqlite3
import time
from typing import Any, Mapping, Optional

from .artifact_transport import ArtifactResolutionReceipt
from .proof_router import parse_da51


XPOLLENATION_SCHEMA = "dashi.xpollenation-neighbourhood/v1"
XPOLLENATION_DB_SCHEMA = "1"
XPOLLENATION_AUTHORITY = "navigation-enrichment-only"

_ALLOWED_RELATIONS = frozenset(
    {
        "exact-same-object",
        "curated-cross-reference",
        "reaction-participant",
        "catalysed-by",
        "protein-structure-of",
        "kinetic-parameter-for",
        "measured-in-assay",
        "described-by-publication",
        "candidate-neighbour",
        "numerical-coincidence",
        "ontology-parent",
        "possible-same-object",
        "wrong-type",
        "negative-control",
    }
)
_ALLOWED_STATUSES = frozenset(
    {"discovered", "identity-paid", "context-paid", "payment-eligible"}
)
_SAME_OBJECT_RELATIONS = frozenset({"exact-same-object", "curated-cross-reference"})


def _text(name: str, value: Any) -> str:
    text = str(value or "").strip()
    if not text:
        raise ValueError(f"{name} must be non-empty")
    return text


def _coordinate(name: str, value: Any) -> tuple[str, str]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{name} must be an object")
    namespace = _text(f"{name}.namespace", value.get("namespace")).lower()
    identifier = _text(f"{name}.identifier", value.get("identifier"))
    return namespace, identifier


@dataclass(frozen=True)
class NormalizedEdge:
    edge_id: str
    subject_namespace: str
    subject_identifier: str
    relation: str
    object_namespace: str
    object_identifier: str
    source_ref: str
    source_revision: str
    acquisition_receipt: str
    status: str
    same_object_claimed: bool
    same_object_verified: bool
    context_equivalent: bool


def _normalize_edge(item: Any) -> NormalizedEdge:
    if not isinstance(item, Mapping):
        raise ValueError("xPollenation edge must be an object")
    edge_id = _text("edgeId", item.get("edgeId"))
    subject_namespace, subject_identifier = _coordinate("edge.subject", item.get("subject"))
    object_namespace, object_identifier = _coordinate("edge.object", item.get("object"))
    relation = _text("edge.relation", item.get("relation"))
    if relation not in _ALLOWED_RELATIONS:
        raise ValueError(f"unsupported xPollenation relation: {relation}")
    status = _text("edge.status", item.get("status"))
    if status not in _ALLOWED_STATUSES:
        raise ValueError(f"unsupported xPollenation status: {status}")
    if item.get("promotionAllowed") is not False:
        raise ValueError("xPollenation edge attempts promotion authority")
    same_object_claimed = item.get("sameObjectClaimed") is True
    same_object_verified = item.get("sameObjectVerified") is True
    if same_object_verified and not same_object_claimed:
        raise ValueError("same-object verification requires a same-object claim")
    if same_object_verified and relation not in _SAME_OBJECT_RELATIONS:
        raise ValueError("same-object verification requires an identity relation")
    return NormalizedEdge(
        edge_id=edge_id,
        subject_namespace=subject_namespace,
        subject_identifier=subject_identifier,
        relation=relation,
        object_namespace=object_namespace,
        object_identifier=object_identifier,
        source_ref=_text("edge.sourceRef", item.get("sourceRef")),
        source_revision=_text("edge.sourceRevision", item.get("sourceRevision")),
        acquisition_receipt=_text(
            "edge.acquisitionReceipt", item.get("acquisitionReceipt")
        ),
        status=status,
        same_object_claimed=same_object_claimed,
        same_object_verified=same_object_verified,
        context_equivalent=item.get("contextEquivalent") is True,
    )


def normalize_neighbourhood(item: Mapping[str, Any]) -> dict[str, Any]:
    schema = _text("schema", item.get("schema"))
    if schema != XPOLLENATION_SCHEMA:
        raise ValueError(f"unsupported xPollenation schema: {schema}")
    authority = _text("authority", item.get("authority"))
    if (
        authority != XPOLLENATION_AUTHORITY
        or item.get("establishesProof") is not False
        or item.get("establishesPayment") is not False
    ):
        raise ValueError("xPollenation neighbourhood attempts authority escalation")
    namespace, identifier = _coordinate("subject", item.get("subject"))
    edges_value = item.get("edges")
    if not isinstance(edges_value, list):
        raise ValueError("edges must be a list")
    edges = [_normalize_edge(edge) for edge in edges_value]
    edge_ids = [edge.edge_id for edge in edges]
    if len(edge_ids) != len(set(edge_ids)):
        raise ValueError("duplicate xPollenation edge id")
    return {
        "schema": schema,
        "subject": {"namespace": namespace, "identifier": identifier},
        "edges": sorted(edges, key=lambda edge: edge.edge_id),
        "authority": XPOLLENATION_AUTHORITY,
        "establishes_proof": False,
        "establishes_payment": False,
    }


def ensure_xpollenation_schema(conn: sqlite3.Connection) -> None:
    conn.execute("PRAGMA foreign_keys=ON")
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS xpollenation_nodes (
            namespace TEXT NOT NULL,
            identifier TEXT NOT NULL,
            authority TEXT NOT NULL DEFAULT 'external-identity-only'
                CHECK (authority = 'external-identity-only'),
            PRIMARY KEY(namespace, identifier)
        ) WITHOUT ROWID;

        CREATE TABLE IF NOT EXISTS xpollenation_neighbourhoods (
            namespace TEXT NOT NULL,
            identifier TEXT NOT NULL,
            da51_address TEXT,
            authority TEXT NOT NULL DEFAULT 'navigation-enrichment-only'
                CHECK (authority = 'navigation-enrichment-only'),
            establishes_proof INTEGER NOT NULL DEFAULT 0 CHECK (establishes_proof = 0),
            establishes_payment INTEGER NOT NULL DEFAULT 0 CHECK (establishes_payment = 0),
            created_at INTEGER NOT NULL,
            PRIMARY KEY(namespace, identifier),
            FOREIGN KEY(namespace, identifier)
                REFERENCES xpollenation_nodes(namespace, identifier)
        ) WITHOUT ROWID;
        CREATE INDEX IF NOT EXISTS xpollenation_neighbourhoods_da51
            ON xpollenation_neighbourhoods(da51_address);

        CREATE TABLE IF NOT EXISTS xpollenation_edges (
            edge_id TEXT PRIMARY KEY,
            focus_namespace TEXT NOT NULL,
            focus_identifier TEXT NOT NULL,
            subject_namespace TEXT NOT NULL,
            subject_identifier TEXT NOT NULL,
            relation_kind TEXT NOT NULL,
            object_namespace TEXT NOT NULL,
            object_identifier TEXT NOT NULL,
            source_ref TEXT NOT NULL,
            source_revision TEXT NOT NULL,
            acquisition_receipt TEXT NOT NULL,
            status TEXT NOT NULL,
            same_object_claimed INTEGER NOT NULL,
            same_object_verified INTEGER NOT NULL,
            context_equivalent INTEGER NOT NULL,
            promotion_allowed INTEGER NOT NULL DEFAULT 0 CHECK (promotion_allowed = 0),
            authority TEXT NOT NULL DEFAULT 'navigation-enrichment-only'
                CHECK (authority = 'navigation-enrichment-only'),
            establishes_proof INTEGER NOT NULL DEFAULT 0 CHECK (establishes_proof = 0),
            establishes_payment INTEGER NOT NULL DEFAULT 0 CHECK (establishes_payment = 0),
            created_at INTEGER NOT NULL,
            FOREIGN KEY(focus_namespace, focus_identifier)
                REFERENCES xpollenation_neighbourhoods(namespace, identifier) ON DELETE CASCADE,
            FOREIGN KEY(subject_namespace, subject_identifier)
                REFERENCES xpollenation_nodes(namespace, identifier),
            FOREIGN KEY(object_namespace, object_identifier)
                REFERENCES xpollenation_nodes(namespace, identifier)
        );
        CREATE INDEX IF NOT EXISTS xpollenation_edges_subject
            ON xpollenation_edges(subject_namespace, subject_identifier, relation_kind);
        CREATE INDEX IF NOT EXISTS xpollenation_edges_object
            ON xpollenation_edges(object_namespace, object_identifier, relation_kind);
        CREATE INDEX IF NOT EXISTS xpollenation_edges_focus
            ON xpollenation_edges(focus_namespace, focus_identifier);

        CREATE TABLE IF NOT EXISTS xpollenation_artifacts (
            namespace TEXT NOT NULL,
            identifier TEXT NOT NULL,
            schema_version TEXT NOT NULL,
            logical_contract_version TEXT NOT NULL,
            logical_artifact_ref TEXT NOT NULL,
            artifact_id TEXT NOT NULL,
            artifact_revision TEXT NOT NULL,
            shard_id TEXT NOT NULL,
            sink TEXT NOT NULL,
            uri TEXT NOT NULL,
            cid TEXT,
            member_path TEXT,
            content_digest TEXT NOT NULL,
            payload_digest TEXT NOT NULL,
            payload_size_bytes INTEGER NOT NULL,
            verified INTEGER NOT NULL CHECK (verified = 1),
            authority TEXT NOT NULL CHECK (authority = 'transport-only'),
            establishes_proof INTEGER NOT NULL CHECK (establishes_proof = 0),
            created_at INTEGER NOT NULL,
            PRIMARY KEY(namespace, identifier),
            FOREIGN KEY(namespace, identifier)
                REFERENCES xpollenation_neighbourhoods(namespace, identifier) ON DELETE CASCADE
        ) WITHOUT ROWID;
        CREATE UNIQUE INDEX IF NOT EXISTS xpollenation_artifacts_logical_ref
            ON xpollenation_artifacts(logical_artifact_ref);
        CREATE INDEX IF NOT EXISTS xpollenation_artifacts_cid
            ON xpollenation_artifacts(cid);
        """
    )
    try:
        conn.execute(
            "INSERT INTO repository_meta(key, value) VALUES('xpollenation_schema', ?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (XPOLLENATION_DB_SCHEMA,),
        )
    except sqlite3.OperationalError:
        pass
    conn.commit()


class XPollenationStore:
    """Persist authority-neutral cross-domain neighbourhoods and artifact joins."""

    def __init__(self, connection: sqlite3.Connection) -> None:
        self.connection = connection
        if self.connection.row_factory is None:
            self.connection.row_factory = sqlite3.Row
        ensure_xpollenation_schema(connection)

    def _node(self, namespace: str, identifier: str) -> None:
        self.connection.execute(
            "INSERT OR IGNORE INTO xpollenation_nodes(namespace, identifier) VALUES(?, ?)",
            (namespace, identifier),
        )

    def _persist_artifact(
        self,
        namespace: str,
        identifier: str,
        receipt: ArtifactResolutionReceipt,
    ) -> None:
        record = receipt.as_record()
        existing = self.connection.execute(
            "SELECT * FROM xpollenation_artifacts WHERE namespace=? AND identifier=?",
            (namespace, identifier),
        ).fetchone()
        immutable = {
            "schema_version": record["schema_version"],
            "logical_contract_version": record["logical_contract_version"],
            "logical_artifact_ref": record["logical_artifact_ref"],
            "artifact_id": record["artifact_id"],
            "artifact_revision": record["artifact_revision"],
            "shard_id": record["shard_id"],
            "sink": record["sink"],
            "uri": record["uri"],
            "cid": record["cid"],
            "member_path": record["member_path"],
            "content_digest": record["content_digest"],
            "payload_digest": record["payload_digest"],
            "payload_size_bytes": record["payload_size_bytes"],
            "verified": 1,
            "authority": "transport-only",
            "establishes_proof": 0,
        }
        if existing is not None:
            current = dict(existing)
            if any(current.get(key) != value for key, value in immutable.items()):
                raise ValueError("xPollenation artifact conflicts with persisted neighbourhood")
            return
        self.connection.execute(
            """
            INSERT INTO xpollenation_artifacts(
                namespace, identifier, schema_version, logical_contract_version,
                logical_artifact_ref, artifact_id, artifact_revision, shard_id,
                sink, uri, cid, member_path, content_digest, payload_digest,
                payload_size_bytes, verified, authority, establishes_proof, created_at
            ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, 'transport-only', 0, ?)
            """,
            (
                namespace,
                identifier,
                record["schema_version"],
                record["logical_contract_version"],
                record["logical_artifact_ref"],
                record["artifact_id"],
                record["artifact_revision"],
                record["shard_id"],
                record["sink"],
                record["uri"],
                record["cid"],
                record["member_path"],
                record["content_digest"],
                record["payload_digest"],
                record["payload_size_bytes"],
                int(time.time()),
            ),
        )

    def ingest_neighbourhood(
        self,
        item: Mapping[str, Any],
        *,
        da51_address: Optional[str] = None,
        artifact_resolution_receipt: Optional[Mapping[str, Any]] = None,
    ) -> dict[str, Any]:
        normalized = normalize_neighbourhood(item)
        namespace = normalized["subject"]["namespace"]
        identifier = normalized["subject"]["identifier"]
        canonical_da51 = parse_da51(da51_address)["address"] if da51_address else None
        receipt = (
            ArtifactResolutionReceipt.from_mapping(artifact_resolution_receipt)
            if artifact_resolution_receipt is not None
            else None
        )

        self._node(namespace, identifier)
        existing = self.connection.execute(
            "SELECT da51_address FROM xpollenation_neighbourhoods WHERE namespace=? AND identifier=?",
            (namespace, identifier),
        ).fetchone()
        if existing is not None and existing[0] not in (None, canonical_da51):
            raise ValueError("xPollenation neighbourhood conflicts with persisted DA51 join")
        self.connection.execute(
            """
            INSERT INTO xpollenation_neighbourhoods(
                namespace, identifier, da51_address, authority,
                establishes_proof, establishes_payment, created_at
            ) VALUES(?, ?, ?, 'navigation-enrichment-only', 0, 0, ?)
            ON CONFLICT(namespace, identifier) DO UPDATE SET
                da51_address=COALESCE(excluded.da51_address, xpollenation_neighbourhoods.da51_address)
            """,
            (namespace, identifier, canonical_da51, int(time.time())),
        )

        for edge in normalized["edges"]:
            self._node(edge.subject_namespace, edge.subject_identifier)
            self._node(edge.object_namespace, edge.object_identifier)
            existing_edge = self.connection.execute(
                "SELECT * FROM xpollenation_edges WHERE edge_id=?",
                (edge.edge_id,),
            ).fetchone()
            values = (
                namespace,
                identifier,
                edge.subject_namespace,
                edge.subject_identifier,
                edge.relation,
                edge.object_namespace,
                edge.object_identifier,
                edge.source_ref,
                edge.source_revision,
                edge.acquisition_receipt,
                edge.status,
                int(edge.same_object_claimed),
                int(edge.same_object_verified),
                int(edge.context_equivalent),
            )
            if existing_edge is not None:
                current = dict(existing_edge)
                keys = (
                    "focus_namespace",
                    "focus_identifier",
                    "subject_namespace",
                    "subject_identifier",
                    "relation_kind",
                    "object_namespace",
                    "object_identifier",
                    "source_ref",
                    "source_revision",
                    "acquisition_receipt",
                    "status",
                    "same_object_claimed",
                    "same_object_verified",
                    "context_equivalent",
                )
                if any(current[key] != value for key, value in zip(keys, values)):
                    raise ValueError(f"xPollenation edge id conflicts with persisted edge: {edge.edge_id}")
                continue
            self.connection.execute(
                """
                INSERT INTO xpollenation_edges(
                    edge_id, focus_namespace, focus_identifier,
                    subject_namespace, subject_identifier, relation_kind,
                    object_namespace, object_identifier, source_ref, source_revision,
                    acquisition_receipt, status, same_object_claimed,
                    same_object_verified, context_equivalent, promotion_allowed,
                    authority, establishes_proof, establishes_payment, created_at
                ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 0,
                         'navigation-enrichment-only', 0, 0, ?)
                """,
                (edge.edge_id, *values, int(time.time())),
            )

        if receipt is not None:
            self._persist_artifact(namespace, identifier, receipt)
        self.connection.commit()
        return {
            "subject": normalized["subject"],
            "edge_count": len(normalized["edges"]),
            "da51_address": canonical_da51,
            "artifact": receipt.as_record() if receipt is not None else None,
            "authority": XPOLLENATION_AUTHORITY,
            "establishes_proof": False,
            "establishes_payment": False,
        }

    def _artifact(self, namespace: str, identifier: str) -> Optional[dict[str, Any]]:
        row = self.connection.execute(
            "SELECT * FROM xpollenation_artifacts WHERE namespace=? AND identifier=?",
            (namespace, identifier),
        ).fetchone()
        if row is None:
            return None
        result = dict(row)
        result.pop("namespace", None)
        result.pop("identifier", None)
        result.pop("created_at", None)
        result["verified"] = bool(result["verified"])
        result["establishes_proof"] = bool(result["establishes_proof"])
        return result

    def neighbourhood(self, namespace: str, identifier: str) -> Optional[dict[str, Any]]:
        namespace = _text("namespace", namespace).lower()
        identifier = _text("identifier", identifier)
        row = self.connection.execute(
            "SELECT * FROM xpollenation_neighbourhoods WHERE namespace=? AND identifier=?",
            (namespace, identifier),
        ).fetchone()
        if row is None:
            return None
        edges = [
            dict(item)
            for item in self.connection.execute(
                """
                SELECT edge_id, subject_namespace, subject_identifier, relation_kind,
                       object_namespace, object_identifier, source_ref, source_revision,
                       acquisition_receipt, status, same_object_claimed,
                       same_object_verified, context_equivalent, promotion_allowed,
                       authority, establishes_proof, establishes_payment
                FROM xpollenation_edges
                WHERE focus_namespace=? AND focus_identifier=?
                ORDER BY edge_id
                """,
                (namespace, identifier),
            ).fetchall()
        ]
        for edge in edges:
            for key in (
                "same_object_claimed",
                "same_object_verified",
                "context_equivalent",
                "promotion_allowed",
                "establishes_proof",
                "establishes_payment",
            ):
                edge[key] = bool(edge[key])
        return {
            "subject": {"namespace": namespace, "identifier": identifier},
            "da51_address": row["da51_address"],
            "edges": edges,
            "artifact": self._artifact(namespace, identifier),
            "authority": row["authority"],
            "establishes_proof": False,
            "establishes_payment": False,
        }

    def neighbourhoods_for_da51(self, address: str) -> list[dict[str, Any]]:
        canonical = parse_da51(address)["address"]
        rows = self.connection.execute(
            "SELECT namespace, identifier FROM xpollenation_neighbourhoods WHERE da51_address=? ORDER BY namespace, identifier",
            (canonical,),
        ).fetchall()
        return [
            item
            for row in rows
            if (item := self.neighbourhood(row["namespace"], row["identifier"])) is not None
        ]
