from __future__ import annotations

from dataclasses import dataclass
import hashlib
import sqlite3
import time
from typing import Any, Optional

from .proof_router import ProofRouteRequest, ProofRouter, parse_da51


EXTERNAL_PROOF_BRIDGE_SCHEMA = "1"


@dataclass(frozen=True)
class ExternalProofDemand:
    demand_ref: str
    external_obligation_ref: str
    statement_digest: str
    query: str
    target_prover: str = "lean"
    claim_kind: str = "deductive"
    mathematical_status: str = "novel-open"
    statement_status: str = "not-transcribed"
    certification_status: str = "uncertified"
    da51_address: Optional[str] = None
    source_declaration: Optional[str] = None
    current_source_hash: Optional[str] = None

    def validate(self) -> None:
        for name, value in (
            ("demand_ref", self.demand_ref),
            ("external_obligation_ref", self.external_obligation_ref),
            ("statement_digest", self.statement_digest),
            ("query", self.query),
        ):
            if not value.strip():
                raise ValueError(f"{name} must be non-empty")


@dataclass(frozen=True)
class ExternalFormalEvidence:
    evidence_ref: str
    demand_ref: str
    external_obligation_ref: str
    statement_digest: str
    da51_address: Optional[str]
    producer: str
    artifact_ref: str
    artifact_digest: str
    checker: str
    checker_revision: str
    result_kind: str
    certification_state: str

    def validate(self) -> None:
        for name, value in (
            ("evidence_ref", self.evidence_ref),
            ("demand_ref", self.demand_ref),
            ("external_obligation_ref", self.external_obligation_ref),
            ("statement_digest", self.statement_digest),
            ("producer", self.producer),
            ("artifact_ref", self.artifact_ref),
            ("artifact_digest", self.artifact_digest),
            ("checker", self.checker),
            ("checker_revision", self.checker_revision),
            ("result_kind", self.result_kind),
            ("certification_state", self.certification_state),
        ):
            if not value.strip():
                raise ValueError(f"{name} must be non-empty")


def ensure_external_proof_bridge_schema(conn: sqlite3.Connection) -> None:
    conn.execute("PRAGMA foreign_keys=ON")
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS external_proof_demands (
            demand_ref TEXT NOT NULL,
            external_obligation_ref TEXT NOT NULL,
            statement_digest TEXT NOT NULL,
            external_route_id TEXT NOT NULL UNIQUE,
            route_id TEXT NOT NULL REFERENCES proof_routes(route_id) ON DELETE CASCADE,
            da51_address TEXT,
            created_at INTEGER NOT NULL,
            authority TEXT NOT NULL DEFAULT 'routing-only',
            establishes_proof INTEGER NOT NULL DEFAULT 0,
            PRIMARY KEY(demand_ref, external_obligation_ref, statement_digest),
            FOREIGN KEY(da51_address) REFERENCES da51_objects(address)
        ) WITHOUT ROWID;
        CREATE INDEX IF NOT EXISTS external_proof_demands_obligation
            ON external_proof_demands(external_obligation_ref, demand_ref, statement_digest);

        CREATE TABLE IF NOT EXISTS external_formal_evidence (
            evidence_ref TEXT PRIMARY KEY,
            demand_ref TEXT NOT NULL,
            external_obligation_ref TEXT NOT NULL,
            statement_digest TEXT NOT NULL,
            da51_address TEXT,
            producer TEXT NOT NULL,
            artifact_ref TEXT NOT NULL,
            artifact_digest TEXT NOT NULL,
            checker TEXT NOT NULL,
            checker_revision TEXT NOT NULL,
            result_kind TEXT NOT NULL,
            certification_state TEXT NOT NULL,
            authority TEXT NOT NULL DEFAULT 'evidence-only',
            establishes_proof INTEGER NOT NULL DEFAULT 0,
            created_at INTEGER NOT NULL,
            FOREIGN KEY(da51_address) REFERENCES da51_objects(address),
            FOREIGN KEY(demand_ref, external_obligation_ref, statement_digest)
                REFERENCES external_proof_demands(demand_ref, external_obligation_ref, statement_digest)
                ON DELETE CASCADE
        );
        CREATE INDEX IF NOT EXISTS external_formal_evidence_obligation
            ON external_formal_evidence(demand_ref, external_obligation_ref, statement_digest);
        """
    )
    try:
        conn.execute(
            "INSERT INTO repository_meta(key, value) VALUES('external_proof_bridge_schema', ?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (EXTERNAL_PROOF_BRIDGE_SCHEMA,),
        )
    except sqlite3.OperationalError:
        pass
    conn.commit()


class ExternalProofRouter:
    """Authority-neutral adapter for SLR/external proof obligations.

    The adapter delegates discovery/debt/backend selection to ``ProofRouter`` and
    persists only the external demand/obligation/statement-digest join. It never
    mirrors SLR PNF, residual, proposition, Matter, or payment payloads.
    """

    def __init__(self, router: ProofRouter, connection: sqlite3.Connection) -> None:
        self.router = router
        self.connection = connection
        ensure_external_proof_bridge_schema(connection)

    @staticmethod
    def _external_route_id(demand: ExternalProofDemand, base_route_id: str) -> str:
        stable = "\n".join(
            (
                base_route_id,
                demand.demand_ref.strip(),
                demand.external_obligation_ref.strip(),
                demand.statement_digest.strip(),
            )
        )
        return hashlib.sha256(stable.encode("utf-8")).hexdigest()

    def route(self, demand: ExternalProofDemand, *, limit: int = 50) -> dict[str, Any]:
        demand.validate()
        result = self.router.route(
            ProofRouteRequest(
                query=demand.query,
                target_prover=demand.target_prover,
                claim_kind=demand.claim_kind,
                mathematical_status=demand.mathematical_status,
                statement_status=demand.statement_status,
                certification_status=demand.certification_status,
                da51_address=demand.da51_address,
                source_declaration=demand.source_declaration,
                current_source_hash=demand.current_source_hash,
            ),
            limit=limit,
        )
        external_route_id = self._external_route_id(demand, result["route_id"])
        da51_address = result.get("da51", {}).get("address") if result.get("da51") else None
        self.connection.execute(
            """
            INSERT INTO external_proof_demands(
                demand_ref, external_obligation_ref, statement_digest,
                external_route_id, route_id, da51_address, created_at,
                authority, establishes_proof
            ) VALUES(?, ?, ?, ?, ?, ?, ?, 'routing-only', 0)
            ON CONFLICT(demand_ref, external_obligation_ref, statement_digest)
            DO UPDATE SET
                external_route_id=excluded.external_route_id,
                route_id=excluded.route_id,
                da51_address=excluded.da51_address,
                created_at=excluded.created_at
            """,
            (
                demand.demand_ref.strip(),
                demand.external_obligation_ref.strip(),
                demand.statement_digest.strip(),
                external_route_id,
                result["route_id"],
                da51_address,
                int(time.time()),
            ),
        )
        self.connection.commit()
        return {
            **result,
            "external_route_id": external_route_id,
            "demand_ref": demand.demand_ref.strip(),
            "external_obligation_ref": demand.external_obligation_ref.strip(),
            "statement_digest": demand.statement_digest.strip(),
            "establishes_proof": False,
            "authority": "routing-only",
        }

    def record_evidence(self, evidence: ExternalFormalEvidence) -> dict[str, Any]:
        evidence.validate()
        da51_address = parse_da51(evidence.da51_address)["address"] if evidence.da51_address else None
        row = self.connection.execute(
            """
            SELECT da51_address
            FROM external_proof_demands
            WHERE demand_ref=? AND external_obligation_ref=? AND statement_digest=?
            """,
            (
                evidence.demand_ref.strip(),
                evidence.external_obligation_ref.strip(),
                evidence.statement_digest.strip(),
            ),
        ).fetchone()
        if row is None:
            raise ValueError("formal evidence has no matching persisted external demand")
        expected_da51 = row[0]
        if expected_da51 is not None and expected_da51 != da51_address:
            raise ValueError("formal evidence DA51 address does not match persisted demand")
        self.connection.execute(
            """
            INSERT INTO external_formal_evidence(
                evidence_ref, demand_ref, external_obligation_ref, statement_digest,
                da51_address, producer, artifact_ref, artifact_digest, checker,
                checker_revision, result_kind, certification_state, authority,
                establishes_proof, created_at
            ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'evidence-only', 0, ?)
            ON CONFLICT(evidence_ref) DO NOTHING
            """,
            (
                evidence.evidence_ref.strip(),
                evidence.demand_ref.strip(),
                evidence.external_obligation_ref.strip(),
                evidence.statement_digest.strip(),
                da51_address,
                evidence.producer.strip(),
                evidence.artifact_ref.strip(),
                evidence.artifact_digest.strip(),
                evidence.checker.strip(),
                evidence.checker_revision.strip(),
                evidence.result_kind.strip(),
                evidence.certification_state.strip(),
                int(time.time()),
            ),
        )
        self.connection.commit()
        return {
            "evidence_ref": evidence.evidence_ref.strip(),
            "demand_ref": evidence.demand_ref.strip(),
            "external_obligation_ref": evidence.external_obligation_ref.strip(),
            "statement_digest": evidence.statement_digest.strip(),
            "authority": "evidence-only",
            "establishes_proof": False,
        }

    def evidence_for_obligation(
        self,
        *,
        demand_ref: str,
        external_obligation_ref: str,
        statement_digest: str,
    ) -> list[dict[str, Any]]:
        rows = self.connection.execute(
            """
            SELECT evidence_ref, demand_ref, external_obligation_ref, statement_digest,
                   da51_address, producer, artifact_ref, artifact_digest, checker,
                   checker_revision, result_kind, certification_state, authority,
                   establishes_proof, created_at
            FROM external_formal_evidence
            WHERE demand_ref=? AND external_obligation_ref=? AND statement_digest=?
            ORDER BY created_at, evidence_ref
            """,
            (demand_ref.strip(), external_obligation_ref.strip(), statement_digest.strip()),
        ).fetchall()
        return [dict(row) for row in rows]

    def route_history_for_obligation(
        self,
        *,
        demand_ref: Optional[str] = None,
        external_obligation_ref: Optional[str] = None,
        limit: int = 50,
    ) -> list[dict[str, Any]]:
        clauses: list[str] = []
        params: list[Any] = []
        if demand_ref:
            clauses.append("demand_ref=?")
            params.append(demand_ref.strip())
        if external_obligation_ref:
            clauses.append("external_obligation_ref=?")
            params.append(external_obligation_ref.strip())
        where = " WHERE " + " AND ".join(clauses) if clauses else ""
        params.append(limit)
        rows = self.connection.execute(
            "SELECT * FROM external_proof_demands" + where + " ORDER BY created_at DESC, external_route_id LIMIT ?",
            params,
        ).fetchall()
        return [dict(row) for row in rows]
