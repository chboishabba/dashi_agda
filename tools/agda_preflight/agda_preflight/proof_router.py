from __future__ import annotations

from dataclasses import dataclass
import hashlib
import sqlite3
import time
from typing import Any, Callable, Optional


DA51_PREFIX = 0xDA51
DA51_DATA_MASK = (1 << 44) - 1
DA51_KNOWN_TYPES = frozenset(range(9))
ATLAS_TYPE = 8
ATLAS_LEVELS = frozenset(range(6))
ATLAS_BIOMES = frozenset(range(9))
ATLAS_STATUSES = frozenset(range(5))

PROOF_ROUTER_SCHEMA = "1"
DA51_REGISTRY_SCHEMA = "1"


@dataclass(frozen=True)
class ProofRouteRequest:
    query: str
    target_prover: str = "lean"
    claim_kind: str = "deductive"
    mathematical_status: str = "novel-open"
    statement_status: str = "not-transcribed"
    certification_status: str = "uncertified"
    da51_address: Optional[str] = None
    source_declaration: Optional[str] = None
    current_source_hash: Optional[str] = None


def parse_da51(address: str, *, allow_unknown_type: bool = False) -> dict[str, Any]:
    text = address.strip()
    body = text[2:] if text[:2].lower() == "0x" else text
    if len(body) != 16 or not body.isascii():
        raise ValueError("DA51 address must contain exactly 16 ASCII hexadecimal digits")
    try:
        raw = int(body, 16)
    except ValueError as exc:
        raise ValueError("DA51 address contains non-hexadecimal characters") from exc
    prefix = raw >> 48
    if prefix != DA51_PREFIX:
        raise ValueError(f"wrong DA51 prefix: 0x{prefix:04X}")
    type_code = (raw >> 44) & 0xF
    if type_code not in DA51_KNOWN_TYPES and not allow_unknown_type:
        raise ValueError(f"unassigned DA51 type code {type_code}")
    data = raw & DA51_DATA_MASK
    atlas = None
    if type_code == ATLAS_TYPE:
        reserved = data & ((1 << 20) - 1)
        if reserved:
            raise ValueError(f"atlas reserved bits are nonzero: 0x{reserved:05X}")
        level = (data >> 40) & 0xF
        biome = (data >> 36) & 0xF
        status = (data >> 32) & 0xF
        serial = (data >> 20) & 0xFFF
        if level not in ATLAS_LEVELS:
            raise ValueError(f"invalid atlas level code {level}")
        if biome not in ATLAS_BIOMES:
            raise ValueError(f"invalid atlas biome code {biome}")
        if status not in ATLAS_STATUSES:
            raise ValueError(f"invalid atlas status code {status}")
        atlas = {
            "level": level,
            "biome": biome,
            "status": status,
            "serial": serial,
            "reserved": reserved,
        }
    return {
        "address": f"0x{raw:016X}",
        "raw": raw,
        "prefix": DA51_PREFIX,
        "type_code": type_code,
        "known_type": type_code in DA51_KNOWN_TYPES,
        "data": data,
        "data_hex": f"0x{data:011X}",
        "atlas": atlas,
        "authority": "identity-only",
        "establishes_proof": False,
    }


def ensure_proof_router_schema(conn: sqlite3.Connection) -> None:
    conn.execute("PRAGMA foreign_keys=ON")
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS da51_objects (
            address TEXT PRIMARY KEY,
            type_code INTEGER NOT NULL,
            data_hex TEXT NOT NULL,
            canonical_owner TEXT NOT NULL DEFAULT 'dashi_lean4/DA51.Core',
            authority TEXT NOT NULL DEFAULT 'identity-only',
            created_at INTEGER NOT NULL
        );

        CREATE TABLE IF NOT EXISTS da51_symbol_links (
            address TEXT NOT NULL REFERENCES da51_objects(address) ON DELETE CASCADE,
            symbol_id TEXT NOT NULL,
            relation TEXT NOT NULL,
            source TEXT NOT NULL,
            PRIMARY KEY(address, symbol_id, relation, source)
        ) WITHOUT ROWID;
        CREATE INDEX IF NOT EXISTS da51_symbol_links_symbol
            ON da51_symbol_links(symbol_id);

        CREATE TABLE IF NOT EXISTS da51_evidence (
            address TEXT NOT NULL REFERENCES da51_objects(address) ON DELETE CASCADE,
            producer TEXT NOT NULL,
            artifact TEXT NOT NULL,
            evidence_kind TEXT NOT NULL,
            revision TEXT NOT NULL DEFAULT '',
            digest TEXT NOT NULL DEFAULT '',
            authority TEXT NOT NULL DEFAULT 'evidence-only',
            created_at INTEGER NOT NULL,
            PRIMARY KEY(address, producer, artifact, evidence_kind, revision, digest)
        ) WITHOUT ROWID;
        CREATE INDEX IF NOT EXISTS da51_evidence_artifact
            ON da51_evidence(producer, artifact);

        CREATE TABLE IF NOT EXISTS proof_routes (
            route_id TEXT PRIMARY KEY,
            created_at INTEGER NOT NULL,
            query TEXT NOT NULL,
            target_prover TEXT NOT NULL,
            claim_kind TEXT NOT NULL,
            mathematical_status TEXT NOT NULL,
            statement_status TEXT NOT NULL,
            certification_status TEXT NOT NULL,
            debt_kind TEXT NOT NULL,
            recommended_backend TEXT NOT NULL,
            generation_permitted INTEGER NOT NULL,
            absence_status TEXT NOT NULL,
            da51_address TEXT,
            source_declaration TEXT,
            agda2lean_mapping_mode TEXT,
            authority TEXT NOT NULL DEFAULT 'routing-only',
            translation_establishes_proof INTEGER NOT NULL DEFAULT 0,
            FOREIGN KEY(da51_address) REFERENCES da51_objects(address)
        );
        CREATE INDEX IF NOT EXISTS proof_routes_da51 ON proof_routes(da51_address);
        CREATE INDEX IF NOT EXISTS proof_routes_query ON proof_routes(query);

        CREATE TABLE IF NOT EXISTS proof_route_matches (
            route_id TEXT NOT NULL REFERENCES proof_routes(route_id) ON DELETE CASCADE,
            ordinal INTEGER NOT NULL,
            match_kind TEXT NOT NULL,
            symbol_id TEXT NOT NULL,
            similarity REAL,
            PRIMARY KEY(route_id, match_kind, ordinal)
        ) WITHOUT ROWID;
        """
    )
    try:
        conn.execute(
            "INSERT INTO repository_meta(key, value) VALUES('proof_router_schema', ?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (PROOF_ROUTER_SCHEMA,),
        )
        conn.execute(
            "INSERT INTO repository_meta(key, value) VALUES('da51_registry_schema', ?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (DA51_REGISTRY_SCHEMA,),
        )
    except sqlite3.OperationalError:
        # Standalone use is permitted, but dashi-repo normally creates
        # repository_meta before this extension is installed.
        pass
    conn.commit()


def classify_debt(request: ProofRouteRequest) -> str:
    target = request.target_prover.lower()
    certified = {
        "lean": "lean-kernel",
        "agda": "agda-kernel",
    }.get(target)
    if certified is not None and request.certification_status == certified:
        return "none"
    if request.claim_kind == "empirical":
        return "empirical-evidence-debt"
    if request.statement_status in {"not-transcribed", "transcribed-unaligned"}:
        # A genuinely novel theorem is mathematical debt even before there is
        # a local transcription. Source-established material is transcription
        # debt until statement alignment is paid.
        if request.mathematical_status not in {"source-established", "derived-in-repo"}:
            return "mathematical-debt"
        return "transcription-debt"
    if (
        request.mathematical_status in {"source-established", "derived-in-repo"}
        and request.statement_status == "source-aligned"
    ):
        return "certification-debt"
    if request.mathematical_status in {"novel-open", "experimentally-supported"}:
        return "mathematical-debt"
    return "mathematical-debt"


def _normalize_mapping_mode(value: Optional[str]) -> Optional[str]:
    if value is None:
        return None
    lowered = value.strip().lower().replace("_", "-")
    canonical = {
        "exact": "Exact",
        "encoded": "Encoded",
        "reconstruct": "Reconstruct",
        "quarantined": "Quarantined",
        "unsupported": "Unsupported",
    }
    return canonical.get(lowered, value.strip())


def _candidate_rows(discovery: dict[str, Any]) -> list[tuple[str, dict[str, Any]]]:
    rows: list[tuple[str, dict[str, Any]]] = []
    for item in discovery.get("live_matches", ()):
        rows.append(("live", item))
    related = discovery.get("related", {}) or {}
    for kind in ("signature_equivalent", "body_equivalent", "similar"):
        for item in related.get(kind, ()) or ():
            rows.append((kind, item))
    for item in discovery.get("query_similar", ()) or ():
        rows.append(("query_similar", item))
    for item in discovery.get("historical_matches", ()) or ():
        rows.append(("historical", item))
    return rows


class ProofRouter:
    """Fail-closed proof/formalisation router over repository intelligence.

    Discovery and compiler/translation capability are observations only. The
    returned route is scheduling metadata and never theorem or authority proof.
    """

    def __init__(
        self,
        *,
        discovery: Callable[..., dict[str, Any]],
        semantic_catalog=None,
        connection: Optional[sqlite3.Connection] = None,
    ) -> None:
        self.discovery = discovery
        self.semantic_catalog = semantic_catalog
        self.connection = connection
        if self.connection is not None:
            ensure_proof_router_schema(self.connection)

    def _capability(self, request: ProofRouteRequest) -> Optional[dict[str, Any]]:
        if self.semantic_catalog is None or not request.source_declaration:
            return None
        lookup = getattr(self.semantic_catalog, "declaration_capability", None)
        if lookup is None:
            return None
        return lookup(
            request.source_declaration,
            current_source_hash=request.current_source_hash,
        )

    @staticmethod
    def _backend(
        request: ProofRouteRequest,
        debt: str,
        mapping_mode: Optional[str],
    ) -> tuple[str, bool]:
        target = request.target_prover.lower()
        if debt == "none":
            return "reuse-existing", False
        if debt == "empirical-evidence-debt":
            return "evidence-acquisition", False
        if target == "agda":
            if debt == "mathematical-debt":
                return "aristotle+agda", True
            if debt == "transcription-debt":
                return "agda-formaliser", True
            return "agda-kernel", False
        if target != "lean":
            return "manual-formalisation", False
        if debt == "mathematical-debt":
            return "aristotle+lean", True
        if mapping_mode in {"Exact", "Encoded"}:
            return "agda2lean", True
        if mapping_mode == "Reconstruct":
            return "agda2lean+aristotle-lean", True
        if mapping_mode in {"Quarantined", "Unsupported"}:
            return "aristotle-lean", True
        if debt == "transcription-debt" and request.source_declaration:
            return "agda2lean-preflight", False
        if debt == "certification-debt":
            return "lean-kernel", False
        return "aristotle+lean", True

    def route(self, request: ProofRouteRequest, *, limit: int = 50) -> dict[str, Any]:
        query = request.query.strip()
        if not query:
            raise ValueError("proof route query must be non-empty")
        if request.target_prover.lower() not in {"lean", "agda"}:
            raise ValueError("target_prover must be 'lean' or 'agda'")

        discovery = self.discovery(query, limit=limit)
        candidates = _candidate_rows(discovery)
        live_or_equivalent = any(
            kind in {"live", "signature_equivalent", "body_equivalent"}
            for kind, _ in candidates
        )
        absence_status = str(discovery.get("absence_status", "search_incomplete"))
        absence_permitted = bool(discovery.get("absence_claim_permitted", False))
        capability = self._capability(request)
        mapping_mode = _normalize_mapping_mode(
            capability.get("mapping_mode") if capability else None
        )

        if live_or_equivalent:
            debt = "reuse-review"
            backend = "repository-reuse-review"
            generation_permitted = False
        elif not absence_permitted:
            debt = "discovery-debt"
            backend = "repository-discovery"
            generation_permitted = False
        else:
            debt = classify_debt(request)
            backend, generation_permitted = self._backend(request, debt, mapping_mode)

        da51 = parse_da51(request.da51_address) if request.da51_address else None
        stable = "\n".join(
            (
                query,
                request.target_prover.lower(),
                request.claim_kind,
                request.mathematical_status,
                request.statement_status,
                request.certification_status,
                debt,
                backend,
                da51["address"] if da51 else "",
                request.source_declaration or "",
                mapping_mode or "",
                absence_status,
            )
        )
        route_id = hashlib.sha256(stable.encode("utf-8")).hexdigest()
        result = {
            "route_id": route_id,
            "query": query,
            "target_prover": request.target_prover.lower(),
            "claim_kind": request.claim_kind,
            "mathematical_status": request.mathematical_status,
            "statement_status": request.statement_status,
            "certification_status": request.certification_status,
            "debt_kind": debt,
            "recommended_backend": backend,
            "generation_permitted": generation_permitted,
            "absence_status": absence_status,
            "discovery": discovery,
            "matches": [
                {
                    "kind": kind,
                    "symbol_id": item.get("qualified_name") or item.get("symbol_id") or item.get("name", ""),
                    "similarity": item.get("similarity", item.get("query_similarity")),
                }
                for kind, item in candidates
            ],
            "da51": da51,
            "source_declaration": request.source_declaration,
            "agda2lean": capability,
            "agda2lean_mapping_mode": mapping_mode,
            "authority": "routing-only",
            "translation_establishes_proof": False,
        }
        if self.connection is not None:
            self._persist(request, result)
        return result

    def _persist(self, request: ProofRouteRequest, result: dict[str, Any]) -> None:
        assert self.connection is not None
        da51 = result.get("da51")
        if da51 is not None:
            self._ensure_da51(da51)
        self.connection.execute(
            """
            INSERT INTO proof_routes(
                route_id, created_at, query, target_prover, claim_kind,
                mathematical_status, statement_status, certification_status,
                debt_kind, recommended_backend, generation_permitted,
                absence_status, da51_address, source_declaration,
                agda2lean_mapping_mode, authority, translation_establishes_proof
            ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'routing-only', 0)
            ON CONFLICT(route_id) DO UPDATE SET
                created_at=excluded.created_at,
                debt_kind=excluded.debt_kind,
                recommended_backend=excluded.recommended_backend,
                generation_permitted=excluded.generation_permitted,
                absence_status=excluded.absence_status,
                agda2lean_mapping_mode=excluded.agda2lean_mapping_mode
            """,
            (
                result["route_id"],
                int(time.time()),
                result["query"],
                result["target_prover"],
                result["claim_kind"],
                result["mathematical_status"],
                result["statement_status"],
                result["certification_status"],
                result["debt_kind"],
                result["recommended_backend"],
                int(bool(result["generation_permitted"])),
                result["absence_status"],
                da51["address"] if da51 else None,
                request.source_declaration,
                result.get("agda2lean_mapping_mode"),
            ),
        )
        self.connection.execute(
            "DELETE FROM proof_route_matches WHERE route_id=?",
            (result["route_id"],),
        )
        ordinals: dict[str, int] = {}
        for match in result["matches"]:
            kind = match["kind"]
            ordinal = ordinals.get(kind, 0)
            ordinals[kind] = ordinal + 1
            self.connection.execute(
                "INSERT INTO proof_route_matches(route_id, ordinal, match_kind, symbol_id, similarity) VALUES(?, ?, ?, ?, ?)",
                (
                    result["route_id"], ordinal, kind, match["symbol_id"], match["similarity"]
                ),
            )
        self.connection.commit()

    def _ensure_da51(self, parsed: dict[str, Any]) -> None:
        assert self.connection is not None
        self.connection.execute(
            """
            INSERT OR IGNORE INTO da51_objects(
                address, type_code, data_hex, canonical_owner, authority, created_at
            ) VALUES(?, ?, ?, 'dashi_lean4/DA51.Core', 'identity-only', ?)
            """,
            (parsed["address"], parsed["type_code"], parsed["data_hex"], int(time.time())),
        )

    def resolve_da51(self, address: str) -> dict[str, Any]:
        parsed = parse_da51(address)
        result = dict(parsed)
        result["symbol_links"] = []
        result["evidence"] = []
        if self.connection is None:
            return result
        self._ensure_da51(parsed)
        result["symbol_links"] = [
            dict(row)
            for row in self.connection.execute(
                "SELECT symbol_id, relation, source FROM da51_symbol_links WHERE address=? ORDER BY symbol_id, relation, source",
                (parsed["address"],),
            ).fetchall()
        ]
        result["evidence"] = self.evidence_for(parsed["address"])
        self.connection.commit()
        return result

    def link_da51(self, address: str, symbol_id: str, *, relation: str, source: str) -> dict[str, Any]:
        if self.connection is None:
            raise ValueError("DA51 link persistence requires a repository connection")
        parsed = parse_da51(address)
        self._ensure_da51(parsed)
        self.connection.execute(
            "INSERT OR IGNORE INTO da51_symbol_links(address, symbol_id, relation, source) VALUES(?, ?, ?, ?)",
            (parsed["address"], symbol_id.strip(), relation.strip(), source.strip()),
        )
        self.connection.commit()
        return self.resolve_da51(parsed["address"])

    def add_evidence(
        self,
        address: str,
        *,
        producer: str,
        artifact: str,
        evidence_kind: str,
        revision: str = "",
        digest: str = "",
    ) -> dict[str, Any]:
        if self.connection is None:
            raise ValueError("DA51 evidence persistence requires a repository connection")
        parsed = parse_da51(address)
        self._ensure_da51(parsed)
        self.connection.execute(
            """
            INSERT OR IGNORE INTO da51_evidence(
                address, producer, artifact, evidence_kind, revision, digest,
                authority, created_at
            ) VALUES(?, ?, ?, ?, ?, ?, 'evidence-only', ?)
            """,
            (
                parsed["address"], producer.strip().lower(), artifact.strip(),
                evidence_kind.strip().lower(), revision.strip(), digest.strip(), int(time.time())
            ),
        )
        self.connection.commit()
        return {
            "address": parsed["address"],
            "evidence": self.evidence_for(parsed["address"]),
            "authority": "evidence-only",
        }

    def evidence_for(self, address: str) -> list[dict[str, Any]]:
        if self.connection is None:
            return []
        parsed = parse_da51(address)
        rows = self.connection.execute(
            """
            SELECT producer, artifact, evidence_kind, revision, digest, authority, created_at
            FROM da51_evidence WHERE address=?
            ORDER BY producer, evidence_kind, artifact, revision, digest
            """,
            (parsed["address"],),
        ).fetchall()
        return [dict(row) for row in rows]

    def frontier_for(self, address: str) -> dict[str, Any]:
        if self.connection is None:
            return {"address": parse_da51(address)["address"], "routes": []}
        parsed = parse_da51(address)
        rows = self.connection.execute(
            """
            SELECT route_id, created_at, query, debt_kind, recommended_backend,
                   generation_permitted, absence_status, authority
            FROM proof_routes WHERE da51_address=? ORDER BY created_at DESC, route_id
            """,
            (parsed["address"],),
        ).fetchall()
        return {
            "address": parsed["address"],
            "routes": [dict(row) for row in rows],
            "authority": "routing-only",
        }

    def route_history(self, *, query: Optional[str] = None, address: Optional[str] = None, limit: int = 50) -> list[dict[str, Any]]:
        if self.connection is None:
            return []
        clauses = []
        params: list[Any] = []
        if query:
            clauses.append("query LIKE ?")
            params.append(f"%{query}%")
        if address:
            clauses.append("da51_address=?")
            params.append(parse_da51(address)["address"])
        where = " WHERE " + " AND ".join(clauses) if clauses else ""
        params.append(limit)
        rows = self.connection.execute(
            "SELECT * FROM proof_routes" + where + " ORDER BY created_at DESC, route_id LIMIT ?",
            params,
        ).fetchall()
        return [dict(row) for row in rows]
