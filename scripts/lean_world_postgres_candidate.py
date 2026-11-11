#!/usr/bin/env python3
"""Atomic PostgreSQL persistence for SEALED UNVERIFIED Lean-world candidates.

Consumes the existing #1484 CanonicalLeanWorld, NEVER source text or a native
export directly. Requires the existing fibre migration and candidate DAG
migration. This is source/proof-occurrence preservation, not kernel admission.
"""
from __future__ import annotations
from hashlib import sha256
from lean_world_canonical_dag import WorldError

class CandidatePersistenceError(WorldError):
    pass

def persist_candidate_world(conn, world):
    """Persist all occurrences and edges or roll back the entire world.

    Caller owns an existing psycopg3 connection; no connection strings or
    credentials are accepted here. The function does NOT commit outside its
    own transaction and never marks anything kernel-certified.
    """
    if not world._sealed:
        raise CandidatePersistenceError("canonical DAG must be sealed")
    if not world.occurrences:
        raise CandidatePersistenceError("empty world cannot be admitted")
    with conn.transaction():
        with conn.cursor() as cur:
            origin_dbids = {}
            for origin in sorted(world.occurrences):
                row = world.occurrences[origin]
                stmt = world.statements[row["statement_id"]]
                source = world.sources.get((origin.repository, origin.revision,
                                            row["path"]))
                if source is None or row["source_sha256"] != source["sha256"]:
                    raise CandidatePersistenceError("missing original source evidence")
                if (row.get("kind") != "lean-elaborated-export" or
                    row.get("kernel_certified") is True or
                    row.get("world_admitted") is True):
                    raise CandidatePersistenceError("unexpected candidate promotion")
                cur.execute("""
                    INSERT INTO lean_world_fibre
                      (foundation_profile,type_head,universe_shape)
                    VALUES (%s,%s,%s)
                    ON CONFLICT (foundation_profile,type_head,universe_shape)
                    DO NOTHING
                """, (stmt.profile,stmt.type_head,stmt.universe_shape))
                cur.execute("""
                    SELECT fibre_id FROM lean_world_fibre
                    WHERE foundation_profile=%s AND type_head=%s
                      AND universe_shape=%s FOR UPDATE
                """, (stmt.profile,stmt.type_head,stmt.universe_shape))
                fibre_id = cur.fetchone()[0]
                canonical_hash = sha256(stmt.canonical_type).digest()
                cur.execute("""
                    SELECT statement_id, canonical_type
                    FROM lean_world_statement
                    WHERE fibre_id=%s AND canonical_sha256=%s FOR UPDATE
                """, (fibre_id,canonical_hash))
                existing = cur.fetchall()
                matching = [key for key, canonical in existing
                            if bytes(canonical) == stmt.canonical_type]
                if any(bytes(canonical) != stmt.canonical_type
                       for _,canonical in existing):
                    raise CandidatePersistenceError("canonical statement hash collision")
                if len(matching)>1:
                    raise CandidatePersistenceError("duplicate canonical statements")
                if matching:
                    statement_id=matching[0]
                else:
                    cur.execute("""
                        INSERT INTO lean_world_statement
                          (fibre_id,canonical_sha256,canonical_type)
                        VALUES (%s,%s,%s) RETURNING statement_id
                    """, (fibre_id,canonical_hash,stmt.canonical_type))
                    statement_id=cur.fetchone()[0]
                cur.execute("""
                    INSERT INTO lean_world_occurrence
                      (repository,revision,declaration,statement_id,fibre_id,
                       proof_term_digest,attribution)
                    VALUES (%s,%s,%s,%s,%s,%s,%s)
                    ON CONFLICT (repository,revision,declaration) DO NOTHING
                """, (origin.repository,origin.revision,origin.declaration,
                      statement_id,fibre_id,row["proof_digest"],
                      row["attribution"]))
                cur.execute("""
                    SELECT statement_id,fibre_id,proof_term_digest,attribution
                    FROM lean_world_occurrence
                    WHERE repository=%s AND revision=%s AND declaration=%s
                """, (origin.repository,origin.revision,origin.declaration))
                expected=(statement_id,fibre_id,row["proof_digest"],
                          row["attribution"])
                if tuple(cur.fetchone()) != expected:
                    raise CandidatePersistenceError("conflicting original occurrence")
                cur.execute("""
                    INSERT INTO lean_world_candidate_receipt
                      (repository,revision,declaration,source_path,
                       source_sha256,exporter_profile)
                    VALUES (%s,%s,%s,%s,%s,%s)
                    ON CONFLICT (repository,revision,declaration) DO NOTHING
                """, (origin.repository,origin.revision,origin.declaration,
                      row["path"],row["source_sha256"],row["exporter_profile"]))
                cur.execute("""
                    SELECT source_path,source_sha256,exporter_profile,status
                    FROM lean_world_candidate_receipt
                    WHERE repository=%s AND revision=%s AND declaration=%s
                """, (origin.repository,origin.revision,origin.declaration))
                if tuple(cur.fetchone()) != (row["path"],row["source_sha256"],
                                              row["exporter_profile"],
                                              "candidate-unverified"):
                    raise CandidatePersistenceError("conflicting candidate provenance")
                origin_dbids[origin] = statement_id
            for origin in sorted(world.occurrences):
                for dep in world._dependencies[origin]:
                    if dep not in origin_dbids:
                        raise CandidatePersistenceError("unresolved original edge")
                    cur.execute("""
                        INSERT INTO lean_world_candidate_dependency
                          (repository,revision,declaration,
                           dep_repository,dep_revision,dep_declaration)
                        VALUES (%s,%s,%s,%s,%s,%s)
                        ON CONFLICT DO NOTHING
                    """, (origin.repository,origin.revision,origin.declaration,
                          dep.repository,dep.revision,dep.declaration))
            # An existing original receipt may not be rebound to a different
            # outgoing edge set on retry, even when all individual edges exist.
            for origin in sorted(world.occurrences):
                cur.execute("""
                    SELECT dep_repository,dep_revision,dep_declaration
                    FROM lean_world_candidate_dependency
                    WHERE repository=%s AND revision=%s AND declaration=%s
                """, (origin.repository,origin.revision,origin.declaration))
                actual={tuple(row) for row in cur.fetchall()}
                expected={(d.repository,d.revision,d.declaration)
                          for d in world._dependencies[origin]}
                if actual != expected:
                    raise CandidatePersistenceError("conflicting dependency history")
    return {"status":"candidate-unverified",
            "original_occurrences":len(world.occurrences),
            "exact_statement_nodes":len(world.statements),
            "kernel_certified":False,
            "world_admitted":False}
