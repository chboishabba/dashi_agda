#!/usr/bin/env python3
"""Store exact Lean-generated joined theorem source + compiled OLean in PostgreSQL.

This is the selected original Lean compiler's success, not a stand-in for
independent checking, nor canonical theorem/type identity across projects.
Every compiled module is foreign-keyed to its original source occurrence.
"""
from __future__ import annotations
from hashlib import sha256
import json
from pathlib import Path

class JoinStoreError(ValueError):
    pass

def digest(data):
    return sha256(data).digest()

def persist_join(conn,report,generated_source,joined_olean):
    if (report.get("status")!="original-lean-theorem-joins-compiled" or
        report.get("independently_checked") is not False or
        report.get("world_admitted") is not False):
        raise JoinStoreError("original Lean proof result cannot be promoted")
    if not isinstance(generated_source,bytes) or not generated_source:
        raise JoinStoreError("missing actual generated Lean source")
    if not isinstance(joined_olean,bytes) or not joined_olean:
        raise JoinStoreError("missing actual checked OLean")
    if (sha256(generated_source).hexdigest()!=
            report.get("generated_join_source_sha256") or
        sha256(joined_olean).hexdigest()!=report.get("joined_olean_sha256")):
        raise JoinStoreError("proof artifact digest does not match compiled report")
    if len(generated_source)>8*1024*1024 or len(joined_olean)>128*1024*1024:
        raise JoinStoreError("compiled proof output exceeds review cap")
    original_modules=report.get("compiled_modules")
    donors=report.get("donor_names")
    if (not isinstance(original_modules,list) or not original_modules or
        not isinstance(donors,list) or not donors):
        raise JoinStoreError("no original module/theorem evidence")
    names=set()
    for row in original_modules:
        origin=row.get("original_source_origin")
        if (not isinstance(origin,dict) or row.get("module") in names or
            not all(origin.get(k) for k in (
                "repository","revision","path","source_sha256"))):
            raise JoinStoreError("missing or duplicate exact original source owner")
        if origin["source_sha256"]!=row.get("source_sha256"):
            raise JoinStoreError("compiled original source sha mismatch")
        names.add(row["module"])
    if len(set(donors))!=len(donors):
        raise JoinStoreError("duplicate donor theorem")
    profile={
        "schema":"original-lean-compiled-proof-join-v1",
        "compiler_sha256":report["lean_binary_sha256"],
        "snapshots":report.get("original_source_snapshots",[]),
        "generated_source_sha256":report["generated_join_source_sha256"],
        "olean_sha256":report["joined_olean_sha256"],
        "modules":[
            [row["module"],row["original_source_origin"],
             row["source_sha256"],row["olean_sha256"]]
            for row in original_modules],
        "donors":donors
    }
    batch_id=digest(json.dumps(profile,sort_keys=True,
                                separators=(",",":")).encode())
    migration=(Path(__file__).resolve().parent/"sql"/
               "lean_world_compiled_join_v1.sql").read_text()
    with conn.transaction():
        with conn.cursor() as cur:
            cur.execute(migration)
            # Validate actual FK source bytes/identity before any new rows.
            for row in original_modules:
                origin=row["original_source_origin"]
                cur.execute("""
                    SELECT encode(sha256,'hex')
                    FROM lean_world_source_occurrence
                    WHERE repository=%s AND revision=%s AND path=%s
                """,(origin["repository"],origin["revision"],origin["path"]))
                found=cur.fetchone()
                if found is None or found[0]!=row["source_sha256"]:
                    raise JoinStoreError("compiled module not bound to original PostgreSQL bytes")
            cur.execute("""
                INSERT INTO lean_world_compiled_join_batch (
                    batch_sha256,source_compiler_sha256,compiler_version,
                    original_source_snapshots,compiled_source,compiled_source_sha256,
                    compiled_olean,compiled_olean_sha256,
                    source_scope_count,joined_theorem_count)
                VALUES (%s,%s,%s,%s::jsonb,%s,%s,%s,%s,%s,%s)
                ON CONFLICT DO NOTHING
            """,(batch_id,bytes.fromhex(report["lean_binary_sha256"]),
                 report["lean_version"],json.dumps(report.get("original_source_snapshots",[])),
                 generated_source,digest(generated_source),
                 joined_olean,digest(joined_olean),
                 len(original_modules),len(donors)))
            cur.execute("""
                SELECT source_compiler_sha256,compiler_version,
                       original_source_snapshots,compiled_source,compiled_source_sha256,
                       compiled_olean,compiled_olean_sha256,
                       source_scope_count,joined_theorem_count,status
                FROM lean_world_compiled_join_batch WHERE batch_sha256=%s
            """,(batch_id,))
            stored=cur.fetchone()
            expected=(
                bytes.fromhex(report["lean_binary_sha256"]),
                report["lean_version"],report.get("original_source_snapshots",[]),
                generated_source,digest(generated_source),
                joined_olean,digest(joined_olean),
                len(original_modules),len(donors),
                "lean-compiled-original-proof-joins"
            )
            if stored is None or tuple(bytes(v) if isinstance(v,memoryview)
                    else v for v in stored)!=expected:
                raise JoinStoreError("compiled proof batch content collision")
            for row in original_modules:
                origin=row["original_source_origin"]
                cur.execute("""
                    INSERT INTO lean_world_compiled_join_module (
                        batch_sha256,module,original_repository,original_revision,
                        original_path,source_sha256,compiled_olean_sha256)
                    VALUES (%s,%s,%s,%s,%s,%s,%s) ON CONFLICT DO NOTHING
                """,(batch_id,row["module"],origin["repository"],origin["revision"],
                     origin["path"],bytes.fromhex(row["source_sha256"]),
                     bytes.fromhex(row["olean_sha256"])))
            # Scope is the compiled root whose imports established access to
            # the donor. It is NOT an assertion about the theorem's source file.
            root=report.get("root_module")
            if root not in names:
                raise JoinStoreError("compiled root missing from original module graph")
            for index,donor in enumerate(donors):
                cur.execute("""
                    INSERT INTO lean_world_compiled_join_theorem (
                        batch_sha256,join_name,donor_name,scope_module)
                    VALUES (%s,%s,%s,%s) ON CONFLICT DO NOTHING
                """,(batch_id,"DASHIJoined.join"+str(index),donor,root))
            cur.execute("""
                SELECT join_name,donor_name,scope_module
                FROM lean_world_compiled_join_theorem
                WHERE batch_sha256=%s ORDER BY join_name
            """,(batch_id,))
            actual=cur.fetchall()
            wanted=sorted(
                [("DASHIJoined.join"+str(i),donor,root)
                 for i,donor in enumerate(donors)])
            if actual!=wanted:
                raise JoinStoreError("conflicting original theorem join history")
            cur.execute("""
                SELECT module,original_repository,original_revision,
                       original_path,encode(source_sha256,'hex'),
                       encode(compiled_olean_sha256,'hex')
                FROM lean_world_compiled_join_module
                WHERE batch_sha256=%s
            """,(batch_id,))
            observed={
                (r[0],r[1],r[2],r[3],r[4],r[5]) for r in cur.fetchall()
            }
            target={
                (r["module"],r["original_source_origin"]["repository"],
                 r["original_source_origin"]["revision"],
                 r["original_source_origin"]["path"],
                 r["source_sha256"],r["olean_sha256"])
                 for r in original_modules
            }
            if observed!=target:
                raise JoinStoreError("conflicting original compiled module history")
    return {
        "status":"lean-compiled-original-proof-joins",
        "batch_sha256":batch_id.hex(),
        "module_occurrences":len(original_modules),
        "joined_theorems":len(donors),
        "generated_source_bytes":len(generated_source),
        "joined_olean_bytes":len(joined_olean),
        "content_stored_in_postgresql":True,
        "independently_checked":False,
        "world_admitted":False
    }


def fetch_join(conn,batch_hex):
    """Recover actual joined proof source + OLean, checking stored digests."""
    if not isinstance(batch_hex,str) or len(batch_hex)!=64:
        raise JoinStoreError("bad original proof join batch key")
    with conn.cursor() as cur:
        cur.execute("""
            SELECT compiled_source,compiled_source_sha256,
                   compiled_olean,compiled_olean_sha256
            FROM lean_world_compiled_join_batch WHERE batch_sha256=%s
        """,(bytes.fromhex(batch_hex),))
        found=cur.fetchone()
    if found is None:
        raise JoinStoreError("compiled proof join not found")
    source,source_hash,olean,olean_hash=found
    source,olean=bytes(source),bytes(olean)
    if digest(source)!=bytes(source_hash) or digest(olean)!=bytes(olean_hash):
        raise JoinStoreError("stored compiled theorem bytes corrupted")
    return source,olean
