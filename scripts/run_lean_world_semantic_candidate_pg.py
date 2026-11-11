#!/usr/bin/env python3
"""Read #1495 native checker acceptance into #1484 candidate-only PG world.

Every linked file is digest verified and bound to original declaration, source
hash and native export. The acceptance JSON remains UNTRUSTED evidence:
it does not authenticate a checker or grant kernel/world certification.
"""
from __future__ import annotations
import argparse
import base64
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import sys

from run_lean_world_export_admission import build, jsonl
from lean_world_postgres_candidate import persist_candidate_world

HEX64=re.compile(r"[0-9a-f]{64}\Z")
HEX40=re.compile(r"[0-9a-f]{40}\Z")
class SemanticCandidateError(ValueError):
    pass

def load_acceptance(path: Path):
    if path.is_symlink() or not path.is_file():
        raise SemanticCandidateError("unsafe acceptance receipt")
    try:
        evidence=json.loads(path.read_bytes())
    except (ValueError,OSError) as exc:
        raise SemanticCandidateError("malformed acceptance receipt") from exc
    if not isinstance(evidence,dict) or evidence.get("schema") != (
            "dashi-lean-real-independent-semantic-acceptance-v1"):
        raise SemanticCandidateError("unsupported acceptance receipt")
    if evidence.get("status") != "independent-checker-observed-two-module-reuse":
        raise SemanticCandidateError("incomplete checker observation")
    # The cross-PR acceptance is now specifically pinned to the independent
    # Rust implementation; legacy Tenet observations are not equivalent.
    if (evidence.get("checker_kind") != "rust-nanoda" or
        evidence.get("checker_source_sha") !=
        "418320295890faed83a96fd97907b12a3b6728c2"):
        raise SemanticCandidateError("wrong independent Rust checker identity")
    if evidence.get("checker_policy",{}).get("unsafe_permit_all_axioms") is not False:
        raise SemanticCandidateError("unsafe checker axiom policy")
    if "sorryAx" in evidence.get("checker_policy",{}).get("permitted_axioms",[]):
        raise SemanticCandidateError("sorry axiom incorrectly permitted")
    if (evidence.get("independent_checker_observed") is not True or
        evidence.get("invalid_fixture_rejected") is not True or
        evidence.get("postgres_world_admitted") is not False or
        evidence.get("fibre_retrieved") is not False):
        raise SemanticCandidateError("false status promotion in evidence")
    revision=evidence.get("original_commit")
    if not isinstance(revision,str) or not HEX40.fullmatch(revision):
        raise SemanticCandidateError("missing original pinned revision")
    bound={}
    for item in evidence.get("declarations",[]):
        if not isinstance(item,dict):
            raise SemanticCandidateError("invalid checker declaration receipt")
        name=item.get("declaration")
        if not isinstance(name,str) or not name or name in bound:
            raise SemanticCandidateError("duplicate or invalid checker declaration")
        for key in ("source_sha256","native_export_sha256"):
            if (not isinstance(item.get(key),str) or
                not HEX64.fullmatch(item[key])):
                raise SemanticCandidateError("invalid bound "+key)
        bound[name]=item
    if not bound:
        raise SemanticCandidateError("no checked declarations")
    objects=[]
    for pathkey,digestkey in (
        ("candidate_source_world_path","candidate_source_world_sha256"),
        ("candidate_export_world_path","candidate_export_world_sha256")):
        relative=Path(evidence.get(pathkey,""))
        if (relative.is_symlink() or not relative.is_file() or
            relative.parent.resolve() != path.parent.resolve()):
            raise SemanticCandidateError("candidate file outside acceptance spool")
        actual=sha256(relative.read_bytes()).hexdigest()
        if evidence.get(digestkey)!=actual:
            raise SemanticCandidateError("candidate file hash mismatch")
        objects.append(relative)
    sources,exports=objects
    source_rows=list(jsonl(sources))
    export_rows=list(jsonl(exports))
    allowed={x["declaration"] for x in export_rows if isinstance(x,dict)}
    if allowed != set(bound) or len(export_rows)!=len(bound):
        raise SemanticCandidateError("original checker declarations mismatch candidate rows")
    original={x["path"]:x for x in source_rows
              if x.get("kind")=="world-source-occurrence"}
    if len(original)!=len(bound):
        raise SemanticCandidateError("source occurrence coverage mismatch")
    for row in export_rows:
        name=row["declaration"]
        checker=bound[name]
        if (row.get("repository")!=evidence.get("original_repository") or
            row.get("revision")!=revision or
            row.get("source_sha256")!=checker["source_sha256"] or
            row.get("native_export_sha256")!=checker["native_export_sha256"] or
            row.get("kind")!="lean-elaborated-export" or
            row.get("kernel_certified") is not False or
            row.get("world_admitted") is not False):
            raise SemanticCandidateError("unbound original export candidate")
        source=original.get(row.get("path"))
        if not source or source.get("sha256")!=row["source_sha256"]:
            raise SemanticCandidateError("unbound candidate source")
        try:
            canonical_bytes=base64.b64decode(row["canonical_type_b64"],validate=True)
        except (ValueError,KeyError) as exc:
            raise SemanticCandidateError("invalid candidate type bytes") from exc
        if not canonical_bytes or not HEX64.fullmatch(row.get("proof_digest","")):
            raise SemanticCandidateError("missing exact proof/type digest")
        for dependency in row.get("dependencies",[]):
            if (dependency.get("repository")!=evidence["original_repository"] or
                dependency.get("revision")!=revision or
                dependency.get("declaration") not in bound):
                raise SemanticCandidateError("unresolved selected original dependency")
    world,_=build(source_rows,export_rows)
    return world,evidence

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--acceptance-receipt",type=Path,required=True)
    p.add_argument("--schema",required=True)
    p.add_argument("--acknowledge-unverified-candidates",action="store_true")
    args=p.parse_args()
    if not args.acknowledge_unverified_candidates:
        p.error("explicit unverified-candidate acknowledgement required")
    if not os.environ.get("PGDATABASE"):
        p.error("explicit PGDATABASE required")
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]{0,62}",args.schema):
        p.error("invalid explicit schema name")
    try:
        import psycopg
        from psycopg import sql
        world,evidence=load_acceptance(args.acceptance_receipt)
        with psycopg.connect("") as conn:
            with conn.cursor() as cur:
                cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                    sql.Identifier(args.schema)))
                cur.execute("SELECT current_schema()")
                if cur.fetchone()[0]!=args.schema:
                    raise SemanticCandidateError("target schema not installed")
            conn.commit()
            result=persist_candidate_world(conn,world)
            with conn.cursor() as cur:
                original=list(sorted(world.occurrences))
                for item in original:
                    cur.execute("""
                        SELECT o.statement_id,f.foundation_profile,
                               f.type_head,f.universe_shape,c.status
                        FROM lean_world_occurrence o
                        JOIN lean_world_fibre f ON f.fibre_id=o.fibre_id
                        JOIN lean_world_candidate_receipt c
                          USING (repository,revision,declaration)
                        WHERE o.repository=%s AND o.revision=%s
                          AND o.declaration=%s
                    """,(item.repository,item.revision,item.declaration))
                    match=cur.fetchone()
                    if not match or match[4]!="candidate-unverified":
                        raise SemanticCandidateError("persisted candidate retrieval failed")
            conn.commit()
        result["source_bound_checker_observation"]=True
        result["retrieved_candidate_occurrences"]=len(world.occurrences)
        result["fibre_retrieved_as_candidate"]=True
        result["kernel_certified"]=False
        result["world_admitted"]=False
        print(json.dumps(result,sort_keys=True))
        return 0
    except (ValueError,OSError,KeyError,ImportError) as exc:
        p.exit(2,"SEMANTIC_CANDIDATE_PG_INCOMPLETE: "+str(exc)+"\n")

if __name__=="__main__":
    raise SystemExit(main())
