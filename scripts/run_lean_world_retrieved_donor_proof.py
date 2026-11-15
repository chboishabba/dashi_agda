#!/usr/bin/env python3
"""Retrieve candidate donor from PostgreSQL and elaborate the exact consumer.

This is an original SQL->Lean proof-reuse acceptance, not proof promotion.
The consumer must be byte-identical to the pinned #1495 independently checked
original, and the donor must have the exact original candidate statement bytes.
"""
from __future__ import annotations
from hashlib import sha256
import base64
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from run_lean_world_semantic_candidate_pg import load_acceptance

class RetrievalError(ValueError):
    pass

def compile_retrieved(conn, *, original_receipt: Path,
                      donor_file: Path, consumer_file: Path,
                      lean_executable: Path):
    _, evidence=load_acceptance(original_receipt)
    originals={item["declaration"]:item for item in evidence["declarations"]}
    donor_name="DASHIWorldSmoke.originalIdentity"
    consumer_name="DASHIWorldSmoke.consumerIdentity"
    if set(originals)!={donor_name,consumer_name}:
        raise RetrievalError("unexpected donor/consumer original identities")
    revision=evidence["original_commit"]
    repo=evidence["original_repository"]
    with conn.cursor() as cur:
        cur.execute("""
            SELECT o.statement_id,o.proof_term_digest,s.canonical_type,
                   c.status,c.source_sha256
            FROM lean_world_occurrence o
            JOIN lean_world_statement s ON s.statement_id=o.statement_id
            JOIN lean_world_fibre f ON f.fibre_id=o.fibre_id
            JOIN lean_world_candidate_receipt c
              USING (repository,revision,declaration)
            WHERE o.repository=%s AND o.revision=%s AND o.declaration=%s
        """,(repo,revision,donor_name))
        donor=cur.fetchone()
        if not donor or donor[3]!="candidate-unverified":
            raise RetrievalError("donor candidate absent or unexpectedly promoted")
        cur.execute("""
            SELECT o.statement_id,s.canonical_type,c.status
            FROM lean_world_occurrence o
            JOIN lean_world_statement s ON s.statement_id=o.statement_id
            JOIN lean_world_candidate_receipt c
              USING (repository,revision,declaration)
            WHERE o.repository=%s AND o.revision=%s AND o.declaration=%s
        """,(repo,revision,consumer_name))
        consumer=cur.fetchone()
        if not consumer or consumer[2]!="candidate-unverified":
            raise RetrievalError("consumer candidate missing")
        if donor[0]!=consumer[0] or bytes(donor[2])!=bytes(consumer[1]):
            raise RetrievalError("original donor/consumer theorem types differ")
    donor_source=Path(donor_file).read_bytes()
    expected_donor_sha=originals[donor_name]["source_sha256"]
    if sha256(donor_source).hexdigest()!=expected_donor_sha:
        raise RetrievalError("donor original bytes changed")
    generated=(
        "import Donor\n"
        "namespace DASHIWorldSmoke\n"
        "theorem consumerIdentity (p : Prop) : p → p := by\n"
        "  exact _root_."+donor_name+" p\n"
        "#print axioms DASHIWorldSmoke.consumerIdentity\n"
        "end DASHIWorldSmoke\n"
    ).encode()
    original_consumer=Path(consumer_file).read_bytes()
    if (generated!=original_consumer or
        sha256(generated).hexdigest()!=originals[consumer_name]["source_sha256"]):
        raise RetrievalError("SQL-reconstructed consumer differs from checked source")
    lean=Path(lean_executable).resolve(strict=True)
    if not lean.is_file() or not os.access(lean,os.X_OK):
        raise RetrievalError("missing pinned Lean executable")
    version=subprocess.run([str(lean),"--version"],capture_output=True,
                           timeout=20,check=False)
    if version.returncode or b"4.28.0" not in version.stdout:
        raise RetrievalError("wrong pinned Lean version")
    env={k:os.environ[k] for k in (
        "PATH","HOME","LANG","LC_ALL","LEAN_SYSROOT","LEAN_PATH") if k in os.environ}
    with tempfile.TemporaryDirectory(prefix="dashi-retrieved-") as temp:
        directory=Path(temp)
        (directory/"Donor.lean").write_bytes(donor_source)
        (directory/"Consumer.lean").write_bytes(generated)
        env["LEAN_PATH"]=str(directory)+(os.pathsep+env["LEAN_PATH"]
                        if env.get("LEAN_PATH") else "")
        compiled=[]
        for module in ("Donor","Consumer"):
            result=subprocess.run(
                [str(lean),"-o",module+".olean",module+".lean"],
                cwd=directory,env=env,stdin=subprocess.DEVNULL,
                capture_output=True,timeout=180,check=False)
            file=directory/(module+".olean")
            if result.returncode or not file.is_file():
                raise RetrievalError("retrieved original "+module+
                                     " proof elaboration failed")
            compiled.append(sha256(file.read_bytes()).hexdigest())
    return {
        "schema":"dashi-lean-retrieved-donor-consumer-observation-v1",
        "status":"candidate-donor-retrieved-second-proof-lean-checked",
        "original_repository":repo,"original_revision":revision,
        "donor":donor_name,"consumer":consumer_name,
        "donor_statement_id":donor[0],
        "donor_original_source_sha256":expected_donor_sha,
        "consumer_original_source_sha256":sha256(generated).hexdigest(),
        "donor_olean_sha256":compiled[0],
        "consumer_olean_sha256":compiled[1],
        "lean_binary_sha256":sha256(lean.read_bytes()).hexdigest(),
        "external_acceptance_receipt_sha256":
            sha256(Path(original_receipt).read_bytes()).hexdigest(),
        "candidate_fibre_retrieved":True,
        "consumer_lean_elaborated":True,
        "independent_checker_run_in_this_step":False,
        "world_admitted":False,
        "kernel_certified":False
    }

def main():
    import argparse
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--acceptance-receipt",required=True,type=Path)
    p.add_argument("--schema",required=True)
    p.add_argument("--donor-source",required=True,type=Path)
    p.add_argument("--consumer-source",required=True,type=Path)
    p.add_argument("--lean",required=True,type=Path)
    p.add_argument("--output-dir",required=True,type=Path)
    args=p.parse_args()
    if not os.environ.get("PGDATABASE"):
        p.error("explicit PGDATABASE required")
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]{0,62}",args.schema):
        p.error("invalid explicit schema")
    try:
        import psycopg
        from psycopg import sql
        with psycopg.connect("") as conn:
            with conn.cursor() as cur:
                cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                    sql.Identifier(args.schema)))
                cur.execute("SELECT current_schema()")
                if cur.fetchone()[0]!=args.schema:
                    raise RetrievalError("unknown explicit schema")
            conn.commit()
            report=compile_retrieved(
                conn,original_receipt=args.acceptance_receipt,
                donor_file=args.donor_source,consumer_file=args.consumer_source,
                lean_executable=args.lean)
        dest=args.output_dir.resolve()
        dest.mkdir(parents=True,exist_ok=True)
        data=(json.dumps(report,sort_keys=True,separators=(",",":"))+"\n").encode()
        output=dest/(sha256(data).hexdigest()+".retrieved-proof-observation.json")
        # Immutable POSIX publication using same checked pattern as #1495.
        if output.exists():
            if output.is_symlink() or output.read_bytes()!=data:
                raise RetrievalError("conflicting retrieved proof receipt")
        else:
            import tempfile
            with tempfile.NamedTemporaryFile(dir=dest,delete=False) as tmp:
                tmp.write(data);tmp.flush();os.fsync(tmp.fileno())
                private=Path(tmp.name)
            try:
                os.link(private,output)
            finally:
                private.unlink(missing_ok=True)
        print(json.dumps({"status":report["status"],"receipt":str(output),
                          "world_admitted":False,"kernel_certified":False},
                         sort_keys=True))
        return 0
    except (ValueError,OSError,ImportError,subprocess.TimeoutExpired) as exc:
        p.exit(2,"RETRIEVED_PROOF_INCOMPLETE: "+str(exc)+"\n")

if __name__=="__main__":
    raise SystemExit(main())
