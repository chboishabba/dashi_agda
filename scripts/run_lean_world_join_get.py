#!/usr/bin/env python3
"""Restore complete original compiled theorem-join closure from PostgreSQL.

Optionally compile a SECOND Lean theorem batch referencing the retrieved
DASHIJoined proofs, without rebuilding any source or downloading a repository.
This is genuine Lean source/proof reuse, not independent verification.
"""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys

from run_lean_world_stream_pg import SCHEMA_RE
from lean_world_compiled_join_store import (
    fetch_join,join_metadata,iter_original_module_oleans)
from run_lean_world_join_proofs import (
    generate_joins,run_compiler,path_for_module,JoinError)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--schema",required=True)
    p.add_argument("--batch",required=True,help="original compiled join batch SHA256")
    p.add_argument("--output-dir",required=True,type=Path)
    p.add_argument("--lean",type=Path,
                   help="same pinned Lean binary; recompile retrieved theorem proof")
    p.add_argument("--reuse-count",type=int,default=0)
    args=p.parse_args()
    if not SCHEMA_RE.fullmatch(args.schema) or args.schema=="public":
        p.error("dedicated original SQL schema required")
    if not os.environ.get("PGDATABASE"):
        p.error("explicit PGDATABASE is required")
    if args.reuse_count<0 or (args.reuse_count and args.lean is None):
        p.error("--reuse-count requires --lean")
    try:
        import psycopg
        from psycopg import sql
        directory=args.output_dir.resolve()
        if directory.exists() or directory.is_symlink():
            raise ValueError("choose a NEW output directory for original proof readback")
        with psycopg.connect("") as conn:
            with conn.cursor() as cur:
                cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                    sql.Identifier(args.schema)))
                cur.execute("SELECT current_schema()")
                if cur.fetchone()[0]!=args.schema:
                    raise ValueError("original world schema does not exist")
            conn.commit()
            meta=join_metadata(conn,args.batch)
            if args.reuse_count>meta["joined_theorems"]:
                raise ValueError("requested more theorem joins than stored")
            compiler=None
            if args.lean is not None:
                compiler=args.lean.resolve(strict=True)
                if sha256(compiler.read_bytes()).hexdigest()!=meta["lean_binary_sha256"]:
                    raise ValueError("must reuse identical pinned Lean compiler")
            source,olean=fetch_join(conn,args.batch)
            directory.mkdir(parents=True,exist_ok=False)
            module_count=0
            for module,raw in iter_original_module_oleans(conn,args.batch):
                file=directory/path_for_module(module).replace(".lean",".olean")
                file.parent.mkdir(parents=True,exist_ok=True)
                with file.open("xb") as output:
                    output.write(raw)
                    output.flush()
                    os.fsync(output.fileno())
                module_count+=1
            if module_count!=meta["module_count"]:
                raise ValueError("original compiled module closure truncated")
        for name,raw in (
            ("DASHIJoinBatch.lean",source),
            ("DASHIJoinBatch.olean",olean)):
            with (directory/name).open("xb") as output:
                output.write(raw)
                output.flush()
                os.fsync(output.fileno())
        reused=None
        if args.reuse_count:
            donors=["DASHIJoined.join"+str(i)
                    for i in range(args.reuse_count)]
            new_source=generate_joins(
                "DASHIJoinBatch",donors,
                join_namespace="DASHIFromStored")
            (directory/"DASHIProofReuse.lean").write_bytes(new_source)
            env={k:os.environ[k] for k in (
                "PATH","HOME","LANG","LC_ALL","LEAN_SYSROOT","LEAN_PATH")
                if k in os.environ}
            env["LEAN_PATH"]=str(directory)+(
                os.pathsep+env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
            digest,result=run_compiler(
                compiler,directory,"DASHIProofReuse.lean",
                environment=env,timeout=600)
            output_text=result.stdout.decode("utf-8","replace")
            for i in range(args.reuse_count):
                if "DASHIFromStored.join"+str(i) not in output_text:
                    raise JoinError("reused imported theorem not checked by Lean")
            if args.reuse_count>=2 and "DASHIFromStored.combined" not in output_text:
                raise JoinError("reused multi-theorem composition not checked by Lean")
            reused={"joined_theorems":args.reuse_count,
                    "consumer_olean_sha256":digest,
                    "consumer_source_sha256":sha256(new_source).hexdigest(),
                    "lean_compilation_succeeded":True,
                    "genuinely_composed_from_retrieved_proofs":args.reuse_count>=2,
                    "axiom_report":output_text[-8000:]}
        print(json.dumps({
            "status":"original-joined-lean-proof-closure-retrieved",
            "batch_sha256":args.batch,"directory":str(directory),
            "original_module_oleans":module_count,
            "join_source_sha256":sha256(source).hexdigest(),
            "join_olean_sha256":sha256(olean).hexdigest(),
            "retrieved_consumer_proof":reused,
            "independently_checked":False,
            "world_admitted":False
        },sort_keys=True))
        return 0
    except (OSError,ValueError,ImportError,subprocess.TimeoutExpired) as exc:
        print("ORIGINAL_PROOF_REUSE_INCOMPLETE: "+str(exc),file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
