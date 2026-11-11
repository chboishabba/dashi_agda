#!/usr/bin/env python3
"""Join MANY existing Lean theorems from original PostgreSQL source bytes.

This is source-original, import-closed Lean proof reuse, not a Rust checker,
a source regex converted to a theorem, or certified world/Agda identity.

One selected root module is fetched from the immutable PostgreSQL source
archive with its recursive same-revision imports.  Each exact source is
rehashed by retrieve_source; only missing Lean-builtins are external.
The entire closure is compiled with a pinned Lean compiler; an additional
generated Lean module then registers independently typechecked theorem
aliases whose values are direct references to original donor theorems.
"""
from __future__ import annotations
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

from lean_world_stream_pg import retrieve_source,SCHEMA_RE
from lean_remote_archive_stream import REPO_RE,COMMIT_RE

# Imports are a discovery plan only. Lean, not this regex, resolves the
# actual compiled import closure and checks proof identities.
IMPORT=re.compile(r"^\s*(?:(?:public|private|meta)\s+)?import\s+([A-Za-z_][\w.]*)(?:\s+([A-Za-z_][\w.]*))*\s*$")
MODULE=re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")
BUILTINS=("Lean.","Init.","Std.")
DEFAULT_MODULE_CAP=128
DEFAULT_SOURCE_CAP=64*1024*1024

class JoinError(ValueError): pass

def names_from_import_line(line):
    # Lean permits multiple modules after a single import keyword.
    match=re.match(r"^\s*(?:(?:public|private|meta)\s+)?import\s+(.+?)\s*$",line)
    if not match:
        return ()
    value=match.group(1).split("--",1)[0].strip()
    tokens=value.split()
    if any(not MODULE.fullmatch(item) for item in tokens):
        raise JoinError("unsupported import statement; cannot assume closure")
    return tuple(tokens)

def parse_imports(raw):
    try:
        text=raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise JoinError("Lean source is not valid UTF-8") from exc
    return tuple(dict.fromkeys(
        imp for line in text.splitlines()
        for imp in names_from_import_line(line)))

def path_for_module(module):
    if not MODULE.fullmatch(module):
        raise JoinError("invalid original module name: "+module)
    return module.replace(".","/")+".lean"

def plan_from_pg(conn,repository,revision,roots,*,max_modules=DEFAULT_MODULE_CAP,
                 max_source_bytes=DEFAULT_SOURCE_CAP,external_prefixes=BUILTINS):
    """Original source-byte import DAG, deterministic topological order."""
    if not REPO_RE.fullmatch(repository) or not COMMIT_RE.fullmatch(revision):
        raise JoinError("requires original immutable repository/revision")
    if not roots or any(not MODULE.fullmatch(x) for x in roots):
        raise JoinError("nonempty original module roots required")
    if not 1<=max_modules<=2048 or not 1<=max_source_bytes<=256*1024*1024:
        raise JoinError("invalid compilation resource caps")
    complete={}
    with conn.cursor() as cur:
        cur.execute("""
            SELECT source_count FROM lean_world_source_archive
            WHERE repository=%s AND revision=%s
              AND status='source-complete-not-elaborated'
        """,(repository,revision))
        if cur.fetchone() is None:
            raise JoinError("pinned original source archive not complete")
        cur.execute("""
            SELECT path FROM lean_world_source_occurrence
            WHERE repository=%s AND revision=%s
        """,(repository,revision))
        complete={p for (p,) in cur}
    if len(complete)>1_000_000:
        raise JoinError("unbounded original source index")
    source={}
    edges={}
    visited=set()
    active=set()
    order=[]
    missing=set()
    total=0
    stack=[(root,False) for root in reversed(roots)]
    while stack:
        mod,leaving=stack.pop()
        if leaving:
            active.remove(mod)
            visited.add(mod)
            order.append(mod)
            continue
        if mod in visited:continue
        if mod in active:raise JoinError("cycle in selected module import closure")
        p=path_for_module(mod)
        if p not in complete:
            if mod.startswith(external_prefixes) or mod in ("Init","Lean","Std"):
                missing.add(mod)
                visited.add(mod)
                continue
            raise JoinError("missing same-revision source dependency: "+mod)
        if len(source)>=max_modules:
            raise JoinError("source module budget exceeded")
        raw=retrieve_source(conn,repository,revision,p)
        total+=len(raw)
        if total>max_source_bytes:
            raise JoinError("original source-byte budget exceeded")
        source[mod]=raw
        deps=parse_imports(raw)
        edges[mod]=deps
        active.add(mod)
        stack.append((mod,True))
        for dep in reversed(deps):
            if dep in active:raise JoinError("cycle in source import closure")
            if dep not in visited:
                stack.append((dep,False))
    return {
        "source":source,"order":order,"edges":edges,
        "external_imports":tuple(sorted(missing)),
        "total_source_bytes":total,
        "root_modules":tuple(roots)
    }

def lean_name(name):
    if not MODULE.fullmatch(name):
        raise JoinError("invalid declaration: "+name)
    return "`"+name

def generate_joins(root_module,donors):
    """Lean elaboration constructs actual kernel-checked theorem declarations.

    Theorem type/universes are taken from the ORIGINAL imported environment;
    the proof is a direct Expr.const pointing to that donor. No assumptions
    about textual signatures, rewrite equivalence or reduced normal forms.
    """
    if not MODULE.fullmatch(root_module):
        raise JoinError("invalid root")
    if not donors or len(donors)>256 or len(set(donors))!=len(donors):
        raise JoinError("invalid selected donor set")
    lines=[
        "import "+root_module,
        "import Lean",
        "open Lean Elab Command",
        "",
    ]
    for i,donor in enumerate(donors):
        if not MODULE.fullmatch(donor):raise JoinError("invalid donor theorem name")
        alias="DASHIJoined.join"+str(i)
        lines.extend([
            "run_cmd do",
            "  let donor : Name := "+lean_name(donor),
            "  let some (.thmInfo info) := (← getEnv).find? donor",
            "    | throwError \"expected original theorem, not axiom/definition: {donor}\"",
            "  let levels := info.levelParams.map Level.param",
            "  let proof := mkConst donor levels",
            "  addDecl <| Declaration.thmDecl {",
            "    name := "+lean_name(alias)+",",
            "    levelParams := info.levelParams,",
            "    type := info.type,",
            "    value := proof",
            "  }",
            "#check "+alias,
            "#print axioms "+alias,
            ""
        ])
    return ("\n".join(lines)+"\n").encode()

def run_compiler(lean,root,relative,*,environment,timeout):
    result=subprocess.run(
        [str(lean),"-o",str(Path(relative).with_suffix(".olean")),relative],
        cwd=root,env=environment,capture_output=True,
        stdin=subprocess.DEVNULL,timeout=timeout,check=False)
    if result.returncode:
        raise JoinError(
            "Lean rejected "+relative+
            " exit="+str(result.returncode)+
            " stderr="+result.stderr.decode("utf-8","replace")[-5000:]+
            " stdout="+result.stdout.decode("utf-8","replace")[-5000:])
    output=root/Path(relative).with_suffix(".olean")
    if not output.is_file():
        raise JoinError("Lean returned zero without compiled output: "+relative)
    return sha256(output.read_bytes()).hexdigest(),result

def compile_and_join(plan,lean,donors,*,timeout=180,max_build_seconds=3600):
    compiler=Path(lean).resolve(strict=True)
    if not compiler.is_file():
        raise JoinError("pinned Lean executable unavailable")
    version=subprocess.run([str(compiler),"--version"],
                           capture_output=True,timeout=15,check=False)
    if version.returncode:
        raise JoinError("Lean version probe failed")
    version_text=version.stdout.decode("utf-8","replace").strip()
    if "4.28.0" not in version_text:
        raise JoinError("Lean 4.28.0 required; do not silently recompile under later Lean")
    if not 1<=timeout<=1800:
        raise JoinError("invalid per-module timeout")
    with tempfile.TemporaryDirectory(prefix="dashi-original-proof-join-") as tmp:
        root=Path(tmp)
        env={k:os.environ[k] for k in (
            "PATH","HOME","LANG","LC_ALL","LEAN_SYSROOT","LEAN_PATH",
            "NIX_LD","NIX_LD_LIBRARY_PATH") if k in os.environ}
        env["LEAN_PATH"]=str(root)+(os.pathsep+env["LEAN_PATH"]
                                   if env.get("LEAN_PATH") else "")
        for module,raw in plan["source"].items():
            file=root/path_for_module(module)
            file.parent.mkdir(parents=True,exist_ok=True)
            file.write_bytes(raw)
        module_receipts=[]
        for module in plan["order"]:
            if module not in plan["source"]:continue
            path=path_for_module(module)
            digest,_=run_compiler(compiler,root,path,
                                  environment=env,timeout=timeout)
            module_receipts.append({
                "module":module,"path":path,
                "source_sha256":sha256(plan["source"][module]).hexdigest(),
                "olean_sha256":digest,
                "direct_imports":list(plan["edges"][module])
            })
        generated=generate_joins(plan["root_modules"][-1],donors)
        (root/"DASHIJoinBatch.lean").write_bytes(generated)
        joined_digest,output=run_compiler(
            compiler,root,"DASHIJoinBatch.lean",
            environment=env,timeout=timeout)
        output_text=output.stdout.decode("utf-8","replace")
        for i in range(len(donors)):
            if "DASHIJoined.join"+str(i) not in output_text:
                raise JoinError("missing original theorem check output")
        return {
            "status":"original-lean-theorem-joins-compiled",
            "lean_version":version_text,
            "lean_binary_sha256":sha256(compiler.read_bytes()).hexdigest(),
            "module_count":len(module_receipts),
            "external_imports":list(plan["external_imports"]),
            "original_source_bytes":plan["total_source_bytes"],
            "compiled_modules":module_receipts,
            "donor_names":list(donors),
            "generated_join_source_sha256":sha256(generated).hexdigest(),
            "joined_olean_sha256":joined_digest,
            "joined_axiom_report":output_text[-12000:],
            "original_lean_compiled":True,
            "generated_lean_proof_references_checked":True,
            "independently_checked":False,
            "world_admitted":False
        }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--schema",required=True)
    p.add_argument("--repository",required=True)
    p.add_argument("--revision",required=True)
    p.add_argument("--module",required=True)
    p.add_argument("--donor",action="append",required=True,
                   help="full original theorem declaration name; repeat")
    p.add_argument("--lean",type=Path,required=True)
    p.add_argument("--max-modules",type=int,default=DEFAULT_MODULE_CAP)
    p.add_argument("--max-source-bytes",type=int,default=DEFAULT_SOURCE_CAP)
    p.add_argument("--timeout",type=int,default=180)
    p.add_argument("--output",type=Path,required=True)
    args=p.parse_args()
    if not SCHEMA_RE.fullmatch(args.schema) or args.schema=="public":
        p.error("dedicated explicit source-world schema required")
    if not os.environ.get("PGDATABASE"):
        p.error("PGDATABASE must be explicit")
    try:
        import psycopg
        from psycopg import sql
        with psycopg.connect("") as conn:
            with conn.cursor() as cur:
                cur.execute(sql.SQL("SET search_path TO {},pg_catalog").format(
                    sql.Identifier(args.schema)))
                cur.execute("SELECT current_schema()")
                if cur.fetchone()[0]!=args.schema:
                    raise JoinError("source world schema missing")
            conn.commit()
            plan=plan_from_pg(
                conn,args.repository,args.revision,[args.module],
                max_modules=args.max_modules,
                max_source_bytes=args.max_source_bytes)
        result=compile_and_join(plan,args.lean,args.donor,timeout=args.timeout)
        result["repository"]=args.repository
        result["revision"]=args.revision
        output=args.output.resolve()
        output.parent.mkdir(parents=True,exist_ok=True)
        if output.exists() or output.is_symlink():
            raise JoinError("refusing to overwrite existing proof join receipt")
        with output.open("x",encoding="utf-8") as f:
            json.dump(result,f,sort_keys=True,indent=2)
            f.write("\n")
        print(json.dumps({
            "status":result["status"],
            "compiled_modules":result["module_count"],
            "joined_theorems":len(result["donor_names"]),
            "receipt":str(output),
            "original_lean_compiled":True,
            "independently_checked":False,
            "world_admitted":False},sort_keys=True))
        return 0
    except (OSError,ValueError,ImportError,subprocess.TimeoutExpired) as exc:
        print("ORIGINAL_PROOF_JOIN_INCOMPLETE: "+str(exc),file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
