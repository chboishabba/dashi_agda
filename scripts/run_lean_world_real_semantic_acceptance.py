#!/usr/bin/env python3
"""Pinned Lean 4.28 donor/consumer -> lean4export -> Rust nanoda acceptance.

This script is intentionally LOCAL, explicit and fail-closed: temporary tool
checkouts, no CI/Docker, no world DB mutation, no proof-status promotion by a
Python parser. A successful run records independent checker observations,
including a negative-control rejection. It does not claim fibre retrieval.
"""
from __future__ import annotations
from hashlib import sha256, sha1
from pathlib import Path
import argparse
import base64
import json
import os
import shutil
import subprocess
import tempfile

EXPORTER_SHA = "d065b0009aed0520e9e99752847a33b337661690"
NANODA_SHA = "418320295890faed83a96fd97907b12a3b6728c2"
FIXTURES = Path(__file__).resolve().parents[1] / "tests/fixtures/lean_world_semantic"

class AcceptanceError(ValueError):
    pass

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def command(args, *, cwd=None, env=None, timeout=600, expect_success=True):
    completed = subprocess.run(
        [str(x) for x in args],cwd=cwd,env=env,
        stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,timeout=timeout,check=False)
    if expect_success and completed.returncode:
        raise AcceptanceError(
            "command failed: "+str(args[0])+
            " stderr_sha256="+sha256(completed.stderr).hexdigest())
    return completed

def clone_tag(root, name, url, tag, expected):
    target=root/name
    command(["git","clone","--quiet","--filter=blob:none","--depth","1",
             "--branch",tag,url,str(target)],timeout=600)
    actual=command(["git","rev-parse","HEAD"],cwd=target).stdout.decode().strip()
    if actual != expected:
        raise AcceptanceError(name+" upstream source revision mismatch")
    return target

def require_tool(name):
    found=shutil.which(name)
    if not found: raise AcceptanceError("missing required executable: "+name)
    return Path(found).resolve()

def nanoda_policy():
    """Strict explicit axiom policy: no sorryAx and no permit-all escape."""
    return {
        "num_threads": 1,
        "stack_size_bytes": 67108864,
        "permitted_axioms": [
            "propext", "Classical.choice", "Quot.sound",
            "Lean.trustCompiler"],
        "unpermitted_axiom_hard_error": False,
        "unsafe_permit_all_axioms": False,
        "nat_extension": True,
        "string_extension": True,
        "print_success_message": True,
    }


def check_nanoda(binary, export, *, config_dir, env, timeout,
                 expect_success=True):
    """Run Rust nanoda against a precise file under a strict axiom policy."""
    cfg=nanoda_policy()
    cfg["export_file_path"]=str(Path(export).resolve())
    cfg["use_stdin"]=False
    cfg_path=Path(config_dir)/("nanoda-"+sha256(
        str(Path(export).resolve()).encode()).hexdigest()[:16]+".json")
    cfg_path.write_text(json.dumps(cfg,sort_keys=True),encoding="utf-8")
    return command([binary,cfg_path],env=env,timeout=timeout,
                   expect_success=expect_success)


def replace_theorem_proof_with_type(raw):
    """Keep NDJSON structurally valid; make one actual theorem ill-typed."""
    rows=[json.loads(line) for line in raw.splitlines()]
    for row in reversed(rows):
        thm=row.get("thm")
        if isinstance(thm,dict) and type(thm.get("type")) is int and (
                type(thm.get("value")) is int and
                thm["value"]!=thm["type"]):
            thm["value"]=thm["type"]
            return ("\n".join(json.dumps(row,separators=(",",":"))
                              for row in rows)+"\n").encode()
    raise AcceptanceError("cannot construct substantive invalid proof control")


def main_run(output_dir: Path, *, timeout=600):
    output_dir=Path(output_dir).resolve()
    lean=require_tool("lean")
    lake=require_tool("lake")
    cargo=require_tool("cargo")
    require_tool("rustc")
    require_tool("git")
    version=command([lean,"--version"]).stdout.decode("utf-8","replace").strip()
    cargo_version=command([cargo,"--version"]).stdout.decode().strip()
    if "Lean (version 4.28.0" not in version and "Lean 4.28.0" not in version:
        raise AcceptanceError("Lean version not the required pinned 4.28.0")
    if not cargo_version.startswith("cargo "):
        raise AcceptanceError("pinned Rust build requires Cargo")
    gitroot=Path(__file__).resolve().parents[1]
    original_commit=command(["git","rev-parse","HEAD"],cwd=gitroot).stdout.decode().strip()
    if len(original_commit)!=40:
        raise AcceptanceError("missing complete original repository commit")
    for file in ("Donor.lean","Consumer.lean"):
        path="tests/fixtures/lean_world_semantic/"+file
        pinned=command(["git","show","HEAD:"+path],cwd=gitroot).stdout
        if pinned != (FIXTURES/file).read_bytes():
            raise AcceptanceError("fixture differs from committed original: "+path)
    if not 1<=timeout<=3600:
        raise AcceptanceError("invalid checker timeout")
    with tempfile.TemporaryDirectory(prefix="dashi-semantic-") as temp:
        root=Path(temp)
        exporter=clone_tag(root,"exporter",
           "https://github.com/leanprover/lean4export.git","v4.28.0",EXPORTER_SHA)
        nanoda=root/"nanoda"
        command(["git","clone","--quiet","--filter=blob:none","--no-checkout",
                 "https://github.com/ammkrn/nanoda_lib.git",str(nanoda)],
                timeout=600)
        command(["git","fetch","--quiet","--depth","1","origin",NANODA_SHA],
                cwd=nanoda,timeout=600)
        command(["git","checkout","--quiet","--detach",NANODA_SHA],cwd=nanoda)
        actual=command(["git","rev-parse","HEAD"],cwd=nanoda).stdout.decode().strip()
        if actual!=NANODA_SHA:
            raise AcceptanceError("nanoda original source revision mismatch")
        command([lake,"build","lean4export"],cwd=exporter,timeout=1200)
        exporter_binary=exporter/".lake/build/bin/lean4export"
        if not exporter_binary.is_file():
            raise AcceptanceError("pinned exporter build produced no binary")
        command([cargo,"build","--release","--locked","--bin","nanoda_bin"],
                cwd=nanoda,timeout=1200)
        checker_binary=nanoda/"target/release/nanoda_bin"
        if not checker_binary.is_file():
            raise AcceptanceError("pinned Rust checker build produced no binary")
        original=root/"original"
        original.mkdir()
        env={k:os.environ[k] for k in (
            "PATH","HOME","LANG","LC_ALL","LEAN_PATH","LEAN_SYSROOT",
            "NIX_LD","NIX_LD_LIBRARY_PATH") if k in os.environ}
        env["LEAN_PATH"]=str(original)+(os.pathsep+env["LEAN_PATH"]
                    if env.get("LEAN_PATH") else "")
        for file in ("Donor.lean","Consumer.lean"):
            shutil.copyfile(FIXTURES/file,original/file)
        reports=[]
        projected={}
        for module, theorem in (
            ("Donor","DASHIWorldSmoke.originalIdentity"),
            ("Consumer","DASHIWorldSmoke.consumerIdentity")):
            checked=command([lean,"-o",module+".olean",module+".lean"],
                            cwd=original,env=env,timeout=timeout)
            compiled=original/(module+".olean")
            if not compiled.is_file():
                raise AcceptanceError("Lean compilation did not emit "+module+".olean")
            export=original/(module+".ndjson")
            with export.open("wb") as sink:
                proc=subprocess.run([str(exporter_binary),module,"--",theorem],
                    cwd=original,env=env,stdout=sink,stderr=subprocess.PIPE,
                    stdin=subprocess.DEVNULL,timeout=timeout,check=False)
            if proc.returncode or not export.stat().st_size:
                raise AcceptanceError(
                    "pinned exporter failed for "+module+
                    " stderr_sha256="+sha256(proc.stderr).hexdigest())
            # Checkers must explicitly reject sorryAx and return zero.
            independent=check_nanoda(checker_binary,export,
                                     config_dir=root,env=env,timeout=timeout)
            if b"Checked " not in independent.stdout or b" no errors" not in independent.stdout:
                raise AcceptanceError("nanoda gave no explicit successful check for "+module)
            from lean_world_native_v3_projection import extract_candidates
            candidate, = extract_candidates(
                export.read_bytes(), selected_names=frozenset((theorem,)))
            if candidate.name != theorem or not candidate.proof_value_present:
                raise AcceptanceError("selected original proof not structurally projected")
            projected[theorem]=(module,candidate)
            reports.append({
                "module":module,"declaration":theorem,
                "source_sha256":digest(original/(module+".lean")),
                "olean_sha256":digest(compiled),
                "native_export_sha256":digest(export),
                "native_export_bytes":export.stat().st_size,
                "checker_stdout_sha256":sha256(independent.stdout).hexdigest(),
                "checker_stderr_sha256":sha256(independent.stderr).hexdigest(),
                "lean_stdout_sha256":sha256(checked.stdout).hexdigest()})
        # Genuine semantic negative control: preserve valid native-v3 syntax
        # and replace a theorem proof with its own TYPE expression. This
        # creates a well-formed export whose proof is ill-typed.
        donor_export=(original/"Donor.ndjson").read_bytes()
        bad_export=replace_theorem_proof_with_type(donor_export)
        bad_path=root/"invalid-proof.ndjson"
        bad_path.write_bytes(bad_export)
        rejection=check_nanoda(checker_binary,bad_path,
                               config_dir=root,env=env,
                               timeout=timeout,expect_success=False)
        if rejection.returncode == 0:
            raise AcceptanceError("nanoda accepted ill-typed theorem negative control")
        # Create candidate-only #1484 compatible originals iff all direct
        # type/proof constants are defined within this selected two-module
        # dependency set. Otherwise publish no misleading complete DAG rows.
        selected=set(projected)
        unresolved={theorem:sorted(
            (set(c.direct_constants)|set(c.proof_direct_constants))-selected)
            for theorem,(_,c) in projected.items()}
        if any(unresolved.values()):
            raise AcceptanceError("selected proof has unresolved original dependencies: "+
                                  json.dumps(unresolved,sort_keys=True))
        source_rows=[]
        export_rows=[]
        for theorem,(module,c) in projected.items():
            source_bytes=(FIXTURES/(module+".lean")).read_bytes()
            original_path="tests/fixtures/lean_world_semantic/"+module+".lean"
            source_rows.append({
                "kind":"world-source-occurrence",
                "status":"source-verified-not-elaborated",
                "repository":"chboishabba/dashi_agda",
                "revision":original_commit,"path":original_path,
                "sha256":sha256(source_bytes).hexdigest(),
                "size":len(source_bytes),
                "git_blob":sha1(b"blob "+str(len(source_bytes)).encode()+
                                b"\0"+source_bytes).hexdigest()
            })
            type_node=json.loads(c.canonical_type.decode("utf-8"))
            dependency_names=(set(c.direct_constants)|
                              set(c.proof_direct_constants))-{theorem}
            export_rows.append({
                "kind":"lean-elaborated-export",
                "repository":"chboishabba/dashi_agda",
                "revision":original_commit,"path":original_path,
                "declaration":theorem,
                "source_sha256":sha256(source_bytes).hexdigest(),
                "proof_digest":c.proof_digest,
                "profile":"lean4-4.28.0-exporter-"+EXPORTER_SHA[:12]+
                          "-nanoda-"+NANODA_SHA[:12],
                "type_head":type_node[2],
                "universe_shape":json.dumps(type_node[1],separators=(",",":")),
                "canonical_type_b64":base64.b64encode(c.canonical_type).decode(),
                "exporter_profile":"lean4export-3x-independent-nanoda-check-observed",
                "attribution":"DASHI original Lean fixture",
                "dependencies":[{
                    "repository":"chboishabba/dashi_agda",
                    "revision":original_commit,"declaration":name
                } for name in sorted(dependency_names)],
                "native_export_sha256":next(r["native_export_sha256"]
                            for r in reports if r["declaration"]==theorem),
                "independent_checker_observed":True,
                "kernel_certified":False,
                "world_admitted":False
            })
        source_rows.append({
            "kind":"world-source-intake-summary",
            "repository":"chboishabba/dashi_agda",
            "revision":original_commit,
            "source_complete":True,"skipped_sources":0,
            "admitted_source_occurrences":len(source_rows)
        })
        source_payload=("".join(json.dumps(x,sort_keys=True)+"\n"
                              for x in source_rows)).encode()
        export_payload=("".join(json.dumps(x,sort_keys=True)+"\n"
                              for x in export_rows)).encode()
        output_dir.mkdir(parents=True,exist_ok=True)
        from lean_world_atomic_spool import publish_immutable
        source_path=output_dir/(sha256(source_payload).hexdigest()+
                                ".source-world.jsonl")
        export_path=output_dir/(sha256(export_payload).hexdigest()+
                                ".candidate-world.jsonl")
        publish_immutable(source_path,source_payload)
        publish_immutable(export_path,export_payload)
        receipt={
            "schema":"dashi-lean-real-independent-semantic-acceptance-v1",
            "status":"independent-checker-observed-two-module-reuse",
            "original_repository":"chboishabba/dashi_agda",
            "original_commit":original_commit,
            "lean_version":version,
            "lean_binary_sha256":digest(lean),
            "rust_cargo_version":cargo_version,
            "exporter_source_sha":EXPORTER_SHA,
            "exporter_executable_sha256":digest(exporter_binary),
            "checker_kind":"rust-nanoda",
            "checker_source_sha":NANODA_SHA,
            "checker_binary_sha256":digest(checker_binary),
            "checker_policy":nanoda_policy(),
            "declarations":reports,
            "candidate_source_world_path":str(source_path),
            "candidate_source_world_sha256":sha256(source_payload).hexdigest(),
            "candidate_export_world_path":str(export_path),
            "candidate_export_world_sha256":sha256(export_payload).hexdigest(),
            "invalid_fixture_name":"ill-typed-original-theorem-proof",
            "invalid_fixture_sha256":digest(bad_path),
            "invalid_fixture_rejected":True,
            "second_lean_elaboration_succeeded":True,
            "independent_checker_observed":True,
            "native_to_canonical_semantic_equality_checked":False,
            "fibre_retrieved":False,
            "postgres_world_admitted":False
        }
        payload=(json.dumps(receipt,sort_keys=True,separators=(",",":"))+"\n").encode()
        output_dir.mkdir(parents=True,exist_ok=True)
        # Immutable publication reuses #1495's tested POSIX no-clobber code.
        from lean_world_atomic_spool import publish_immutable
        path=output_dir/(sha256(payload).hexdigest()+".semantic-acceptance.json")
        publish_immutable(path,payload)
        return {"status":receipt["status"],"receipt":str(path),
                "receipt_sha256":sha256(payload).hexdigest(),
                "independent_checker_observed":True,
                "fibre_retrieved":False,"postgres_world_admitted":False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output-dir",required=True,type=Path)
    p.add_argument("--timeout",default=600,type=int)
    args=p.parse_args()
    try:
        print(json.dumps(main_run(args.output_dir,timeout=args.timeout),sort_keys=True))
    except (OSError,ValueError,subprocess.TimeoutExpired) as exc:
        p.exit(2,"REAL_SEMANTIC_ACCEPTANCE_INCOMPLETE: "+str(exc)+"\n")
    return 0

if __name__=="__main__":
    raise SystemExit(main())
