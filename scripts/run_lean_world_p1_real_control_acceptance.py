#!/usr/bin/env python3
"""Real Lean compiler + native-v3 P1 binder/changed-literal acceptance.

Compiles the ORIGINAL committed positive/negative source control and runs
an installed, version-compatible lean4export for all three declarations.
The same native type/proof codec and queue used by PRs #1494/#1495 are
called with no mock data, no independent Rust checker, no CI and no Docker.

Produces immutable original native handoffs and explicit Lean local compile
receipt. This standalone native control fixture is not yet a PostgreSQL
source-world admission; PG P1 requires the identical source revision/path
to already exist in the original SQL source store.
"""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path
import argparse
import json
import os
import shutil
import subprocess
import tempfile
import sys

from lean_world_native_v3_projection import extract_candidates
from lean_world_native_p1_codec import candidate_receipt
from lean_world_native_v3_export import inspect_v3,store_native
from lean_world_native_admission_queue import enqueue

SOURCE="tests/fixtures/lean_world_p1/BinderAndConstantControls.lean"
MODULE="tests.fixtures.lean_world_p1.BinderAndConstantControls"
NAMES=("DASHIP1.first","DASHIP1.second","DASHIP1.changed")

class RealP1ControlError(ValueError): pass

def command(argv,*,cwd=None,env=None,timeout=600):
    run=subprocess.run([str(x) for x in argv],cwd=cwd,env=env,
                       stdin=subprocess.DEVNULL,capture_output=True,
                       timeout=timeout,check=False)
    if run.returncode:
        raise RealP1ControlError("tool invocation failed: "+
                                str(argv[0])+" stderr_sha256="+
                                sha256(run.stderr).hexdigest())
    return run

def real_acceptance(*,lean,exporter,output,timeout=600):
    repo=Path(__file__).resolve().parents[1]
    source_file=repo/SOURCE
    original=source_file.read_bytes()
    git_rev=command(["git","rev-parse","HEAD"],cwd=repo).stdout.decode().strip()
    if len(git_rev)!=40:
        raise RealP1ControlError("original repository revision must be pinned")
    if command(["git","show","HEAD:"+SOURCE],cwd=repo).stdout!=original:
        raise RealP1ControlError("real P1 fixture differs from committed original")
    lean=Path(lean).resolve(strict=True)
    exporter=Path(exporter).resolve(strict=True)
    if not lean.is_file() or not exporter.is_file():
        raise RealP1ControlError("pinned native tooling unavailable")
    version=command([lean,"--version"]).stdout.decode("utf-8","replace").strip()
    if "Lean" not in version:
        raise RealP1ControlError("not a Lean compiler")
    if not 10<=timeout<=3600:
        raise RealP1ControlError("invalid real acceptance budget")
    output=Path(output).resolve()
    if output.exists() or output.is_symlink():
        raise RealP1ControlError("choose a NEW original P1 output directory")
    output.mkdir(parents=True)
    artifact_dir=output/"native"
    queue_dir=output/"queue"
    closure_id=sha256(
        json.dumps({"lean_binary_sha256":sha256(lean.read_bytes()).hexdigest(),
                    "toolchain":version,"source_sha256":sha256(original).hexdigest(),
                    "builtin_imports_only":True},sort_keys=True).encode()).hexdigest()
    with tempfile.TemporaryDirectory(prefix="dashi-real-p1-") as directory:
        root=Path(directory)
        staged=root/SOURCE
        staged.parent.mkdir(parents=True)
        staged.write_bytes(original)
        env={k:os.environ[k] for k in ("PATH","LANG","LC_ALL","HOME","LEAN_SYSROOT",
                                      "NIX_LD","NIX_LD_LIBRARY_PATH") if k in os.environ}
        env["LEAN_PATH"]=str(root)
        olean=root/Path(SOURCE).with_suffix(".olean")
        built=command([lean,"-o",olean,staged],cwd=root,env=env,timeout=timeout)
        if not olean.is_file():
            raise RealP1ControlError("Lean returned success without OLean")
        compiled_olean_sha256=sha256(olean.read_bytes()).hexdigest()
        joined={}
        receipts=[]
        for declaration in NAMES:
            native=command([exporter,MODULE,"--",declaration],
                           cwd=root,env=env,timeout=timeout).stdout
            validation=inspect_v3(native)
            source_closure=[{"path":SOURCE,"sha256":sha256(original).hexdigest()}]
            owner=store_native(
                native,validation,artifact_dir,
                repository="chboishabba/dashi_agda",revision=git_rev,
                module=MODULE,declaration=declaration,
                source_closure=source_closure,toolchain=version,
                dependency_closure_id=closure_id)
            queued=enqueue(owner,queue_dir)
            selected=extract_candidates(
                native,selected_names=frozenset([declaration]))
            matches=[x for x in selected if x.name==declaration]
            if len(matches)!=1:
                raise RealP1ControlError("original selected theorem absent/ambiguous")
            candidate=matches[0]
            observed=candidate_receipt(
                candidate,toolchain=version,
                source_sha256=sha256(original).hexdigest(),
                export_sha256=sha256(native).hexdigest())
            if not candidate.proof_value_present or not observed["exported_expr_roundtrip"]:
                raise RealP1ControlError("real theorem proof/export roundtrip absent")
            joined[declaration]=observed
            receipts.append({
                "declaration":declaration,
                "handoff_manifest":queued["manifest"],
                "exact_type_sha256":observed["exact_exported_type_sha256"],
                "alpha_type_sha256":observed["alpha_type_sha256"],
                "exact_proof_sha256":observed["exact_exported_proof_sha256"],
                "native_export_sha256":sha256(native).hexdigest(),
                "kernel_checked_original_module":True,
                "independently_verified":False
            })
    first=joined[NAMES[0]]
    second=joined[NAMES[1]]
    changed=joined[NAMES[2]]
    if (first["alpha_type_bytes"]!=second["alpha_type_bytes"] or
        first["alpha_type_bytes"]==changed["alpha_type_bytes"]):
        raise RealP1ControlError("real binder-alpha/changed-literal control failed")
    result={
        "schema":"dashi-real-lean-p1-native-expr-controls-v1",
        "status":"real-Lean-compiled-native-binder-controls",
        "repository":"chboishabba/dashi_agda",
        "original_revision":git_rev,
        "original_source_path":SOURCE,
        "original_source_sha256":sha256(original).hexdigest(),
        "lean_version":version,
        "lean_binary_sha256":sha256(lean.read_bytes()).hexdigest(),
        "compiled_original_olean_sha256":compiled_olean_sha256,
        "original_source_kernel_compiled":True,
        "native_proof_roundtrip":True,
        "binder_alpha_positive":True,
        "changed_numeral_negative":True,
        "declarations":receipts,
        "source_bytes_reconstructed_by_export_codec":False,
        "independent_checker_required":False,
        "authoritative_world_admitted":False
    }
    # OLean bytes are ephemeral; only its checked original digest persists.
    receipt_path=output/"receipt.p1-real-native-controls.json"
    with receipt_path.open("x",encoding="utf-8") as file:
        json.dump(result,file,sort_keys=True,indent=2)
        file.write("\n")
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean",required=True,type=Path)
    p.add_argument("--exporter",required=True,type=Path)
    p.add_argument("--output",required=True,type=Path)
    p.add_argument("--timeout",type=int,default=600)
    args=p.parse_args()
    try:
        result=real_acceptance(
            lean=args.lean,exporter=args.exporter,
            output=args.output,timeout=args.timeout)
        print(json.dumps({
            "status":result["status"],
            "original_revision":result["original_revision"],
            "positive":result["binder_alpha_positive"],
            "negative":result["changed_numeral_negative"],
            "receipt":str(args.output/"receipt.p1-real-native-controls.json"),
            "world_admitted":False},sort_keys=True))
        return 0
    except (OSError,ValueError,ImportError,subprocess.TimeoutExpired) as exc:
        print("REAL_P1_LEAN_INCOMPLETE: "+str(exc),file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
