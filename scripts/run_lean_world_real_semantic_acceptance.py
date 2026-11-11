#!/usr/bin/env python3
"""Pinned Lean 4.28 donor/consumer -> lean4export -> Tenet acceptance.

This script is intentionally LOCAL, explicit and fail-closed: temporary tool
checkouts, no CI/Docker, no world DB mutation, no proof-status promotion by a
Python parser. A successful run records independent checker observations,
including a negative-control rejection. It does not claim fibre retrieval.
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

EXPORTER_SHA = "d065b0009aed0520e9e99752847a33b337661690"
TENET_SHA = "026a35ce8c433b4785a8be8ae15952803ddfacc5"
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

def main_run(output_dir: Path, *, timeout=600):
    lean=require_tool("lean")
    lake=require_tool("lake")
    dotnet=require_tool("dotnet")
    require_tool("git")
    version=command([lean,"--version"]).stdout.decode("utf-8","replace").strip()
    dotnet_version=command([dotnet,"--version"]).stdout.decode().strip()
    if "Lean (version 4.28.0" not in version and "Lean 4.28.0" not in version:
        raise AcceptanceError("Lean version not the required pinned 4.28.0")
    if not dotnet_version.startswith("10."):
        raise AcceptanceError("Tenet acceptance requires .NET SDK 10")
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
        tenet=clone_tag(root,"tenet",
           "https://github.com/keithadler/tenet.git","v0.11.3",TENET_SHA)
        command([lake,"build","lean4export"],cwd=exporter,timeout=1200)
        exporter_binary=exporter/".lake/build/bin/lean4export"
        if not exporter_binary.is_file():
            raise AcceptanceError("pinned exporter build produced no binary")
        command([dotnet,"build","-c","Release","-f","net10.0",
                 "src/Tenet.Cli/Tenet.Cli.csproj"],cwd=tenet,timeout=1200)
        tenet_binary=tenet/"src/Tenet.Cli/bin/Release/net10.0/tenet"
        if not tenet_binary.is_file():
            raise AcceptanceError("pinned Tenet build produced no executable")
        tenet_assembly=tenet/"src/Tenet.Cli/bin/Release/net10.0/tenet.dll"
        if not tenet_assembly.is_file():
            raise AcceptanceError("pinned Tenet assembly unavailable")
        original=root/"original"
        original.mkdir()
        env={k:os.environ[k] for k in (
            "PATH","HOME","LANG","LC_ALL","LEAN_PATH","LEAN_SYSROOT","DOTNET_ROOT",
            "NIX_LD","NIX_LD_LIBRARY_PATH") if k in os.environ}
        env["LEAN_PATH"]=str(original)+(os.pathsep+env["LEAN_PATH"]
                    if env.get("LEAN_PATH") else "")
        for file in ("Donor.lean","Consumer.lean"):
            shutil.copyfile(FIXTURES/file,original/file)
        reports=[]
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
            independent=command([tenet_binary,"check",export,
                                 "--fail-on-axiom","sorryAx"],
                                 cwd=original,env=env,timeout=timeout)
            if b"OK:" not in independent.stdout:
                raise AcceptanceError("Tenet gave no explicit OK receipt for "+module)
            reports.append({
                "module":module,"declaration":theorem,
                "source_sha256":digest(original/(module+".lean")),
                "olean_sha256":digest(compiled),
                "native_export_sha256":digest(export),
                "native_export_bytes":export.stat().st_size,
                "checker_stdout_sha256":sha256(independent.stdout).hexdigest(),
                "checker_stderr_sha256":sha256(independent.stderr).hexdigest(),
                "lean_stdout_sha256":sha256(checked.stdout).hexdigest()})
        # Independent rejection: select an actual malformed corpus input from
        # the pinned checker distribution, never create a fabricated acceptance.
        invalid=sorted((tenet/"tests/fixtures/invalid").rglob("*.ndjson"))
        if not invalid:
            raise AcceptanceError("pinned checker negative-control corpus missing")
        rejection=command([tenet_binary,"check",invalid[0]],
                          cwd=tenet,env=env,timeout=timeout,
                          expect_success=False)
        if rejection.returncode == 0:
            raise AcceptanceError("independent checker accepted invalid control")
        receipt={
            "schema":"dashi-lean-real-independent-semantic-acceptance-v1",
            "status":"independent-checker-observed-two-module-reuse",
            "original_repository":"chboishabba/dashi_agda",
            "original_commit":original_commit,
            "lean_version":version,
            "lean_binary_sha256":digest(lean),
            "dotnet_sdk_version":dotnet_version,
            "dotnet_executable_sha256":digest(dotnet),
            "exporter_source_sha":EXPORTER_SHA,
            "exporter_executable_sha256":digest(exporter_binary),
            "checker_source_sha":TENET_SHA,
            "checker_apphost_sha256":digest(tenet_binary),
            "checker_assembly_sha256":digest(tenet_assembly),
            "declarations":reports,
            "invalid_fixture_name":invalid[0].relative_to(tenet).as_posix(),
            "invalid_fixture_sha256":digest(invalid[0]),
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
