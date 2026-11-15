#!/usr/bin/env python3
"""Actual lean4export v3 producer within the ephemeral Lean workspace.

Native v3 syntax validation is NOT full DAG validation or a kernel proof.
dashi_lean4's build_jmd_lean_ast_world.py owns DAG validation/admission.
"""
from __future__ import annotations
import hashlib, json, os, re, resource, signal, subprocess, tempfile
from pathlib import Path
from lean_world_atomic_spool import publish_immutable, PublicationError

IDENT=re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")
SHA40=re.compile(r"[0-9a-f]{40}\Z")
KINDS={"thm","def","opaque","axiom","inductive","quot","ctor","rec"}
class NativeExportError(ValueError): pass

def sha(data:bytes)->str: return hashlib.sha256(data).hexdigest()

def inspect_v3(raw:bytes)->dict:
    if not raw or len(raw)>200_000_000: raise NativeExportError("empty/oversized export")
    count=0
    declarations=0
    for line in raw.splitlines():
        if not line.strip(): continue
        if len(line)>8_000_000: raise NativeExportError("oversized NDJSON record")
        try: row=json.loads(line)
        except (ValueError,UnicodeError) as e: raise NativeExportError("invalid v3 JSONL") from e
        if not isinstance(row,dict): raise NativeExportError("nonobject NDJSON row")
        if count==0:
            meta=row.get("meta")
            version=meta.get("format",{}).get("version") if isinstance(meta,dict) else None
            if not isinstance(version,str) or not version.startswith("3."):
                raise NativeExportError("missing first v3 metadata")
        elif "meta" in row: raise NativeExportError("duplicate metadata")
        if any(k in row for k in KINDS): declarations+=1
        count+=1
    if declarations==0: raise NativeExportError("no native declarations exported")
    return {"export_sha256":sha(raw),"ndjson_records":count,"declaration_records":declarations,
            "syntax_v3_checked":True,"dag_validated":False,"kernel_proof_verified":False}

def export_native(workspace:Path,module:str,declaration:str,*,command:tuple[str,...]=("lean4export",),
                  lean_path:str="",timeout:int=180,memory_mib:int=4096)->tuple[bytes,dict]:
    if not IDENT.fullmatch(module) or not IDENT.fullmatch(declaration):
        raise NativeExportError("invalid Lean module/declaration name")
    if not command or any(not isinstance(c,str) or not c for c in command):
        raise NativeExportError("invalid native exporter command")
    if not 1<=timeout<=1800 or memory_mib<128:
        raise NativeExportError("invalid resource budget")
    workspace=workspace.resolve()
    if not workspace.is_dir(): raise NativeExportError("missing ephemeral workspace")
    env={k:os.environ[k] for k in ("PATH","LANG","LC_ALL","LC_CTYPE","TZ") if k in os.environ}
    home=workspace/".export-home"
    home.mkdir(exist_ok=True)
    env["HOME"]=str(home)
    env["LEAN_PATH"]=str(workspace)+(os.pathsep+lean_path if lean_path else "")
    argv=[*command,module,"--",declaration]
    def limits():
        resource.setrlimit(resource.RLIMIT_AS,(memory_mib*1048576,memory_mib*1048576))
    try:
        proc=subprocess.Popen(argv,cwd=workspace,env=env,stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,stderr=subprocess.PIPE,
            start_new_session=True,preexec_fn=limits)
    except OSError as e: raise NativeExportError("export executable unavailable") from e
    try: stdout,stderr=proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as e:
        os.killpg(proc.pid,signal.SIGKILL)
        proc.communicate()
        raise NativeExportError("native exporter timed out") from e
    if proc.returncode:
        raise NativeExportError("native exporter exited "+str(proc.returncode)+"; stderr_sha256="+sha(stderr))
    report=inspect_v3(stdout)
    report["exporter_command"]=argv
    report["stderr_sha256"]=sha(stderr)
    return stdout,report

def store_native(raw:bytes,verification:dict,output:Path,*,repository:str,revision:str,
                 module:str,declaration:str,source_closure:list[dict],
                 toolchain:str,dependency_closure_id:str)->dict:
    if not SHA40.fullmatch(revision) or not source_closure:
        raise NativeExportError("missing pinned source identity")
    if any(not isinstance(s.get("sha256"),str) or len(s["sha256"])!=64 for s in source_closure):
        raise NativeExportError("missing source hashes")
    if verification.get("export_sha256")!=sha(raw):
        raise NativeExportError("native export digest mismatch")
    output=output.resolve()
    output.mkdir(parents=True,exist_ok=True)
    artifact=output/(sha(raw)+".ndjson")
    try:
        publish_immutable(artifact, raw)
    except PublicationError as exc:
        raise NativeExportError(str(exc)) from exc
    return {"schema":"dashi-lean-ephemeral-native-export-v1",
            "status":"native-v3-exported-unadmitted",
            "repository":repository,"revision":revision,"module":module,
            "declaration":declaration,"toolchain":toolchain,
            "dependency_closure_id":dependency_closure_id,
            "source_closure":source_closure,"artifact_path":str(artifact),
            "artifact_sha256":sha(raw),"validation":verification,
            "complete_dag_checked":False,"world_admitted":False,
            "kernel_proof_certified":False}
