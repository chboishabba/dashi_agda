#!/usr/bin/env python3
"""Resume the actual original-action endpoint, not the auxiliary P5 search.

Uses an existing genuine source-run directory. Never overwrites its inputs.
Exit 0 only for a completed exact ambient roundtrip, 3 for checkpoint pause,
124 for stage timeout, 2 for blocked source/runtime/error.
"""
import argparse, json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
from importlib.metadata import version, PackageNotFoundError

ROOT=Path(__file__).resolve().parents[1]
SCRIPTS=ROOT/"scripts"
SOURCE=ROOT/"Docs/support/reference/Monster3BLindseyOrdinaryCD20261124.json"

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def save(p,data):
    t=p.with_suffix(".tmp");t.write_text(json.dumps(data,indent=2)+"\n");t.replace(p)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source-run",type=Path,required=True,help="original P5 run containing corrected cover and direct positive MMV31 packet")
    p.add_argument("--manifest",type=Path,default=ROOT/".dashi/monster3b-mmgroup/monster3b-authentic-manifest.json")
    p.add_argument("--cover",type=Path)
    p.add_argument("--plus",type=Path)
    p.add_argument("--model",type=Path,help="optional existing canonical signed Weil receipt")
    p.add_argument("--outdir",type=Path,required=True)
    p.add_argument("--timeout",type=int,default=90,help="per-stage wall-clock limit; 0 disables")
    p.add_argument("--max-new",type=int,help="new checkpoints per producer invocation")
    p.add_argument("--negative-audit",type=int,default=1)
    p.add_argument("--chunk-size",type=int,default=16)
    a=p.parse_args()
    if a.timeout<0 or (a.max_new is not None and a.max_new<0) or not 0<=a.negative_audit<=90 or not 1<=a.chunk_size<=729:p.error("invalid timeout/budget/audit/chunk")
    src=a.source_run.resolve();out=a.outdir.resolve()
    manifest=a.manifest.resolve();cover=(a.cover or src/"mmgroup_canonical_cover_hit0.json").resolve()
    plus=(a.plus or src/"actual_mmv31_hom").resolve()
    model=(a.model or out/"canonical_signed_729_model.json").resolve()
    if out==src or src in out.parents or out in src.parents:p.error("use separate output and source-run directories")
    if out==plus or plus in out.parents or out in plus.parents:p.error("do not write into the original positive packet")
    out.mkdir(parents=True,exist_ok=True)
    report={"schema":"monster3b-actual-char0-execution-v1","stages":{},
            "source_run":str(src),"manifest":str(manifest),"cover":str(cover),
            "plus":str(plus),"model":str(model),"actual_roundtrip":False,
            "full_group_authentication_and_kernel_acceptance_separate":True}
    summary=out/"execution_summary.json"
    def finish(status,code):
        report["status"]=status;save(summary,report);print(status,flush=True);return code
    for name,path in (("manifest",manifest),("cover",cover),("plus_status",plus/"mmv31_hom_status.json"),("ordinary_source",SOURCE)):
        if not path.is_file():
            report["missing_input"]=str(path);return finish("BLOCKED_MISSING_ORIGINAL_INPUT_"+name.upper(),2)
    ambient=plus/"ambient_basis_rows_mod31.npz"
    if not ambient.is_file():ambient=plus/"ambient_basis_rows.npz"
    if not ambient.is_file():
        report["missing_input"]=str(ambient);return finish("BLOCKED_MISSING_ORIGINAL_AMBIENT_ROWS",2)
    try:runtime=version("mmgroup")
    except PackageNotFoundError:return finish("BLOCKED_MMGROUP_NOT_INSTALLED",2)
    report["mmgroup_version"]=runtime
    report["input_sha256"]={str(x):sha(x) for x in (manifest,cover,plus/"mmv31_hom_status.json",ambient,SOURCE)}
    def stage(name,script,args=()):
        path=SCRIPTS/script
        key={"script_sha256":sha(path),"runtime":runtime,"args":[str(x) for x in args]}
        log=out/(name+".log")
        cmd=[sys.executable,"-O",str(path),*map(str,args)]
        try:
            with log.open("a") as f:
                f.write("\n"+datetime.now(timezone.utc).isoformat()+" "+repr(cmd)+"\n");f.flush()
                proc=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=a.timeout or None)
            rc=proc.returncode
        except subprocess.TimeoutExpired:rc=124
        report["stages"][name]={"returncode":rc,"log":str(log),"identity":key}
        save(summary,report);return rc
    # Cache a successful native preflight only for identical backend, test and
    # installed runtime; never use a fixture or a previous failed invocation.
    preflight=out/"native_preflight_identity.json"
    pid={"runtime":runtime,"backend":sha(SCRIPTS/"monster3b_conway_exact_crt.py"),
         "checker":sha(SCRIPTS/"check_monster3b_native_exact_preflight.py")}
    if not preflight.is_file() or read(preflight)!=pid:
        rc=stage("native_preflight","check_monster3b_native_exact_preflight.py")
        if rc:return finish("NATIVE_PREFLIGHT_NOT_COMPLETE",124 if rc==124 else 2)
        save(preflight,pid)
    else:report["stages"]["native_preflight"]={"status":"REUSED_IDENTICAL_SUCCESS_RECEIPT"}
    if not model.is_file():
        if a.model:return finish("BLOCKED_EXPLICIT_MODEL_MISSING",2)
        rc=stage("canonical_weil","monster3b_global_parity_weil_section.py",("--cover",cover,"--out",model))
        if rc:return finish("CANONICAL_WEIL_NOT_COMPLETE",124 if rc==124 else 2)
    budget=[] if a.max_new is None else ["--max-new",a.max_new]
    vacuum=out/"vacuum"
    rc=stage("actual_char0_vacuum","monster3b_actual_char0_vacuum.py",
       ["--manifest",manifest,"--cover",cover,"--model",model,"--plus",plus,"--outdir",vacuum,"--negative-audit",a.negative_audit,*budget])
    if rc:return finish("VACUUM_CHECKPOINT_PAUSE" if rc==3 else "VACUUM_NOT_COMPLETE",rc if rc in (3,124) else 2)
    result=vacuum/"actual_char0_result.json"
    if not result.is_file() or read(result).get("status")!="ACTUAL_CHAR0_SIGNED_VACUUM_GENERATOR_WELD":return finish("BLOCKED_MISSING_EXACT_VACUUM_RECEIPT",2)
    weights=out/"weights"
    rc=stage("actual_full_weight_roundtrip","monster3b_actual_char0_weight_roundtrip.py",
       ["--manifest",manifest,"--cover",cover,"--vacuum",vacuum,"--outdir",weights,"--chunk-size",a.chunk_size,*budget])
    if rc:return finish("WEIGHT_CHECKPOINT_PAUSE" if rc==3 else "WEIGHT_NOT_COMPLETE",rc if rc in (3,124) else 2)
    receipt=weights/"actual_char0_weight_roundtrip.json"
    if not receipt.is_file():return finish("BLOCKED_MISSING_WEIGHT_RECEIPT",2)
    r=read(receipt)
    if r.get("status")!="ACTUAL_CHAR0_FULL_WEIGHT_ROUNDTRIP" or r.get("actual_exact_ambient_roundtrip") is not True or r["identity"]["vacuum_receipt_sha256"]!=sha(result):return finish("BLOCKED_INVALID_WEIGHT_RECEIPT",2)
    report.update(actual_roundtrip=True,vacuum_receipt_sha256=sha(result),weight_receipt_sha256=sha(receipt))
    return finish("ACTUAL_CHAR0_ENDPOINT_ROUNDTRIP_COMPLETE",0)
if __name__=="__main__":raise SystemExit(main())
