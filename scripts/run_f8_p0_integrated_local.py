#!/usr/bin/env python3
"""F8 integrated P0 execution packet: reuse existing original owner modules.

No CI. No replacement PDE. Run from a literal checkout with source files.
Phases:
  preflight: source pins, exact construction probes, existing coupled-energy,
             constraint and radial Sobolev diagnostics, full-producer receipts.
  native:    original checkpointed A0/A1/C0/C1 original solver runner (opt-in).
  compare:   fail-closed 96-signed receiver parity and checkpoint forensics.
A check whose source is absent, skipped, times out or exits nonzero is NOT PASS.
Artifacts are JSON ledgers under .local-f8-p0-integrated/. Physical acceptance
always remains OPEN until continuum finite-speed/curvature/strong trace.
"""
import argparse,hashlib,json,os,subprocess,sys,time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
SOURCE_PINS={
 "scripts/ksw668_f8_tt_multipole.py":"28f114fa2fd364a8569f04a7e2ace15e45ffe980",
 "scripts/ksw668_f8_fv_source_flux.py":"dec4e79e3a4899952a5deceb786324bc0745982c",
 "scripts/ksw668_f8_weak_source.py":"69f35c6569667034214035d810dee06251a6d2ad",
 "scripts/ksw668_f8_ssprk_checkpoint.py":"2ef1bfbd4df98c29168a8f8b626efbecb71cdf99",
 "scripts/run_f8_lxix_native_source_matrix.py":"94e6303eab04823ab7f39244d21a32c98a300a07",
}
CHECKS={
 "construction-original-SAT":"scripts/check_f8_xcvi_original_sat_constraint_geometry_sympy.py",
 "construction-face-projection":"scripts/check_f8_xcvii_stagewise_constraint_projection_sympy.py",
 "construction-moving-action-trace":"scripts/check_f8_xcviii_action_boundary_dynamic_trace_sympy.py",
 "construction-manufactured-moving-wall":"scripts/check_f8_xcix_manufactured_moving_wall_trace_sympy.py",
 "original-full-coupled-constraint":"scripts/ksw668_f8_characteristic_constraint_maxcut.py",
 "original-radial-sobolev":"scripts/ksw668_f8_radial_sobolev_hierarchy.py",
 "geometry-brane-cones":"scripts/check_f8_xcii_induced_31_cones_sympy.py",
 "geometry-compact-causal-null":"scripts/check_f8_xciii_same_source_cones_and_far_null.py",
 "original-receipt-spatial-temporal":"scripts/check_f8_xci_existing_production_attribution_sympy.py",
 "original-receipt-field-lower-bound":"scripts/check_f8_xcv_far_wall_lower_bound_sympy.py",
}
REFERENCE_FILES=[
 "Artifacts/ksw668/ads5_f8_LVI_corrected_refinement_compact_20261120.json",
 "Artifacts/ksw668/ads5_f8_LVI_independent_medium_full.json",
 "Artifacts/ksw668/ads5_f8_LVI_independent_medium-dt-half_full.json",
 "Artifacts/ksw668/ads5_f8_LXIX_source_intervention_20261120.json",
]

def git_sha(path):
    data=path.read_bytes()
    return hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()

def write_atomic(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    tmp=path.with_suffix(path.suffix+".tmp")
    tmp.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")
    tmp.replace(path)

def run_one(label,argv,work,timeout):
    log=work/(label+".log")
    with log.open("w") as out:
        try:
            r=subprocess.run(argv,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT,
                env={**os.environ,"PYTHONDONTWRITEBYTECODE":"1","OPENBLAS_NUM_THREADS":"1",
                     "NUMBA_NUM_THREADS":"2"},timeout=timeout)
            return {"status":"PASS" if r.returncode==0 else "FAIL",
                    "exit_code":r.returncode,"log":str(log)}
        except subprocess.TimeoutExpired:
            return {"status":"TIMEOUT","log":str(log),"timeout_seconds":timeout}
        except OSError as e:
            return {"status":"BLOCKED","log":str(log),"reason":str(e)}

def check_sources():
    result={}
    for rel,sha in SOURCE_PINS.items():
        path=ROOT/rel
        observed=git_sha(path) if path.is_file() else None
        result[rel]={"status":"PASS" if observed==sha else "FAIL",
                     "expected":sha,"observed":observed}
    return result

def prepare(work,timeout):
    records={"phase":"preflight","source_identity":check_sources(),
             "checks":{},"reference_files":{}}
    for path in REFERENCE_FILES:
        p=ROOT/path
        records["reference_files"][path]={"status":"PASS" if p.is_file() else "FAIL",
            "git_blob_sha":git_sha(p) if p.is_file() else None}
    if not all(x["status"]=="PASS" for x in records["source_identity"].values()):
        records["status"]="FAIL_SOURCE_PROVENANCE"
        return records
    for label,rel in CHECKS.items():
        p=ROOT/rel
        records["checks"][label]=(run_one(label,[sys.executable,str(p)],work,timeout)
                                   if p.is_file() else {"status":"BLOCKED","missing_file":rel})
    records["status"]=("PASS_PREFLIGHT_ONLY" if
        all(x["status"]=="PASS" for x in records["checks"].values())
        and all(x["status"]=="PASS" for x in records["reference_files"].values())
        else "INCOMPLETE_OR_FAILED_PREFLIGHT")
    return records

def compare(work,timeout,native_dir,full_json,ck_file):
    report={"phase":"compare","source_identity":check_sources(),"checks":{}}
    if not all(x["status"]=="PASS" for x in report["source_identity"].values()):
        report["status"]="FAIL_SOURCE_PROVENANCE"
        return report
    parity=ROOT/"scripts/check_f8_lxxxvii_native_96_receipt.py"
    if parity.is_file():
        report["checks"]["four-way-96-signed"]=run_one(
            "native-96-parity",[sys.executable,str(parity),"--work",str(native_dir.resolve())],
            work,timeout)
    else:report["checks"]["four-way-96-signed"]={"status":"BLOCKED","missing_file":str(parity)}
    # Checkpoint forensics are optional independently supplied original
    # terminal files; do NOT pretend the current A0/A1 checkpoints are old FV.
    if bool(full_json)!=bool(ck_file):
        report["checks"]["checkpoint"]={"status":"BLOCKED","reason":"supply both --production-json and --checkpoint"}
    elif full_json:
        consumer=ROOT/"scripts/check_f8_xciv_checkpoint_wall_stencil.py"
        report["checks"]["checkpoint"]=(run_one("checkpoint-raw-wall",
            [sys.executable,str(consumer),"--checkpoint",str(ck_file.resolve()),
            "--production-json",str(full_json.resolve())],work,timeout)
            if consumer.is_file() else {"status":"BLOCKED","missing_file":str(consumer)})
    else:
        report["checks"]["checkpoint"]={"status":"NOT_RUN","reason":"authenticated original NPZ not provided"}
    report["status"]=("PASS_RECEIPT_PARITY_ONLY" if
        report["checks"]["four-way-96-signed"]["status"]=="PASS"
        else "OPEN_NATIVE_96_PARITY")
    report["continuum_causal_null_accepted"]=False
    report["physical_signal_accepted"]=False
    return report

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--phase",choices=("preflight","native","compare"),required=True)
    p.add_argument("--work",type=Path,default=ROOT/".local-f8-p0-integrated")
    p.add_argument("--native-dir",type=Path,default=ROOT/".local-f8-lxxxvii")
    p.add_argument("--timeout",type=int,default=90)
    p.add_argument("--production-json",type=Path)
    p.add_argument("--checkpoint",type=Path)
    p.add_argument("--max-rounds",type=int,default=64)
    args=p.parse_args()
    assert 1<=args.timeout<=90 and 1<=args.max_rounds<=10000
    args.work.mkdir(parents=True,exist_ok=True)
    now=time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime())
    if args.phase=="preflight":
        result=prepare(args.work,args.timeout)
    elif args.phase=="compare":
        result=compare(args.work,args.timeout,args.native_dir,args.production_json,args.checkpoint)
    else:
        source=check_sources()
        result={"phase":"native","source_identity":source,
                "status":"FAIL_SOURCE_PROVENANCE"}
        if all(x["status"]=="PASS" for x in source.values()):
            runner=ROOT/"scripts/run_f8_lxxxvii_native_96_local.sh"
            if runner.is_file():
                env={**os.environ,"F8_MAX_ROUNDS":str(args.max_rounds)}
                log=args.work/"native-cooperative.log"
                with log.open("w") as out:
                    try:
                        proc=subprocess.run(["bash",str(runner),str(args.native_dir.resolve())],
                                            cwd=ROOT,env=env,stdout=out,
                                            stderr=subprocess.STDOUT)
                        result["status"]="NATIVE_RECEIPT_PARITY_PASS_ONLY" if proc.returncode==0 else "NATIVE_INCOMPLETE_OR_FAIL"
                        result["exit_code"]=proc.returncode
                    except OSError as e:
                        result["status"]="NATIVE_BLOCKED"
                        result["reason"]=str(e)
                result["log"]=str(log)
            else:result["status"]="NATIVE_BLOCKED_NO_ORIGINAL_RUNNER"
        result["continuum_causal_null_accepted"]=False
        result["physical_signal_accepted"]=False
    result["timestamp_utc"]=now
    report=args.work/(args.phase+"-ledger.json")
    write_atomic(report,result)
    print(json.dumps({"ledger":str(report),"status":result["status"]},indent=2))
    # Intentionally nonzero unless a scoped phase truly passed.
    return 0 if result["status"] in ("PASS_PREFLIGHT_ONLY",
              "PASS_RECEIPT_PARITY_ONLY","NATIVE_RECEIPT_PARITY_PASS_ONLY") else 2
if __name__=="__main__":raise SystemExit(main())
