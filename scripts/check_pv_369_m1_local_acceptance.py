#!/usr/bin/env python3
"""M1 local Golden acceptance: execute exact checked-out PV369 sources.

This is intentionally LOCAL and fail-closed: no GitHub Action success,
source-written theorem, manually reported arithmetic result, or unrun
selftest is counted as accepted. Never manufactures a physical PCE.
Run at the repo root with the pinned Agda toolchain.

Exit codes: 0 = all selected checks passed; 1 = error; 2 = Agda unavailable
in strict --require-agda mode. Without --require-agda, native Agda remains
explicitly UNVERIFIED; that outcome cannot be called all-gates pass.
"""
import argparse
import json
import py_compile
import shutil
import subprocess
import sys
from pathlib import Path

SCRIPTS = (
    "check_pv_g173_same_sample_optics_eqe_iv_weld.py",
    "check_pv_g173_same_sample_weld_independent_fixture.py",
    "check_pv_369_worst_case_power_intervals.py",
    "check_pv_369_unsampled_iv_mpp_envelope.py",
    "check_pv_g173_multijunction_net_loss_frontier.py",
    "check_pv_v68_published_multijunction_table_identity.py",
    "check_pv_v68_printed_4t_rounding_interval.py",
)
AGDA = (
    "DASHI/Physics/Photovoltaic/PV369NetHalfThresholdExact.agda",
    "DASHI/Physics/Photovoltaic/PV369FourJunctionOpticsToMeasuredIVExact.agda",
    "DASHI/Physics/Photovoltaic/PV369G173MultiJunctionLossFrontierExact.agda",
    "DASHI/Physics/Photovoltaic/PV369IntervalRobustAcceptanceExact.agda",
    "DASHI/Physics/Photovoltaic/PV369UnsampledIVPowerEnvelopeExact.agda",
    "DASHI/Physics/Photovoltaic/Atomic369BasisTransportNoFreeGainExact.agda",
    "DASHI/Physics/Photovoltaic/PVGreen68FourTerminalPublishedSourceExact.agda",
    "DASHI/Physics/Photovoltaic/PV369P2CoulombSolarNonPromotionExact.agda",
    "DASHI/Unified/PVPrimaryTOESpliceExact.agda",
)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--require-agda",action="store_true")
    ap.add_argument("--output",type=Path)
    args=ap.parse_args()
    root=Path(__file__).resolve().parent.parent
    result={"type":"PV369 M1 actual checked-out local acceptance",
        "physical_efficiency_certified":False,
        "369_specific_gain_measured":False,
        "python":[],"agda":[],"native_agda_status":"NOT_RUN",
        "errors":[]}
    for name in SCRIPTS:
        path=root/"scripts"/name
        entry={"file":name,"parse":"NOT_RUN","selftest":"NOT_RUN"}
        result["python"].append(entry)
        if not path.is_file():
            result["errors"].append("missing committed Python file: "+str(path))
            continue
        try:
            py_compile.compile(str(path),doraise=True)
            entry["parse"]="PASS"
        except Exception as exc:
            entry["parse"]="FAIL"
            result["errors"].append("Python syntax "+name+": "+repr(exc))
            continue
        invocation=[sys.executable,str(path)]
        if name!="check_pv_g173_same_sample_weld_independent_fixture.py":
            invocation.append("--selftest")
        run=subprocess.run(invocation,cwd=root,capture_output=True,text=True,timeout=90)
        entry["return_code"]=run.returncode
        entry["stderr_tail"]=run.stderr[-1500:]
        if run.returncode:
            entry["selftest"]="FAIL"
            result["errors"].append("Python executed selftest failed: "+name)
        else:
            entry["selftest"]="PASS"
            try:
                report=json.loads(run.stdout)
                count=report.get("checks_passed",report.get("passed",report.get("local_exact_arithmetic_checks_passed")))
                entry["checks_reported"]=count
                if report.get("all_passed") is not True or not isinstance(count,int) or count<10:
                    entry["selftest"]="FAIL"
                    result["errors"].append("missing verifiable JSON selftest count: "+name)
            except json.JSONDecodeError:
                if name!="check_pv_g173_same_sample_weld_independent_fixture.py" or not run.stdout.startswith("PASS 26 "):
                    entry["selftest"]="FAIL"
                    result["errors"].append("unexpected selftest stdout: "+name)
                else:
                    entry["checks_reported"]=26

    agda=shutil.which("agda")
    if not agda:
        result["native_agda_status"]="UNAVAILABLE"
        result["errors"].append("Agda kernel unavailable; no Golden acceptance")
    else:
        result["native_agda_status"]="RUNNING"
        for name in AGDA:
            entry={"file":name,"acceptance":"NOT_RUN"}
            result["agda"].append(entry)
            file=root/name
            if not file.exists():
                entry["acceptance"]="FAIL"
                result["errors"].append("missing Agda file: "+name)
                continue
            try:
                run=subprocess.run([agda,"-i",str(root),str(file)],cwd=root,
                    capture_output=True,text=True,timeout=180)
                entry["exit_code"]=run.returncode
                entry["output_tail"]=(run.stdout+"\n"+run.stderr)[-1200:]
                entry["acceptance"]="PASS" if run.returncode==0 else "FAIL"
                if run.returncode:result["errors"].append("Agda kernel failed: "+name)
            except subprocess.TimeoutExpired:
                entry["acceptance"]="TIMEOUT"
                result["errors"].append("Agda timeout: "+name)
        result["native_agda_status"]="PASS" if not any(
            e["acceptance"]!="PASS" for e in result["agda"]) else "FAIL"

    result["exact_checked_out_python_passed"]=all(
        x["parse"]=="PASS" and x["selftest"]=="PASS" for x in result["python"])
    result["all_formal_gates_passed"]=(
        result["exact_checked_out_python_passed"] and result["native_agda_status"]=="PASS")
    if args.output:args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
    if not agda and args.require_agda:return 2
    return 1 if result["errors"] else 0

if __name__=="__main__":sys.exit(main())
