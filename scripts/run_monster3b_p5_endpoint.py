#!/usr/bin/env python3
"""Unified source-first Monster 3B P5 endpoint workstation run.

Stages (fresh receipts, fail-closed):
  L10A Steel original Magma acquisition -> 12D GModule number-field export
       -> GAP 210-class original word-order/trace fingerprint candidates
  L10C construct exact 78/90 from one genuine ordinary12 matrix system
  L10B/L12R compute actual mmgroup Hit0 E-canonical words and central cover
       -> optionally solve the actual characteristic-zero Hom intertwiner
       and source outer twisted semilinear equations when supplied

This does NOT secretly promote characteristic-7 MMV data to char-zero
Monster-Hom coordinates or identify Hit0 as Monster 4D by group order.

Run at repo root:
  python3 scripts/run_monster3b_p5_endpoint.py --all

Options:
  --source-file path/to/Steel-original.M (skip network acquire)
  --manifest path/to/monster3b-authentic-manifest.json
  --module M             (original Magma GModule variable name)
  --hom char0_hom12.json (actual same-object target action; optional)
  --outer-map original_outer_alpha.json (actual source automorphism; optional)
  --skip-mmgroup         (if only Steel/Magma/GAP available)
  --skip-magma           (if original JSON already exported)
  --skip-gap             (stage fingerprint later)
"""
from __future__ import annotations
import argparse
from datetime import datetime,timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import traceback

ROOT=Path(__file__).resolve().parents[1]
SCRIPTS=ROOT/"scripts"
DEFAULT_MANIFEST=ROOT/".dashi/monster3b-mmgroup/monster3b-authentic-manifest.json"
def stage(name,command,log,timeout,cwd):
    now=time.monotonic()
    try:
        p=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
             text=True,errors="replace",cwd=cwd,timeout=timeout,check=False)
        log.write_text(p.stdout)
        return {"status":"EXIT_0" if p.returncode==0 else f"EXIT_{p.returncode}",
            "seconds":round(time.monotonic()-now,3),
            "log":str(log),"command":command,
            "tail":p.stdout[-1600:] if p.returncode else ""}
    except Exception as exc:
        log.write_text(traceback.format_exc())
        return {"status":type(exc).__name__,
          "seconds":round(time.monotonic()-now,3),
          "log":str(log),"command":command,"error":str(exc)}
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--all",action="store_true",help="run every currently available endpoint producer")
    ap.add_argument("--source-file",type=Path)
    ap.add_argument("--manifest",type=Path,default=DEFAULT_MANIFEST)
    ap.add_argument("--module",default="M")
    ap.add_argument("--hom",type=Path)
    ap.add_argument("--outer-map",type=Path)
    ap.add_argument("--skip-mmgroup",action="store_true")
    ap.add_argument("--skip-magma",action="store_true")
    ap.add_argument("--skip-gap",action="store_true")
    ap.add_argument("--actual-mod31-hom",action="store_true",
        help="also construct actual mmgroup MMV(31) 90D Hom vacuum and 12/78 C2 sectors")
    ap.add_argument("--timeout",type=int,default=900)
    ap.add_argument("--outdir",type=Path)
    args=ap.parse_args()
    if args.timeout<1:ap.error("--timeout must be >0")
    base=ROOT/"build/monster3b-p5-endpoint"
    out=(args.outdir or base/("run-"+datetime.now(timezone.utc).strftime(
        "%Y%m%dT%H%M%SZ")+"-"+str(os.getpid()))).resolve()
    if out.exists() and any(out.iterdir()):
        ap.error("refusing to overwrite nonempty endpoint run: "+str(out))
    out.mkdir(parents=True,exist_ok=True)
    srcdir=(ROOT/".dashi/monster3b-steel-ordinary12").resolve()
    srcdir.mkdir(parents=True,exist_ok=True)
    report={
      "schema":"monster3b-P5-source-endpoint-orchestration-v1",
      "root":str(ROOT),"run_directory":str(out),
      "stages":{},"lemma_status":{},
      "actual_char0_Monster_Hom_cannot_be_inferred_from_MMV7":True,
      "source_4D_class_GAP_paid":True,
      "specific_Hit0_MM_group_word_in_class_4D_identified":False,
      "original_source_6Suz_standard_generator_to_MM_word_identified":False,
      "certification_deferred":True}
    summary=out/"endpoint_summary.json"
    def save():summary.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    def run(name,command,timeout=None):
        receipt=stage(name,[str(x) for x in command],out/(name+".log"),
                      timeout or args.timeout,ROOT)
        report["stages"][name]=receipt
        save()
        return receipt["status"]=="EXIT_0"
    try:
        if args.source_file:
            source=args.source_file.resolve()
            if not source.is_file():raise ValueError("--source-file not found")
            source_path=source
            report["stages"]["acquire"]={"status":"USER_SOURCE_FILE"}
        else:
            source_path=srcdir/"d12.6Suz.nfdeg2.M"
            if run("acquire",[sys.executable,
                SCRIPTS/"monster3b_steel_ordinary12_to90.py","--acquire",
                "--source-root",srcdir]) is False:
                raise RuntimeError("original Steel source acquisition failed")
        if not args.skip_magma:
            if not run("magma_export",[sys.executable,
                    SCRIPTS/"monster3b_steel_magma_export.py",
                    "--source",source_path,"--outdir",out,
                    "--module",args.module,"--magma","--timeout",args.timeout]):
                raise RuntimeError("original Magma module export failed; inspect magma_export.log")
            original12=out/"steel12_source_generators.json"
        else:
            original12=srcdir/"steel12_source_generators.json"
            if not original12.is_file():raise RuntimeError(
                "--skip-magma but prior original Steel source JSON is absent")
        report["lemma_status"]["M3B-L10A_original_12_matrix_module"]=(
            "SOURCE_MAGMA_PRODUCED" if not args.skip_magma else "PREEXISTING_JSON_NOT_REVALIDATED")
        report["source12_json"]=str(original12);save()
        if not run("derive90",[sys.executable,
                SCRIPTS/"monster3b_steel_ordinary12_to90.py",
                "--matrix-json",original12,"--out",
                out/"ordinary12_derived90.json"]):
            raise RuntimeError("Q(zeta3) 12→78→90 exact field construction failed")
        report["lemma_status"]["M3B-L10C_inner_90_from_source12"]="DERIVED_EXACT"
        if not args.skip_gap:
            if run("gap_fingerprint",[sys.executable,
                    SCRIPTS/"monster3b_gap_ordinary12_class_fingerprint.py",
                    "--source",original12,"--outdir",out,
                    "--run-gap","--timeout",args.timeout]):
                report["lemma_status"]["M3B-L10A_class_orientation"]=(
                    "EXACT_FINGERPRINT_CANDIDATES_NOT_CANONICAL_CLASS_WORD")
            else:
                report["lemma_status"]["M3B-L10A_class_orientation"]="GAP_FINGERPRINT_FAILED"
        else:
            report["lemma_status"]["M3B-L10A_class_orientation"]="DEFERRED"
        if not args.skip_mmgroup:
            if not args.manifest.exists():
                report["stages"]["mmgroup_canonical_words"]={
                    "status":"MISSING_AUTHENTIC_MANIFEST","path":str(args.manifest)}
            else:
                if run("mmgroup_canonical_words",[sys.executable,
                        SCRIPTS/"monster3b_mmgroup_canonical_cover_words.py",
                        "--root",ROOT,"--manifest",args.manifest,"--out",
                        out/"mmgroup_canonical_cover_hit0.json"]):
                    report["lemma_status"]["M3B-L10B_MM_E_canonical_word"] = \
                        "EXACT_ACTUAL_MM_COVER_WORDS; NO_SOURCE_STANDARD_GENERATOR_ID"
                    report["lemma_status"]["M3B-L12R_outer_E_action"] = \
                        "ACTUAL_MM_CONJUGATION_AND_CENTRAL_RELATOR_DATA; COMPLEX_OUTER_OPEN"
                else:
                    report["lemma_status"]["M3B-L10B_MM_E_canonical_word"]="FAILED"
        if args.actual_mod31_hom:
            cover=out/"mmgroup_canonical_cover_hit0.json"
            if not args.manifest.exists():
                report["lemma_status"]["M3B-L10B_actual_mod31_Hom_vacuum"]=\
                    "MISSING_AUTHENTIC_MANIFEST"
            else:
                arguments=[sys.executable,
                    SCRIPTS/"monster3b_actual_mmv31_hom_projector.py",
                    "--manifest",args.manifest,
                    "--outdir",out/"actual_mmv31_hom"]
                if cover.exists():
                    arguments.extend(["--cover",cover])
                if run("actual_mod31_hom",arguments):
                    report["lemma_status"]["M3B-L10B_actual_mod31_Hom_vacuum"]=\
                        "GENUINE_MM31_MODULAR_PROJECTOR; NOT_COMPLEX_HOM"
                else:
                    report["lemma_status"]["M3B-L10B_actual_mod31_Hom_vacuum"]="FAILED"
                if run("hom_outer",[sys.executable,
               SCRIPTS/"monster3b_ordinary12_hom_outer_weld.py",
               "--source",original12,"--out",out/"hom_outer_weld.json",
               * (["--hom",str(args.hom)] if args.hom else []),
               * (["--outer-map",str(args.outer_map)] if args.outer_map else [])]):
            report["lemma_status"]["M3B-L10B_complex_12_Hom_intertwiner"]=(
                "CONDITIONAL_EXACT_LINEAR_WELD; SOURCE_AUTHENTICATION_OPEN"
                if args.hom else "NEEDS_ACTUAL_COMPLEX_MONSTER_HOM")
            report["lemma_status"]["M3B-L12R_complex_outer_intertwiner"]=(
                "CONDITIONAL_TWISTED_INTERTWINER; WORD_GAUGE_OPEN"
                if args.outer_map and args.hom else "NEEDS_SOURCE_OUTER_AND_COMPLEX_HOM")
        else:
            report["lemma_status"]["M3B-L10B_complex_12_Hom_intertwiner"]="ERROR"
        report["status"]="STAGED_MATHEMATICAL_ENDPOINTS_WITH_REMAINING_SOURCE_ATTACHMENT"
    except Exception as exc:
        report["status"]="ERROR_FAIL_CLOSED"
        report["error"]={"type":type(exc).__name__,"message":str(exc),
                         "traceback":traceback.format_exc(limit=7)}
    finally:
        save()
    print("MONSTER3B_P5_STATUS:",report["status"])
    print("ENDPOINT_SUMMARY:",summary)
    print("SOURCE_CHECKS:",json.dumps(report["lemma_status"],indent=2))
    return 0 if report["status"]!="ERROR_FAIL_CLOSED" else 2
if __name__=="__main__":raise SystemExit(main())
