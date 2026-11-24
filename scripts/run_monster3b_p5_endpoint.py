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
    ap.add_argument("--both-mod31-phases",action="store_true",
        help="construct zeta=5 and 25 source Hom sectors, recover exact Qzeta12 candidate characters")
    ap.add_argument("--reuse-mod31-plus",type=Path,
        help="reuse prior authentic zeta=5 rank90 source folder; only build missing phase")
    ap.add_argument("--actual-mod127-hom",action="store_true",
        help="independent original Monster MMV(127) 90D B-vacuum source")

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
        # This original ATLAS 2.Suz:2 729 scalar theorem needs no
        # Steel, Magma, GAP, mmgroup or user-supplied source archive.
        # It is a selected quotient-chart donor, NOT a literal Monster
        # 729-to-196884 vector identification.
        if run("ATLAS_original_729_Weil_replay",[
            sys.executable,
            SCRIPTS/"check_monster3b_atlas_source729_relator.py",
            "--out",out/"ATLAS_original_729_Weil_relator.json"]):
            report["lemma_status"]["M3B-L10B_ATLAS_existing_729_Weil_model"]=\
                "EXACT_2SUZ2_QUOTIENT_R7_ONE_BOTH_PHASES; NOT_MM_SAME_OBJECT"
        else:
            report["lemma_status"]["M3B-L10B_ATLAS_existing_729_Weil_model"]=\
                "SOURCE_729_ATLAS_REPLAY_FAILED"
        original12=None
        source_path=srcdir/"d12.6Suz.nfdeg2.M"
        source_available=False
        if args.source_file:
            source_path=args.source_file.resolve()
            source_available=source_path.is_file()
            report["stages"]["acquire"]={
                "status":"USER_SOURCE_FILE" if source_available else "SOURCE_FILE_MISSING",
                "path":str(source_path)}
        else:
            source_available=run("acquire",[sys.executable,
                SCRIPTS/"monster3b_steel_ordinary12_to90.py","--acquire",
                "--source-root",srcdir])
        if not source_available:
            report["lemma_status"]["M3B-L10A_original_12_matrix_module"]=\
                "STEEL_SOURCE_NOT_AVAILABLE; MMGROUP_STAGE_WILL_STILL_RUN"
        elif not args.skip_magma:
            if run("magma_export",[sys.executable,
                    SCRIPTS/"monster3b_steel_magma_export.py",
                    "--source",source_path,"--outdir",out,
                    "--module",args.module,"--magma","--timeout",args.timeout]):
                original12=out/"steel12_source_generators.json"
                report["lemma_status"]["M3B-L10A_original_12_matrix_module"]=\
                    "SOURCE_MAGMA_PRODUCED"
            else:
                report["lemma_status"]["M3B-L10A_original_12_matrix_module"]=\
                    "SOURCE_MAGMA_EXPORT_FAILED; MMGROUP_STAGE_WILL_STILL_RUN"
        else:
            original12=srcdir/"steel12_source_generators.json"
            if not original12.is_file():original12=None
            report["lemma_status"]["M3B-L10A_original_12_matrix_module"]=\
                ("PREEXISTING_JSON_NOT_REVALIDATED" if original12 else
                 "MISSING_SOURCE_JSON_WITH_SKIP_MAGMA")
        if args.actual_mod127_hom and args.manifest.exists():
            other127=[sys.executable,
                SCRIPTS/"monster3b_actual_mmv31_hom_projector.py",
                "--manifest",args.manifest,"--prime",127,
                "--outdir",out/"actual_mmv127_hom"]
            if (out/"mmgroup_canonical_cover_hit0.json").is_file():
                other127.extend(["--cover",
                    out/"mmgroup_canonical_cover_hit0.json"])
            ok127=run("actual_mod127_hom",other127)
            report["lemma_status"]["M3B-L10B_actual_mod127_Hom_vacuum"]=(
                "SECOND_SPLIT_GOOD_PRIME_SOURCE; NOT_COMPLEX_HOM"
                if ok127 else "FAILED")
        if original12 is not None:
            report["source12_json"]=str(original12);save()
            if run("derive90",[sys.executable,
                    SCRIPTS/"monster3b_steel_ordinary12_to90.py",
                    "--matrix-json",original12,"--out",
                    out/"ordinary12_derived90.json"]):
                report["lemma_status"]["M3B-L10C_inner_90_from_source12"]="DERIVED_EXACT"
            else:
                report["lemma_status"]["M3B-L10C_inner_90_from_source12"]="FAILED"
            if not args.skip_gap:
                if run("gap_fingerprint",[sys.executable,
                        SCRIPTS/"monster3b_gap_ordinary12_class_fingerprint.py",
                        "--source",original12,"--outdir",out,
                        "--run-gap","--timeout",args.timeout]):
                    report["lemma_status"]["M3B-L10A_class_orientation"]=\
                        "EXACT_FINGERPRINT_CANDIDATES_NOT_CANONICAL_CLASS_WORD"
                else:
                    report["lemma_status"]["M3B-L10A_class_orientation"]="GAP_FINGERPRINT_FAILED"
            else:
                report["lemma_status"]["M3B-L10A_class_orientation"]="DEFERRED"
        else:
            report["lemma_status"]["M3B-L10C_inner_90_from_source12"]=\
                "BLOCKED_ON_AUTHENTIC_STEEL_12_MATRICES"
            report["lemma_status"]["M3B-L10A_class_orientation"]=\
                "BLOCKED_ON_AUTHENTIC_STEEL_12_MATRICES"
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
        # Literal class4D via the genuine 196883 Monster character.
        # Independent of Steel/Magma and of the expensive full MMV(31)
        # projection.  Only a UNIQUE original GAP Monster class
        # position10 match can upgrade the local C-word to 4D.
        cover=out/"mmgroup_canonical_cover_hit0.json"
        if cover.is_file():
            classargs=[sys.executable,
                SCRIPTS/"monster3b_literal_mm_4d_character_class.py",
                "--cover",cover,"--outdir",out/"literal_MM_C_4D",
                "--timeout",args.timeout]
            if args.skip_gap:classargs.append("--skip-gap")
            if run("literal_MM_C_class4D",classargs):
                classreceipt=out/"literal_MM_C_4D/literal_MM_C_4D_status.json"
                if classreceipt.is_file():
                    classdata=json.loads(classreceipt.read_text())
                    report["literal_MM_C_class_status"]=classdata["status"]
                    report["specific_Hit0_MM_group_word_in_class_4D_identified"]=(
                        classdata.get("original_MM_C_4D_confirmed") is True)
                    report["lemma_status"]["M3B-L12R_literal_MM_4D_class"]=(
                        "EXACT_MONSTER_4D" if
                        report["specific_Hit0_MM_group_word_in_class_4D_identified"]
                        else "ORIGINAL_CHARACTER_CLASS_PENDING_OR_NOT_4D")
            else:
                report["lemma_status"]["M3B-L12R_literal_MM_4D_class"]=\
                    "CHARACTER_SOURCE_STAGE_FAILED"
        else:
            report["lemma_status"]["M3B-L12R_literal_MM_4D_class"]=\
                "BLOCKED_ON_AUTHENTIC_CANONICAL_MONSTER_WORD"

        # Reuse the prior exact 729 Schr/Weil compiler on the already
        # authenticated real MM-group quotient; no Steel/Magma, GAP or
        # 729D dense operator materialization is needed.
        cover=out/"mmgroup_canonical_cover_hit0.json"
        weilmodel=out/"source_original729_Weil_model.json"
        if cover.is_file():
            model_paid=run("original729_weil_model",[
                sys.executable,
                SCRIPTS/"monster3b_original729_weil_source_cocycle_weld.py",
                "--cover",cover,"--out",weilmodel])
            report["lemma_status"]["M3B-L10B_existing_729_Weil_kernel"]=( 
                "EXACT_CHOSEN_729_MODEL_COCYCLE_AND_R7_RELATOR" if model_paid
                else "EXISTING_729_MODEL_SOURCE_ALIGNMENT_FAILED")
        else:
            model_paid=False
            report["lemma_status"]["M3B-L10B_existing_729_Weil_kernel"]=\
                "BLOCKED_ON_AUTHENTIC_CORRECTED_GROUP_C_D_MATRICES"
        if args.actual_mod31_hom or args.both_mod31_phases:
            cover=out/"mmgroup_canonical_cover_hit0.json"
            if not args.manifest.exists():
                report["lemma_status"]["M3B-L10B_actual_mod31_Hom_vacuum"]=\
                    "MISSING_AUTHENTIC_MANIFEST"
            else:
                plus=(args.reuse_mod31_plus.resolve() if args.reuse_mod31_plus
                      else out/"actual_mmv31_hom")
                if args.reuse_mod31_plus:
                    state=json.loads((plus/"mmv31_hom_status.json").read_text())
                    if (state.get("p"),state.get("zeta_mod_p"),
                        state.get("number_independent_B_fixed_vectors"))!=(31,5,90):
                        raise ValueError("reused original mod31+ receipt has wrong phase/rank")
                    report["stages"]["actual_mod31_hom"]={
                        "status":"REUSED_PREVIOUS_AUTHENTIC_SOURCE",
                        "path":str(plus)}
                    positive=True
                else:
                    arguments=[sys.executable,
                        SCRIPTS/"monster3b_actual_mmv31_hom_projector.py",
                        "--manifest",args.manifest,
                        "--outdir",plus,"--prime",31]
                    if cover.exists():
                        arguments.extend(["--cover",cover])
                    positive=run("actual_mod31_hom",arguments)
                report["lemma_status"]["M3B-L10B_actual_mod31_Hom_vacuum"]=(
                    "GENUINE_MM31_MODULAR_PROJECTOR; NOT_COMPLEX_HOM"
                    if positive else "FAILED")
                if positive and model_paid:
                    if run("original729_actual_plus_vacuum_weld",[
                        sys.executable,
                        SCRIPTS/"monster3b_original729_actual_vacuum_weld.py",
                        "--model",weilmodel,"--phase1",plus,
                        "--outdir",out/"source729_actual_mod31_plus"]):
                        report["lemma_status"]["M3B-L10B_original729_MM31_plus_gauge"]=\
                            "MODEL_729_TO_ACTUAL_90_PROJECTIVE_COMPARISON_NOT_CHAR0"
                if positive and model_paid:
                    symlog=out/"actual_projective_12_sym2_78_plus.json"
                    if run("actual_same_word_projective_sym2_plus",[
                        sys.executable,
                        SCRIPTS/"monster3b_actual_order3_projective_sym2_weld.py",
                        "--model",weilmodel,"--plus",plus,"--out",symlog]):
                        data=json.loads(symlog.read_text())
                        report["lemma_status"]["M3B-L10C_projective_12_to_78_plus"]=\
                            data["status"]
                    else:
                        report["lemma_status"]["M3B-L10C_projective_12_to_78_plus"]=\
                            "ORIGINAL_SOURCE_CUBIC_OR_DUAL_SYM2_OBSTRUCTION"
                if positive and model_paid:
                    iso_dir=out/"actual_mod31_78_intertwiner_plus"
                    if run("actual_MM_78_to_dual_Sym2_12_plus_intertwiner",[
                        sys.executable,
                        SCRIPTS/"monster3b_actual_projective_sym2_intertwiner.py",
                        "--model",weilmodel,"--plus",plus,
                        "--outdir",iso_dir]):
                        value=json.loads((iso_dir/
                            "actual_MM_78_dualSym2_intertwiner_report.json").read_text())
                        report["lemma_status"]["M3B-L10C_same_MM_78_operator_intertwiner_plus"]=\
                            value["status"]
                    else:
                        report["lemma_status"]["M3B-L10C_same_MM_78_operator_intertwiner_plus"]=\
                            "ACTUAL_MM_78_SOURCE_OPERATOR_OBSTRUCTION"
                if args.both_mod31_phases and positive:
                    minus=out/"actual_mmv31_hom_opposite"
                    other=[sys.executable,
                        SCRIPTS/"monster3b_actual_mmv31_hom_projector.py",
                        "--manifest",args.manifest,"--outdir",minus,
                        "--prime",31,"--opposite-phase"]
                    if cover.exists():other.extend(["--cover",cover])
                    if run("actual_mod31_hom_opposite",other):
                        if model_paid:
                            if run("original729_actual_minus_vacuum_weld",[
                                sys.executable,
                                SCRIPTS/"monster3b_original729_actual_vacuum_weld.py",
                                "--model",weilmodel,"--phase2",minus,
                                "--outdir",out/"source729_actual_mod31_minus"]):
                                report["lemma_status"]["M3B-L10B_original729_MM31_minus_gauge"]=\
                                    "MODEL_729_TO_ACTUAL_OPPOSITE_PHASE_PROJECTIVE_COMPARISON"

                        if model_paid:
                            symlog=out/"actual_projective_12_sym2_78_both.json"
                            if run("actual_same_word_projective_sym2_both_phases",[
                                sys.executable,
                                SCRIPTS/"monster3b_actual_order3_projective_sym2_weld.py",
                                "--model",weilmodel,"--plus",plus,"--minus",minus,
                                "--out",symlog]):
                                data=json.loads(symlog.read_text())
                                report["lemma_status"]["M3B-L10C_projective_12_to_78_both"]=\
                                    data["status"]
                            else:
                                report["lemma_status"]["M3B-L10C_projective_12_to_78_both"]=\
                                    "ORIGINAL_SOURCE_CUBIC_OR_DUAL_SYM2_OBSTRUCTION"
                        if model_paid:
                            iso_dir=out/"actual_mod31_78_intertwiner_both"
                            if run("actual_MM_78_to_dual_Sym2_12_both_intertwiners",[
                                sys.executable,
                                SCRIPTS/"monster3b_actual_projective_sym2_intertwiner.py",
                                "--model",weilmodel,"--plus",plus,
                                "--minus",minus,"--outdir",iso_dir]):
                                value=json.loads((iso_dir/
                                    "actual_MM_78_dualSym2_intertwiner_report.json").read_text())
                                report["lemma_status"]["M3B-L10C_same_MM_78_operator_intertwiner_both"]=\
                                    value["status"]
                            else:
                                report["lemma_status"]["M3B-L10C_same_MM_78_operator_intertwiner_both"]=\
                                    "ACTUAL_MM_78_SOURCE_OPERATOR_OBSTRUCTION"
                        if run("quadratic12_character_lift",[
                            sys.executable,
                            SCRIPTS/"monster3b_quadratic12_character_lift.py",
                            "--plus",plus,"--minus",minus,
                            "--out",out/"quadratic12_character_candidates.json"]):
                            report["lemma_status"]["M3B-L10A_mod31_to_ordinary_character"]=\
                                "EXACT_BOUNDED_CANDIDATES; WEIL_PHASE_COHERENCE_NOT_YET_CLOSED"
                        if cover.is_file():
                            if run("actual_mod31_outer_phase_pair",[
                                sys.executable,
                                SCRIPTS/"monster3b_mm31_outer_phase_pair.py",
                                "--plus",plus,"--minus",minus,
                                "--manifest",args.manifest,"--cover",cover,
                                "--outdir",out/"actual_mod31_outer_phase_pair"]):
                                report["lemma_status"]["M3B-L12R_actual_MM31_outer_phase_pair"]=\
                                    "GENUINE_MOD31_OUTER_PROJECTIVE_ACTION; NOT_COMPLEX"
                            else:
                                report["lemma_status"]["M3B-L12R_actual_MM31_outer_phase_pair"]=\
                                    "ACTUAL_MOD31_OUTER_PHASE_SOURCE_FAILED"
                    else:
                        report["lemma_status"]["M3B-L10A_mod31_to_ordinary_character"]=\
                            "OPPOSITE_PHASE_PRODUCER_FAILED"
        if original12 is not None:
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
        else:
            report["lemma_status"]["M3B-L10B_complex_12_Hom_intertwiner"]=\
                "BLOCKED_ON_ORIGINAL_STEEL_12_AND_REAL_CHAR0_HOM"
            report["lemma_status"]["M3B-L12R_complex_outer_intertwiner"]=\
                "BLOCKED_ON_ORIGINAL_STEEL_12_AND_REAL_SOURCE_OUTER_WORD_MAP"
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
