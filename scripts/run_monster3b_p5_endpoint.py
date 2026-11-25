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
import hashlib
import shutil
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
    ap.add_argument("--reuse-cover",type=Path,help="reuse the original corrected MM cover JSON; verify literal phase in a separate small stage")
    ap.add_argument("--skip-magma",action="store_true")
    ap.add_argument("--skip-gap",action="store_true")
    ap.add_argument("--actual-mod31-hom",action="store_true",
        help="also construct actual mmgroup MMV(31) 90D Hom vacuum and 12/78 C2 sectors")
    ap.add_argument("--require-char0-expression",action="store_true",help="fail unless exact source-bound characteristic-zero expression is produced")
    ap.add_argument("--legacy-projective-diagnostics",action="store_true",help="also run independent raw projective 78D searches; not required by the direct canonical source join")
    ap.add_argument("--both-mod31-phases",action="store_true",
        help="construct zeta=5 and 25 source Hom sectors, recover exact Qzeta12 candidate characters")
    ap.add_argument("--reuse-mod31-plus",type=Path,
        help="reuse prior authentic zeta=5 rank90 source folder; only build missing phase")
    ap.add_argument("--reuse-mod31-minus",type=Path,help="reuse complete original opposite-phase packet")
    ap.add_argument("--independent-minus",action="store_true",help="use independent opposite phase search instead of literal C transport")
    ap.add_argument("--actual-mod127-hom",action="store_true",
        help="independent original Monster MMV(127) 90D B-vacuum source")

    ap.add_argument("--timeout",type=int,default=900)
    ap.add_argument("--outdir",type=Path)
    args=ap.parse_args()
    if args.timeout<1:ap.error("--timeout must be >0")
    if args.require_char0_expression:args.both_mod31_phases=True
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
        lindsey_ok=run("lindsey_ordinary_signed_source",[sys.executable,
            SCRIPTS/"monster3b_lindsey_ordinary_signed.py",
            "--out",out/"lindsey_ordinary_signed.json"])
        report["lemma_status"]["M3B-L10A_L10C_Lindsey_ordinary_source"]=(
            "EXACT_ORDINARY_SIGNED_12_78_90_ATLAS_CHART" if lindsey_ok else "SOURCE_REPLAY_FAILED")
        original12=None
        source_path=srcdir/"d12.6Suz.nfdeg2.M"
        source_available=False
        if args.skip_magma:
            # Cached ordinary matrices are usable without the Magma source.
            # Lindsey is independently available and no network is needed.
            source_available=True
            report["stages"]["acquire"]={"status":"SKIPPED_MAGMA_EXPORT"}
        elif args.source_file:
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
                ("LINDSEY_SOURCE_AVAILABLE; STEEL_INDEPENDENT_DONOR_NOT_AVAILABLE" if lindsey_ok else "NO_ORDINARY_SOURCE_MATRICES")
            report["lemma_status"]["M3B-L10A_class_orientation"]=\
                "BLOCKED_ON_AUTHENTIC_STEEL_12_MATRICES"
        if args.reuse_cover:
            source_cover=args.reuse_cover.resolve()
            reuse_data=json.loads(source_cover.read_text())
            manifest_data=json.loads(args.manifest.read_text())
            if (reuse_data.get("actual_mmgroup_used") is not True or
                reuse_data.get("original_source_blob_sha")!=manifest_data.get("source_blob_sha") or
                not all(reuse_data.get(k) for k in ("canonical_C_word","canonical_D_word"))):
                raise ValueError("invalid reused source cover")
            shutil.copyfile(source_cover,out/"mmgroup_canonical_cover_hit0.json")
            report["stages"]["mmgroup_canonical_words"]={"status":"REUSED_ORIGINAL_COVER",
                "path":str(source_cover),"sha256":hashlib.sha256(source_cover.read_bytes()).hexdigest()}
        elif not args.skip_mmgroup:
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
        cover=out/"mmgroup_canonical_cover_hit0.json"
        phase_receipt=out/"literal_standard_D_phase.json"
        phase_paid=False
        if cover.is_file() and args.manifest.is_file():
            phase_paid=run("literal_standard_D_phase",[sys.executable,
                SCRIPTS/"monster3b_literal_standard_D_phase.py",
                "--manifest",args.manifest,"--cover",cover,"--out",phase_receipt])
            report["lemma_status"]["M3B-L12R_literal_standard_D_phase"]=(
                "ACTUAL_MM_STANDARD_WORD_AND_CENTRAL_RESIDUAL" if phase_paid else "SOURCE_PHASE_RESIDUAL")
            if phase_paid:
                report["original_source_6Suz_standard_generator_to_MM_word_identified"]=True
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
        # Independent source outer-2C class candidate, not the inner r/2B fusion.
        if not args.skip_gap:
            outer_class_ok=run("outer_C_source_class_fusion",[
                "gap","-q",SCRIPTS/"monster3b_atlas_outer_C_class_source_fusion.g"])
            report["lemma_status"]["M3B-L12R_outer_C_source_class_candidates"]=(
                "SOURCE_FUSION_LOG_AVAILABLE" if outer_class_ok else "SOURCE_FUSION_UNAVAILABLE")
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
        canonical_model=out/"canonical_signed_729_model.json"
        canonical_paid=False
        if cover.is_file():
            canonical_paid=run("canonical_signed_729_global_cochain",[
                sys.executable,SCRIPTS/"monster3b_global_parity_weil_section.py",
                "--cover",cover,"--out",canonical_model])
            report["lemma_status"]["M3B-L10B_global_model_Weil_cochain"]=(
                "CANONICAL_SIGNED_MODEL_SECTION" if canonical_paid else "MODEL_SOURCE_RESIDUAL")
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
                def original_phase(name,reuse,dest,root):
                    arguments=[sys.executable,SCRIPTS/"monster3b_actual_mmv31_hom_projector.py",
                        "--manifest",args.manifest,"--outdir",dest,"--prime",31]
                    if root==25:arguments.append("--opposite-phase")
                    if cover.exists():arguments.extend(["--cover",cover])
                    if reuse:
                        reuse=reuse.resolve()
                        state=json.loads((reuse/"mmv31_hom_status.json").read_text())
                        if (state.get("p"),state.get("zeta_mod_p"),
                            state.get("number_independent_B_fixed_vectors"))!=(31,root,90):
                            raise ValueError("reused original phase receipt has wrong phase/rank")
                        required=("actual_C2_12_78_mod31.npz","actual_C2_on_90_mod31.npz",
                            "actual_D_12_78_vacuum_sandwich_mod31.npz",
                            "actual_CDCinv_12_78_vacuum_sandwich_mod31.npz",
                            "actual_inner_pair_vacuum_cocycle_mod31.npz")
                        saved=json.loads(cover.read_text()) if cover.exists() else {}
                        if (all((reuse/f).is_file() for f in required) and
                            all(state.get(k) and state.get(k)==saved.get(k)
                                for k in ("canonical_C_word","canonical_D_word"))):
                            report["stages"][name]={"status":"REUSED_PREVIOUS_AUTHENTIC_SOURCE","path":str(reuse)}
                            return reuse,True
                        if not state.get("derived_from_plus"):
                            arguments.extend(["--reuse-basis",reuse])
                        elif root==25 and canonical_paid:
                            arguments.extend(["--derive-from-plus",plus])
                        else:
                            raise ValueError("derived packet requires canonical C transport")
                    elif root==25 and canonical_paid and not args.independent_minus:
                        arguments.extend(["--derive-from-plus",plus])
                    return dest,run(name,arguments)
                plus,positive=original_phase("actual_mod31_hom",args.reuse_mod31_plus,
                    out/"actual_mmv31_hom",5)
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
                legacy_search=args.legacy_projective_diagnostics or not (canonical_paid and args.both_mod31_phases)
                if positive and model_paid and legacy_search:
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
                    minus,opposite=original_phase("actual_mod31_hom_opposite",args.reuse_mod31_minus,
                        out/"actual_mmv31_hom_opposite",25)
                    if opposite:
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
                        if model_paid and legacy_search:
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
                                if model_paid and legacy_search and (iso_dir/"actual_MM_projective_Sym2_78_intertwiner_phase1.npz").is_file() and (iso_dir/"actual_MM_projective_Sym2_78_intertwiner_phase2.npz").is_file():
                                    joined=out/"signed_outer_raw_join"
                                    raw_ok=run("signed_outer_raw_packet_join",[
                                        sys.executable,SCRIPTS/"monster3b_signed_outer_sym2_join.py",
                                        "--inner",iso_dir,"--outer",out/"actual_mod31_outer_phase_pair",
                                        "--outdir",joined])
                                    report["lemma_status"]["M3B-L10C_signed_raw_outer_join"]=(
                                        "CONDITIONAL_RAW_PACKET_MATCH" if raw_ok else "RAW_PACKET_RESIDUAL")
                                if canonical_paid:
                                    full_join=out/"canonical_signed_normalizer"
                                    full_ok=run("canonical_signed_normalizer",[
                                        sys.executable,SCRIPTS/"monster3b_canonical_signed_normalizer_weld.py",
                                        "--model",canonical_model,"--plus",plus,"--minus",minus,
                                        "--outer",out/"actual_mod31_outer_phase_pair","--outdir",full_join])
                                    report["lemma_status"]["M3B-L10B_L10C_L12R_canonical_signed_mod31"]=(
                                        "SOURCE_BOUND_MOD31_SIGNED_GENERATOR_WELD" if full_ok else "CANONICAL_SOURCE_RESIDUAL")
                                    if full_ok:
                                        source_join=run("lindsey_actual_MM31_source_join",[
                                            sys.executable,SCRIPTS/"monster3b_lindsey_actual_mod31_join.py",
                                            "--cover",cover,"--model",canonical_model,"--packet-dir",full_join,
                                            "--outdir",out/"lindsey_actual_MM31"])
                                        report["lemma_status"]["M3B-L10A_L10B_L10C_L12R_Lindsey_MM31"]=(
                                            "SOURCE_BOUND_SIGNED_MOD31_12_78_WELD" if source_join else "SOURCE_JOIN_RESIDUAL")
                                        if source_join and phase_paid:
                                            char0=run("exact_char0_Hom_expression",[sys.executable,
                                                SCRIPTS/"monster3b_char0_reynolds_witness.py",
                                                "--manifest",args.manifest,"--cover",cover,"--phase",phase_receipt,
                                                "--model",canonical_model,"--outer",out/"actual_mod31_outer_phase_pair",
                                                "--canonical",full_join,"--join",out/"lindsey_actual_MM31",
                                                "--plus",plus,"--minus",minus,"--out",out/"exact_char0_Hom_expression.json"])
                                            report["lemma_status"]["M3B-L10B_L10C_exact_char0_Hom_expression"]=(
                                                "EXACT_GROUP_ALGEBRA_WITNESS_NOT_DENSE_EVALUATION" if char0 else "CHAR0_EXPRESSION_SOURCE_RESIDUAL")

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
                ("LINDSEY_SOURCE_AVAILABLE; NEEDS_ACTUAL_CHAR0_HOM" if lindsey_ok else "BLOCKED_ON_ORDINARY_SOURCE_AND_REAL_CHAR0_HOM")
            report["lemma_status"]["M3B-L12R_complex_outer_intertwiner"]=\
                ("LINDSEY_SIGNED_SOURCE_AVAILABLE; NEEDS_ACTUAL_MM_Q7_AND_CHAR0_HOM" if lindsey_ok else "BLOCKED_ON_ORDINARY_SOURCE_AND_REAL_SOURCE_OUTER_WORD_MAP")
        exact_paid=report["lemma_status"].get("M3B-L10B_L10C_exact_char0_Hom_expression")=="EXACT_GROUP_ALGEBRA_WITNESS_NOT_DENSE_EVALUATION"
        report["status"]=("EXACT_CHAR0_EXPRESSION_PRODUCED_NOT_DENSE_EVALUATION" if exact_paid else
            "REQUIRED_CHAR0_EXPRESSION_UNPAID" if args.require_char0_expression else
            "STAGED_MATHEMATICAL_ENDPOINTS_WITH_REMAINING_SOURCE_ATTACHMENT")
    except Exception as exc:
        report["status"]="ERROR_FAIL_CLOSED"
        report["error"]={"type":type(exc).__name__,"message":str(exc),
                         "traceback":traceback.format_exc(limit=7)}
    finally:
        save()
    print("MONSTER3B_P5_STATUS:",report["status"])
    print("ENDPOINT_SUMMARY:",summary)
    print("SOURCE_CHECKS:",json.dumps(report["lemma_status"],indent=2))
    return 2 if report["status"] in ("ERROR_FAIL_CLOSED","REQUIRED_CHAR0_EXPRESSION_UNPAID") else 0
if __name__=="__main__":raise SystemExit(main())
