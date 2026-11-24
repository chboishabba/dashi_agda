#!/usr/bin/env python3
"""M3B-L10A: match Steel's actual Q(zeta3) word fingerprints to BOTH
original CTblLib 6.Suz faithful12 character rows, retaining ambiguity.

Required input: original Magma export from monster3b_steel_magma_export.py,
including exact order/trace/trace_square of genuine Group(M) words.

This does NOT assume Magma Group(M).i equals ATLAS/MM standard C,D.
An unmarked class fingerprint can have several original 6.Suz classes
and can be compatible with both 12a/12b Galois orientations. Never
choose a position from a tie or mistake this for an MM element word.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
import re
import shutil
import subprocess

SCHEMA="monster3b-steel6suz-ordinary12-v1"
def expression(v):
    if not isinstance(v,list) or len(v)!=2:raise ValueError("trace must be [a,b]")
    q=[Fraction(x) for x in v]
    return f"({q[0]})+({q[1]})*E(3)"
def quoted(x):
    if not re.fullmatch(r"[G0-9.*^-]{1,80}",x):
        raise ValueError("invalid source group-word token")
    return json.dumps(x)
def generate(data,output):
    if data.get("schema")!=SCHEMA:raise ValueError("invalid original Magma exporter input")
    fingers=data.get("fingerprints")
    if not isinstance(fingers,list) or not fingers:
        raise ValueError("missing actual Group(M) word fingerprints")
    body=[]
    for rec in fingers:
        label=rec["word"]
        order=rec["group_order"]
        if type(order)!=int or order<1 or order>1000000:
            raise ValueError("source group order invalid")
        body.append((label,order,expression(rec["trace"]),expression(rec["trace_square"])))
    # Only actual GAP/CTblLib resolves class positions; source words are
    # fingerprints, not a fully-paid abstract->actual word map.
    lines=[
        'if LoadPackage("ctbllib") <> true then Error("CTblLib required"); fi;',
        'six := CharacterTable("6.Suz");',
        'if Size(six) <> 2690072985600 or NrConjugacyClasses(six) <> 210 then',
        '  Error("wrong original 6.Suz table"); fi;',
        'irr := Irr(six); ord := OrdersClassRepresentatives(six);',
        'square := PowerMap(six,2);',
        'if irr[153][1] <> 12 or irr[154][1] <> 12 then',
        '  Error("selected source faithful12 positions changed"); fi;',
        'PairList := function(xs)',
        '  local s,i;',
        '  s := "[";',
        '  for i in [1..Length(xs)] do',
        '    if i > 1 then Append(s,","); fi;',
        '    Append(s,String(xs[i]));',
        '  od;',
        '  Append(s,"]"); return s;',
        'end;',
        'out := "{\\"schema\\":\\"monster3b-Steel-original12-GAP-class-fingerprint-v1\\",\\"words\\":[";',
    ]
    for i,(word,order,tr,tr2) in enumerate(body):
        lines.extend([
            f'c153 := Filtered([1..210], k -> ord[k]={order} and irr[153][k]={tr} and irr[153][square[k]]={tr2});',
            f'c154 := Filtered([1..210], k -> ord[k]={order} and irr[154][k]={tr} and irr[154][square[k]]={tr2});',
            'if Length(c153)=0 and Length(c154)=0 then',
            f' Error("original source group-word fingerprint absent in 6.Suz at row {i+1}"); fi;',
            ('Append(out,",");' if i else ''),
            'Append(out,'+json.dumps('{"word":'+json.dumps(word))+');',
            'Append(out,",\\"row153_classes\\":"); Append(out,PairList(c153));',
            'Append(out,",\\"row154_classes\\":"); Append(out,PairList(c154));',
            'Append(out,"}");',
        ])
    lines += ['Append(out,"]}");',
              'PrintTo('+json.dumps(str(output.resolve()))+',out);',
              'Print("STEEL_ORDINARY12_GAP_SOURCE_FINGERPRINT_WRITTEN\\n");','QUIT;']
    return "\n".join(x for x in lines if x)+"\n"
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source",type=Path,default=Path(
        ".dashi/monster3b-steel-ordinary12/steel12_source_generators.json"))
    ap.add_argument("--outdir",type=Path,default=Path(".dashi/monster3b-steel-ordinary12"))
    ap.add_argument("--run-gap",action="store_true")
    ap.add_argument("--timeout",type=int,default=900)
    args=ap.parse_args()
    if args.timeout<1:ap.error("--timeout must be positive")
    data=json.loads(args.source.read_text())
    args.outdir.mkdir(parents=True,exist_ok=True)
    output=args.outdir/"steel12_original_gap_class_candidates.json"
    stage=args.outdir/"stage_steel12_gap_fingerprint.g"
    stage.write_text(generate(data,output))
    state={"status":"STAGED","source_sha256":hashlib.sha256(args.source.read_bytes()).hexdigest(),
      "stage":str(stage),"output":str(output),
      "original_6Suz_generator_word_to_GAP_class_paid":False,
      "original_6Suz_generator_word_to_Monster_MM_paid":False}
    if args.run_gap:
        exe=shutil.which("gap")
        if exe is None:ap.error("GAP executable missing from PATH")
        cp=subprocess.run([exe,"-q",str(stage)],stdout=subprocess.PIPE,
           stderr=subprocess.STDOUT,text=True,timeout=args.timeout,check=False)
        (args.outdir/"steel12_gap_class.log").write_text(cp.stdout)
        if cp.returncode!=0 or not output.is_file():
            state["status"]="ERROR";state["error"]=cp.stdout[-2400:]
        else:
            receipt=json.loads(output.read_text())
            rows=receipt["words"]
            state["status"]="CLASS_FINGERPRINTS_AMBIGUOUS_OR_CANDIDATES"
            state["all_words_have_some_source_12_class"]=all(
                x["row153_classes"] or x["row154_classes"] for x in rows)
            state["row153_all_words_compatible"]=all(x["row153_classes"] for x in rows)
            state["row154_all_words_compatible"]=all(x["row154_classes"] for x in rows)
            state["original_source_12_irr_orientation_can_be_uniquely_named_from_fingerprints"]=(
                state["row153_all_words_compatible"]!=state["row154_all_words_compatible"])
            if not state["all_words_have_some_source_12_class"]:
                state["status"]="SOURCE_FINGERPRINT_MISMATCH"
    status=args.outdir/"steel12_gap_fingerprint_status.json"
    status.write_text(json.dumps(state,indent=2,sort_keys=True)+"\n")
    print(json.dumps(state,indent=2))
    return 0 if state["status"] not in ("ERROR","SOURCE_FINGERPRINT_MISMATCH") else 2
if __name__=="__main__":raise SystemExit(main())
