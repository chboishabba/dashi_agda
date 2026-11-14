#!/usr/bin/env python3
"""Original G20 Research Group member-level fossil-subsidy compliance audit.

This verifies the arithmetical consistency and member alignment of a
source-attributed web-table transcription. It is NOT original-byte
verification, physical emissions measurement, or causal identification.
"""
import json
from pathlib import Path
from collections import Counter

ROOT=Path(__file__).resolve().parents[1]
PATH=ROOT/"Docs/research/ccdcoe_p3_g20rg_fossil_member_transcription.json"

def need(condition, message):
    if not condition:
        raise ValueError(message)

def validate(data):
    need(data["schema"]=="dashi.ccdcoe.p3.g20rg.fossil_member_transcription.v1","schema")
    a,b=data["source_rows"]
    need((a["study_id"],b["study_id"])==("brisbane2014_final_G20RG","antalya2015_final_G20RG"),"study owners")
    need(a["assessment_window"]==["2014-11-16","2015-10-01"],"Brisbane window")
    need(b["assessment_window"]==["2015-11-16","2016-09-05"],"Antalya window")
    need(a["commitment_id"]!=b["commitment_id"],"different commitments fused")
    aligned=[]
    for row in (a,b):
        entries=row["member_scores"]
        need(len(entries)==20,"20 members including EU")
        names=[e["member"] for e in entries]
        codes=[e["code"] for e in entries]
        need(len(set(names))==len(set(codes))==20,"duplicated member")
        need(codes[-1]=="EU" and codes.count("EU")==1,"EU distinct assessed member")
        vals=[e["score"] for e in entries]
        need(all(type(v) is int and v in (-1,0,1) for v in vals),"original scoring scale")
        calc=sum(vals)*100//20
        need(calc==row["reported_narrative_score_hundredths"],"member arithmetic disagrees with report narrative")
        need((calc+100)//2 in (row["reported_narrative_percent"],
                                  row["reported_narrative_percent"]-1),"reported rounded percentage")
        need(row["url"].startswith("https://") and "g20.utoronto.ca" in row["url"],"original research report URL")
        aligned.append(dict(zip(codes,vals)))
    need(set(aligned[0])==set(aligned[1]),"member cohorts not aligned")
    need(a["reported_table_score_hundredths"]==-40 and
         a["reported_narrative_score_hundredths"]==-45,"Brisbane printed discrepancy not retained")
    need(b["reported_table_score_hundredths"]==-35,"Antalya original table summary")
    before,after=aligned
    transitions=Counter((before[k],after[k]) for k in before)
    return {"source_status":"web_table_transcription_not_original_byte_verified",
            "assessed_members_including_EU":len(before),
            "original_member_score_rows":40,
            "brisbane_calculated_mean":sum(before.values())/20,
            "antalya_calculated_mean":sum(after.values())/20,
            "brisbane_printed_table_mean":-0.40,
            "brisbane_printed_mean_conflicts_with_member_arithmetic":True,
            "paired_higher":sum(after[k]>before[k] for k in before),
            "paired_lower":sum(after[k]<before[k] for k in before),
            "paired_unchanged":sum(after[k]==before[k] for k in before),
            "transitions":{str(k):v for k,v in sorted(transitions.items())},
            "cross_summit_causal_effect_identified":False,
            "country_level_emissions_effect_identified":False}

def self_test():
    original=json.loads(PATH.read_text(encoding="utf-8"))
    positive=validate(original)
    need(positive["original_member_score_rows"]==40,"positive audit")
    for modifier in ("duplicate","tamper","fuse","round","EU"):
        changed=json.loads(json.dumps(original))
        if modifier=="duplicate":
            changed["source_rows"][0]["member_scores"][1]["code"]="ARG"
        elif modifier=="tamper":
            changed["source_rows"][0]["member_scores"][0]["score"]=1
        elif modifier=="fuse":
            changed["source_rows"][1]["commitment_id"]=changed["source_rows"][0]["commitment_id"]
        elif modifier=="round":
            changed["source_rows"][0]["reported_table_score_hundredths"]=-45
        else:
            changed["source_rows"][0]["member_scores"][-1]["code"]="FRA"
        try: validate(changed)
        except ValueError: pass
        else: raise AssertionError("negative control accepted "+modifier)
    return dict(positive,synthetic_negative_controls=5)

if __name__=="__main__":
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument("--self-test",action="store_true")
    args=parser.parse_args()
    print(json.dumps(self_test() if args.self_test else validate(json.loads(PATH.read_text(encoding="utf-8"))),
                     sort_keys=True,indent=2))
