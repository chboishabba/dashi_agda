#!/usr/bin/env python3
"""CCDCOE original-source claim-coding protocol and independent-coder audit.

No original GCC passage, coder observation or human response has been
authenticated. This validator does not invent those data. Synthetic tests
prove the arithmetic and rejection logic only.
"""
import argparse
import copy
import json
from collections import Counter
from pathlib import Path

PATH=Path(__file__).resolve().parents[1]/"Docs/research/ccdcoe_p3_gcc1993_claim_coding_protocol_20261109.json"
EXPECTED={"rensberger_original","hansen_original_correction","gcc_june_response","gcc_september_bulletin"}
DIMENSIONS={"uncertainty","scientific_voice","risk_time_horizon","responsibility","agency","selective_reuse"}
def require(condition,reason):
    if not condition:raise ValueError(reason)
def reliability(pairs):
    """Agreement and Cohen's kappa, without fabricated perfect kappa."""
    require(bool(pairs),"No paired coder observations")
    n=len(pairs)
    agreement=sum(a==b for a,b in pairs)/n
    labels=set(a for a,b in pairs)|set(b for a,b in pairs)
    left=Counter(a for a,b in pairs);right=Counter(b for a,b in pairs)
    chance=sum(left[z]*right[z] for z in labels)/(n*n)
    kappa=None if chance==1 else (agreement-chance)/(1-chance)
    return dict(n=n,observed_agreement=agreement,expected_chance_agreement=chance,kappa=kappa)
def audit(data):
    require(data.get("schema")=="dashi.ccdcoe.p3.gcc1993_claim_level_protocol.v1","schema")
    original=data["original_objects"]
    require(len(original)==4 and {x["id"] for x in original}==EXPECTED,"cohort identity")
    require(sum(x["analysis_eligible"] for x in original)==2,"archive summaries falsely admitted")
    require(all(x["byte_verified"] is False for x in original),"fabricated source hash")
    require(set(data["dimensions"])==DIMENSIONS,"coding ontology")
    for k,v in data["dimensions"].items():
        require("undeterminable" in v["codes"] and len(v["codes"])==len(set(v["codes"])),"missing-data coding "+k)
        require(len(v["rule"].strip())>20,"dimension lacks rule")
    protocol=data["coder_protocol"]
    require(protocol["independent_blind_coders"]==2,"independent coder design")
    require(protocol["passage_hash_required"] and protocol["source_offset_required"],"source passage provenance")
    require(protocol["no_inferred_nonmentions_from_missing_PDF"],"absent source not missing wording")
    require(data["admitted_original_passages"]==[] and data["independent_coder_observations"]==[] and data["causal_effect_estimates"]==[],"empirical observations fabricated")
    require(len(data["comparison_design"]["negative_controls"])>=4,"adversarial causal controls omitted")
    require(len(data["comparison_design"]["rival_explanations"])>=4,"competing explanations omitted")
    return {"source_objects":4,"publisher_rendered_sources":2,"unreviewed_GCC_PDF_sources":2,
            "independently_coded_passages":0,"identified_causal_effects":0,
            "coding_dimensions":len(DIMENSIONS),"independent_coder_records":0}
def self_test(data):
    result=audit(data)
    examples=[
        ("perfect_two_class",[("a","a"),("b","b")],1.0,1.0),
        ("balanced_disagreement",[("a","b"),("b","a")],0.0,-1.0),
        ("constant_class",[("a","a"),("a","a")],1.0,None),
    ]
    for name,pairs,pagree,pkappa in examples:
        measured=reliability(pairs)
        require(measured["observed_agreement"]==pagree,name+" observed")
        require(measured["kappa"]==pkappa,name+" kappa")
    defects=[
        ("admit_missing_GCC",lambda x:x["original_objects"][2].update(analysis_eligible=True)),
        ("invent_passage",lambda x:x["admitted_original_passages"].append({"fake":True})),
        ("invent_causal_effect",lambda x:x["causal_effect_estimates"].append({"effect":1})),
        ("lose_missing_code",lambda x:x["dimensions"]["uncertainty"]["codes"].remove("undeterminable")),
        ("fuse_authors",lambda x:x["original_objects"][1].update(id="rensberger_original")),
        ("lose_controls",lambda x:x["comparison_design"].update(negative_controls=[])),
        ("single_coder",lambda x:x["coder_protocol"].update(independent_blind_coders=1)),
        ("no_source_hash",lambda x:x["coder_protocol"].update(passage_hash_required=False)),
        ("invent_source_digest",lambda x:x["original_objects"][2].update(byte_verified=True)),
    ]
    for name,mutation in defects:
        changed=copy.deepcopy(data);mutation(changed)
        try:audit(changed)
        except (ValueError,KeyError):continue
        raise AssertionError("negative test admitted: "+name)
    return dict(result,negative_controls=len(defects),synthetic_kappa_cases=len(examples))
if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--self-test",action="store_true")
    a=p.parse_args();data=json.loads(PATH.read_text(encoding="utf-8"))
    print(json.dumps(self_test(data) if a.self_test else audit(data),indent=2,sort_keys=True))
