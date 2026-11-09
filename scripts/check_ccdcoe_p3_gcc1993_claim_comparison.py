#!/usr/bin/env python3
"""Source-grade cognitive-framing comparison without unsupported causal inference."""
import argparse
import copy
import json
from datetime import date
from pathlib import Path

PATH=Path(__file__).resolve().parents[1]/"Docs/research/ccdcoe_p3_gcc1993_claim_comparison_20261109.json"
KEYS={
 "rensberger_original":("Boyce Rensberger","publisher_primary_rendered","1993-05-31"),
 "hansen_original_correction":("James E. Hansen","publisher_primary_rendered","1993-06-08"),
 "gcc_june_response":("John Shlaes, Global Climate Coalition","archive_secondary_description_of_original_gcc_source","1993-06-30"),
 "gcc_september_bulletin":("Global Climate Coalition","archive_secondary_description_of_original_gcc_source","1993-09-01")}
EDGES=[
 ("rensberger_original","hansen_original_correction","published_response"),
 ("rensberger_original","gcc_june_response","archival_description_of_secondary_promotion"),
 ("hansen_original_correction","gcc_june_response","time_order_negative_control_only"),
 ("gcc_june_response","gcc_september_bulletin","chronological_comparison_only")]
def require(value,reason):
    if not value:raise ValueError(reason)
def check(m):
    require(m.get("schema")=="dashi.ccdcoe.p3.gcc1993_claim_comparison.v1","schema")
    objects=m["objects"]; o={x["id"]:x for x in objects}
    require(len(o)==len(objects)==len(KEYS) and set(o)==set(KEYS),"original source objects")
    for key,(author,grade,day) in KEYS.items():
        x=o[key]
        require((x["owner"],x["kind"],x["date"])==(author,grade,day),"original author/source grade")
        require(date.fromisoformat(x["date"]).isoformat()==day,"dated source")
        require(x["url"].startswith("https://"),"original URL")
        require(isinstance(x["source_observation"],str) and len(x["source_observation"])>=35,"bounded observation")
        require(bool(x["framing_tags"]) and len(set(x["framing_tags"]))==len(x["framing_tags"]),"claim coding")
        require(x["verified_authorial_awareness_of_future_sources"] is False,"invented awareness")
        require(x["actual_audience_effect_verified"] is False,"invented audience effects")
    require("May 31" in o["rensberger_original"]["date_conflict"] and "June 1" in o["rensberger_original"]["date_conflict"],"original publication date conflict")
    require("explicit_corrective_response" in o["hansen_original_correction"]["framing_tags"],"Hansen correction omitted")
    require("scientific_disagreement" in o["rensberger_original"]["framing_tags"],"original journalist's reported dissent erased")
    comparisons=m["comparisons"]
    require(len(comparisons)==len(EDGES),"comparison count")
    for x,(early,late,grade) in zip(comparisons,EDGES):
        require((x["earlier"],x["later"],x["grade"])==(early,late,grade),"causal direction or evidence grade")
        require(o[early]["date"]<o[late]["date"],"negative chronology control")
        require(x["intentional_omission_verified"] is False and x["causal_uptake_verified"] is False,"unsupported intent / uptake")
    return {"sources":len(o),"comparisons":len(comparisons),"independent_original_publisher_texts":2,
            "archive_described_unverified_original_GCC_PDFs":2,
            "verified_knowledge_or_deliberate_omission":0,"measured_causal_effects":0}
def self_test(m):
    positive=check(m)
    tests=[
      ("author",lambda x:x["objects"][1].update(owner="GCC")),
      ("source_grade",lambda x:x["objects"][2].update(kind="publisher_primary_rendered")),
      ("publisher_date",lambda x:x["objects"][0].update(date_conflict="June 1 only")),
      ("incorrect_sequence",lambda x:x["comparisons"][2].update(earlier="gcc_june_response")),
      ("omission_inferred",lambda x:x["comparisons"][2].update(intentional_omission_verified=True)),
      ("uptake_inferred",lambda x:x["comparisons"][1].update(causal_uptake_verified=True)),
      ("response_inferred",lambda x:x["objects"][3].update(actual_audience_effect_verified=True)),
      ("Hansen_correction_erased",lambda x:x["objects"][1].update(framing_tags=["long_term_risk"])),
      ("journalist_dissent_erased",lambda x:x["objects"][0].update(framing_tags=["near_term_benign"])),
      ("duplicate",lambda x:x["objects"].append(copy.deepcopy(x["objects"][0])))]
    for name,change in tests:
        y=copy.deepcopy(m);change(y)
        try:check(y)
        except (ValueError,KeyError):continue
        raise AssertionError("negative control accepted "+name)
    return dict(positive,negative_controls=len(tests))
if __name__=="__main__":
    parser=argparse.ArgumentParser();parser.add_argument("--self-test",action="store_true")
    a=parser.parse_args();m=json.loads(PATH.read_text(encoding="utf-8"))
    print(json.dumps(self_test(m) if a.self_test else check(m),sort_keys=True,indent=2))
