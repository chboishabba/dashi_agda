#!/usr/bin/env python3
"""CCDCOE cognitive-warfare discriminator and source-cohort attribution audit.

Checks claims about evidence stage and whether all necessary gates have
actual independently validated records. No empirical causal inference is
produced by these assertions or from documentary/artistic source metadata.
"""
import argparse
import copy
import json
from pathlib import Path

PATH=Path(__file__).resolve().parents[1]/"Docs/research/ccdcoe_p3_cognitive_warfare_case_discriminator_20261109.json"
CASES={
 "gcc_harrison_1993_1995":("historical_actor_self_report",False),
 "gcc_clippings_1993":("source_indexed_media_archive",False),
 "api_draft_1998":("contemporaneous_proposed_plan",False),
 "supran_oreskes_2017":("published_document_metrics_not_reanalysed_microdata",True),
 "leon_films":("edition_metadata_only",False),
 "dont_look_up_satire":("film_metadata_only",False),
 "planet_humans_documentary":("author_publication_and_claims_not_independently_reviewed",False)}
REQUIRED={"exposure","mechanism","causality","intent_targeting"}

def require(p,m):
    if not p: raise ValueError(m)

def validate(obj):
    require(obj.get("schema")=="dashi.ccdcoe.p3.cognitive_warfare_discrimination.v1","schema")
    rows=obj["cases"]
    ids=[r["id"] for r in rows]
    require(len(ids)==len(CASES) and len(set(ids))==len(CASES) and set(ids)==set(CASES),"source cohort identity")
    for r in rows:
        stage,content=CASES[r["id"]]
        require(r["evidence_grade"]==stage and r["measured_content_change"] is content,"evidence grade / original coded content")
        require(r["primary_source"].startswith("https://") and bool(r["subject"].strip()),"original source attribution")
        require(bool(r["cautions"]),"original epistemic limitation omitted")
        for v in ("measured_audience_response","causal_effect_identified","hostile_intent_identified"):
            require(r[v] is False,"unsupported operation-promoting field: "+v)
    gates=obj["discriminator_requirements"]
    require({g["gate"] for g in gates}==REQUIRED and len(gates)==len(REQUIRED),"four distinct discriminator gates")
    for g in gates:
        require(bool(g["question"].strip()) and bool(g["necessary"].strip()),"genuine falsifiable design needed")
        require(g["observed"] is False,"independent records missing: "+g["gate"])
    require("Supran" in obj["original_source_credit"] or "original" in obj["original_source_credit"].lower(),"original-source credit")
    return {"historically_or_culturally_attributed_cases":len(rows),
            "source_document_metric_cases":sum(r["measured_content_change"] for r in rows),
            "independent_cognitive_warfare_identifications":0,
            "identified_audience_effects":0,
            "required_original_evidence_gates":len(gates),
            "unpaid_independent_evidence_gates":sum(not g["observed"] for g in gates)}
def self_test(base):
    positive=validate(base)
    mutations=[
      ("duplicate_case",lambda x:x["cases"].append(copy.deepcopy(x["cases"][0]))),
      ("self_report_promoted",lambda x:x["cases"][0].update(causal_effect_identified=True)),
      ("fiction_promoted",lambda x:x["cases"][5].update(measured_audience_response=True)),
      ("corpus_reclassified",lambda x:x["cases"][3].update(measured_content_change=False)),
      ("intent_promoted",lambda x:x["cases"][1].update(hostile_intent_identified=True)),
      ("missing_control",lambda x:x["discriminator_requirements"].pop()),
      ("unverified_control",lambda x:x["discriminator_requirements"][2].update(observed=True))]
    for label,change in mutations:
        altered=copy.deepcopy(base);change(altered)
        try:validate(altered)
        except ValueError:continue
        raise AssertionError("negative control accepted: "+label)
    return dict(positive,synthetic_negative_controls=len(mutations))
if __name__=="__main__":
    parser=argparse.ArgumentParser();parser.add_argument("--self-test",action="store_true")
    a=parser.parse_args();data=json.loads(PATH.read_text(encoding="utf-8"))
    print(json.dumps(self_test(data) if a.self_test else validate(data),sort_keys=True,indent=2))
