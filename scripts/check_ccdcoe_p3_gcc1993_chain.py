#!/usr/bin/env python3
"""CCDCOE 1993 GCC source-chain audit: provenance and temporal order only.

No original scanned bytes are included; this verifies a constrained catalogue
transcription, not dispatch, delivery, publication influence or audience effects.
"""
import argparse
import copy
import json
from datetime import date
from pathlib import Path

MANIFEST=Path(__file__).resolve().parents[1]/"Docs/research/ccdcoe_p3_gcc1993_intervention_chain_20261109.json"
ORIGINAL={
 "january_expertise":("1993-01-04","gcc_communication","journalists","1993-climate-expertise-news-release"),
 "march_pre_response":("1993-03-10","gcc_communication","public_unspecified","1993-natural-warming-models-national-action-plan"),
 "may_reporters":("1993-05-03","gcc_communication","journalists","1993-response-clinton-earth-day-pledge"),
 "july_doe":("1993-07-08","gcc_communication","department_of_energy","1993-national-action-plan-doe-letter"),
 "july_whitehouse":("1993-07-19","gcc_communication","white_house","1993-white-house-cos-letter"),
 "archived_clippings":(None,"original_news_authors","public_readers_not_verified","1993-media-hits")}
EDGES=[
 ("january_expertise","march_pre_response"),
 ("march_pre_response","may_reporters"),
 ("may_reporters","july_doe"),
 ("july_doe","july_whitehouse")]
def require(c,m):
    if not c: raise ValueError(m)
def verify(data):
    require(data.get("schema")=="dashi.ccdcoe.p3.gcc1993_intervention_chain.v1","schema")
    items=data.get("objects",[])
    ids=[x["id"] for x in items]
    require(len(ids)==len(ORIGINAL) and len(set(ids))==len(ORIGINAL)
            and set(ids)==set(ORIGINAL),"unique original objects")
    by_id={x["id"]:x for x in items}
    for id,(date_s,author,target,slug) in ORIGINAL.items():
        x=by_id[id]
        require((x["date"],x["author_role"],x["target_role"])==(date_s,author,target),"original source identity "+id)
        require(x["source_url"]=="https://www.climatefiles.com/denial-groups/global-climate-coalition-collection/"+slug+"/","archive URL "+id)
        require(x["stage"]=="catalogue_listing","source grade promotion")
        require(bool(x["claim_scope"].strip()),"missing claim scope")
        if date_s:
            require(x["date_kind"]=="archive_catalogue_date_not_verified_dispatch","source date overclaimed")
            require(date.fromisoformat(x["date"]).isoformat()==date_s,"invalid date")
        else:
            require(x["date_kind"]=="multiple_article_dates_not_one_discrete_event","clippings falsely dated")
    edges=data.get("links",[])
    require(len(edges)==len(EDGES)
            and [(x["from"],x["to"]) for x in edges]==EDGES,"historical edge order")
    for edge in edges:
        a=by_id[edge["from"]]; b=by_id[edge["to"]]
        require(a["date"]<b["date"],"reverse chronological direction")
        require(edge["relationship"]=="archive_date_order_only","influence from mere ordering")
        for field in ("independent_delivery_verified","media_reuse_verified","mechanism_effect_verified"):
            require(edge[field] is False,"unsupported inference "+field)
    require("April 1998 API" in " ".join(data["negative_controls"]),
            "separate API authorship/chronology omitted")
    return {"source_catalogue_objects":len(items),"chronology_only_edges":len(edges),
            "independently_authenticated_original_bytes":0,
            "independently_verified_delivery":0,
            "observed_media_reuse_causal_links":0,
            "measured_audience_effects":0}

def self_test(m):
    valid=verify(m)
    def modify(id,field,value):
        return lambda d:next(x for x in d["objects"] if x["id"]==id).update({field:value})
    cases=[
        ("duplicate_object",lambda d:d["objects"].append(copy.deepcopy(d["objects"][0]))),
        ("backdated",modify("july_whitehouse","date","1993-04-01")),
        ("fused_newspaper_author",modify("archived_clippings","author_role","gcc_communication")),
        ("reporter_letter_fictional_receipt",lambda d:d["links"][1].update(independent_delivery_verified=True)),
        ("fictional_media_effect",lambda d:d["links"][2].update(media_reuse_verified=True)),
        ("fictional_mechanism_effect",lambda d:d["links"][0].update(mechanism_effect_verified=True)),
        ("wrong_source",modify("may_reporters","source_url","https://example.org")),
        ("promoted_archive_grade",modify("july_doe","stage","authenticated_original_bytes")),
        ("clippings_fake_single_date",modify("archived_clippings","date","1993-07-01")),
        ("wrong_actor_target",modify("july_doe","target_role","journalists")),
        ("wrong_march_date",modify("march_pre_response","date","1993-06-10")),
        ("march_false_recipient",modify("march_pre_response","target_role","journalists"))]
    for label,mutator in cases:
        d=copy.deepcopy(m);mutator(d)
        try:verify(d)
        except (ValueError,KeyError,TypeError):continue
        raise AssertionError("negative control accepted "+label)
    return dict(valid,negative_controls=len(cases))
if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--self-test",action="store_true")
    args=parser.parse_args()
    data=json.loads(MANIFEST.read_text(encoding="utf-8"))
    print(json.dumps(self_test(data) if args.self_test else verify(data),sort_keys=True,indent=2))
