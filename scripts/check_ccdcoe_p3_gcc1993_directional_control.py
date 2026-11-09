#!/usr/bin/env python3
"""Audit direction, original authorship and evidentiary non-promotion.

No live URL fetch or PDF byte authentication. Original sources and
historical claims belong to the named journalists and institutions.
"""
import argparse
import copy
import json
from datetime import date
from pathlib import Path

FILE=Path(__file__).resolve().parents[1]/"Docs/research/ccdcoe_p3_gcc1993_directional_negative_control_20261109.json"
EXPECTED={
 "wp_rensberger_19930601":("1993-06-01","independent_newspaper_article"),
 "gcc_shlaes_19930630":("1993-06-30","gcc_response_to_existing_article"),
 "hansen_rebuttal_19930608":("1993-06-08","independently_authored_scientist_rebuttal"),
 "wp_christy_spencer_199307":("1993-07","independent_newspaper_article"),
 "gcc_september_bulletin_1993":("1993-09","gcc_republishes_reference_to_article")}
EDGES=[
 ("wp_rensberger_19930601","hansen_rebuttal_19930608","original_publisher_authored_reply"),
 ("wp_rensberger_19930601","gcc_shlaes_19930630","archive_description_of_reference"),
 ("wp_christy_spencer_199307","gcc_september_bulletin_1993","archive_description_of_later_amplification"),
 ("wp_rensberger_19930601","gcc_september_bulletin_1993","archive_description_of_later_amplification"),
 ("hansen_rebuttal_19930608","gcc_september_bulletin_1993","preexisting_counterevidence_not_proven_seen_or_selected")]

def require(ok,reason):
    if not ok: raise ValueError(reason)

def review(m):
    require(m.get("schema")=="dashi.ccdcoe.p3.gcc1993_directed_original_source_relations.v1","schema")
    objs=m["objects"]
    byid={o["id"]:o for o in objs}
    require(len(objs)==len(byid)==len(EXPECTED) and set(byid)==set(EXPECTED),"source IDs")
    for k,(d,role) in EXPECTED.items():
        o=byid[k]
        require(o["date"]==d and o["role"]==role,"source role/date")
        require(o["source"].startswith("https://www.climatefiles.com/denial-groups/global-climate-coalition-collection/"),"source locator")
        require(o["creator"].strip(),"original author")
        if len(d)==10:require(date.fromisoformat(d).isoformat()==d,"date syntax")
        else:require(len(d)==7,"month precision")
    require("Boyce Rensberger" in byid["wp_rensberger_19930601"]["creator"],"journalist credit")
    require("John Shlaes" in byid["gcc_shlaes_19930630"]["creator"],"GCC author credit")
    r=byid["wp_rensberger_19930601"]
    require(r["page_display_date"]=="1993-05-31" and r["archive_url_date"]=="1993-06-01", "publisher/archive disagreement erased")
    require(r["original_publisher_url"].startswith("https://www.washingtonpost.com/archive/politics/1993/06/01/"),"original publisher locator")
    require(r["source_grade"]=="original_publisher_rendered_article_not_independent_binary_archive","false source-byte verification")
    voices=r["original_content_observations"]
    require(len(voices)==3,"original article multiple speakers")
    require(all(len(c["original_page_lines"])==2 and c["original_page_lines"][0]<c["original_page_lines"][1] for c in voices),"original article line references")
    require("Patrick Michaels" in voices[1]["attributed_speaker"] and "James Hansen" in voices[2]["attributed_speaker"],"opposing source voices conflated")
    rebuttal=byid["hansen_rebuttal_19930608"]
    require("James E. Hansen" in rebuttal["creator"] and rebuttal["source"].startswith("https://www.washingtonpost.com/archive/opinions/1993/06/08/"),"original independent rebuttal")
    require(rebuttal["original_byte_digest_verified"] is False,"rebuttal bytes falsely authenticated")
    bulletin=byid["gcc_september_bulletin_1993"]
    require(bulletin["archived_edition"]=="Climate Watch Volume 1, Issue 9","exact original bulletin edition")
    require(bulletin["source"]=="https://www.climatefiles.com/denial-groups/global-climate-coalition-collection/1993-climate-watch-vol-1-issue-9/","bulletin original archive locator")
    links=m["links"]
    require(len(links)==len(EDGES),"link count")
    for link,(a,b,grade) in zip(links,EDGES):
        require((link["earlier"],link["later"],link["evidence_kind"])==(a,b,grade),"link orientation/source grade")
        require(byid[a]["date"]<byid[b]["date"],"later article falsely causes earlier original")
        require(bool(link["original_source_relationship"].strip()),"relation description")
        for k in ("journalist_exposure_verified","original_article_GCC_causation_verified","audience_effect_verified"):
            require(link[k] is False,"unsupported causal promotion: "+k)
    return {"source_objects":len(objs),"directional_source_mentions":len(links),
            "original_publisher_articles_and_letters":2,"original_publisher_date_discrepancies":1,
            "original_counterresponse_public_before_GCC":True,
            "verified_article_causation":0,"verified_audience_exposure":0,
            "verified_population_effect":0}

def self_test(m):
    positive=review(m)
    mods=[
      ("flip_first",lambda x:x["links"][0].update(earlier="gcc_shlaes_19930630")),
      ("flip_second",lambda x:x["links"][1].update(later="wp_christy_spencer_199307")),
      ("replace_author",lambda x:next(o for o in x["objects"] if o["id"]=="wp_rensberger_19930601").update(creator="GCC")),
      ("backdate_response",lambda x:next(o for o in x["objects"] if o["id"]=="gcc_shlaes_19930630").update(date="1993-05-01")),
      ("promote_article",lambda x:x["links"][0].update(original_article_GCC_causation_verified=True)),
      ("promote_exposure",lambda x:x["links"][1].update(journalist_exposure_verified=True)),
      ("promote_effect",lambda x:x["links"][1].update(audience_effect_verified=True)),
      ("fake_grade",lambda x:x["links"][0].update(evidence_kind="independent_causal_inference")),
      ("duplicate",lambda x:x["objects"].append(copy.deepcopy(x["objects"][0]))),
      ("date_discrepancy_erased",lambda x:next(o for o in x["objects"] if o["id"]=="wp_rensberger_19930601").update(page_display_date="1993-06-01")),
      ("Hansen_voice_erased",lambda x:next(o for o in x["objects"] if o["id"]=="wp_rensberger_19930601")["original_content_observations"][2].update(attributed_speaker="GCC")),
      ("Hansen_response_author_fused",lambda x:next(o for o in x["objects"] if o["id"]=="hansen_rebuttal_19930608").update(creator="GCC")),
      ("Hansen_response_postdated",lambda x:next(o for o in x["objects"] if o["id"]=="hansen_rebuttal_19930608").update(date="1993-07-08")),
      ("bulletin_issue_erased",lambda x:next(o for o in x["objects"] if o["id"]=="gcc_september_bulletin_1993").update(archived_edition="unknown")),
      ("Hansen_bytes_fabricated",lambda x:next(o for o in x["objects"] if o["id"]=="hansen_rebuttal_19930608").update(original_byte_digest_verified=True))]
    for label,modify in mods:
        changed=copy.deepcopy(m);modify(changed)
        try: review(changed)
        except (ValueError,KeyError):continue
        raise AssertionError("negative control accepted "+label)
    return dict(positive,negative_controls=len(mods))
if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--self-test",action="store_true")
    a=p.parse_args();data=json.loads(FILE.read_text(encoding="utf-8"))
    print(json.dumps(self_test(data) if a.self_test else review(data),sort_keys=True,indent=2))
