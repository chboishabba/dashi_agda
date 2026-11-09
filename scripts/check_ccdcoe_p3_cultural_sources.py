#!/usr/bin/env python3
"""Bibliographic/genre gates for CCDCOE P3 cultural source atlas.

A publisher synopsis or narrative work must not count as an original
empirical observation, a verified causal estimate or author endorsement.
"""
import json
from pathlib import Path
PATH=Path(__file__).resolve().parents[1]/"Docs/research/ccdcoe_p3_cultural_source_atlas_20261109.json"
CATEGORIES={
 "merchants_of_doubt":"historical_scholarship",
 "end_times_fascism":"political_analysis",
 "doppelganger":"cultural_political_analysis",
 "shock_doctrine":"historical_political_analysis",
 "global_green_new_deal":"policy_argument",
 "big_myth":"historical_scholarship",
 "new_climate_war":"climate_communication_analysis",
 "doubt_their_product":"science_policy_history",
 "heads_in_sand":"social_science_argument",
 "planet_humans":"documentary_argument",
 "dont_look_up":"fictional_satire",
 "merchants_documentary":"documentary_adaptation"}
def require(test,description):
    if not test: raise ValueError(description)
def validate(obj):
    require(obj.get("schema")=="dashi.ccdcoe.p3.cultural_source_atlas.v1","schema")
    items=obj["items"]; by_id={item["id"]:item for item in items}
    require(len(items)==len(CATEGORIES)==len(by_id) and set(by_id)==set(CATEGORIES),"work identity")
    for ident,kind in CATEGORIES.items():
        r=by_id[ident]
        require(r["kind"]==kind,"genre/author source identity")
        require(isinstance(r["authors"],str) and r["authors"].strip(),"missing author")
        require(isinstance(r["title"],str) and r["title"].strip(),"missing title")
        require(isinstance(r["year"],int) and 2000 <= r["year"] <= 2026,"year")
        require(r["url"].startswith("https://"),"original attributed URL")
        require(r["primary_text_fully_reviewed"] is False,"full-text review invented")
        require(r["empirical_causal_effect_verified"] is False,"causality invented")
        require(r["author_endorses_DASHI"] is False,"original author endorsement invented")
    require("Naomi Klein; Astra Taylor"==by_id["end_times_fascism"]["authors"],"2026 authorship")
    require("Naomi Oreskes; Erik M. Conway"==by_id["merchants_of_doubt"]["authors"],"2010 authorship")
    require("Noam Chomsky; Robert Pollin; editor C. J. Polychroniou"==by_id["global_green_new_deal"]["authors"],"Green New Deal credits")
    return {"bibliographic_source_objects":len(items),"original_full_texts_replicated":0,
            "real_world_causal_effects_from_artworks":0,"original_author_endorsements_inferred":0}
def self_test(data):
    result=validate(data)
    for ident,field,bad in [
        ("end_times_fascism","authors","Naomi Oreskes"),
        ("dont_look_up","kind","historical_scholarship"),
        ("planet_humans","empirical_causal_effect_verified",True),
        ("global_green_new_deal","primary_text_fully_reviewed",True),
        ("merchants_of_doubt","author_endorses_DASHI",True)]:
        copied=json.loads(json.dumps(data));next(x for x in copied["items"] if x["id"]==ident)[field]=bad
        try: validate(copied)
        except ValueError: pass
        else: raise AssertionError("negative control accepted "+ident+field)
    return dict(result,negative_controls=5)
if __name__=="__main__":
    import argparse
    a=argparse.ArgumentParser();a.add_argument("--self-test",action="store_true")
    opts=a.parse_args();obj=json.loads(PATH.read_text(encoding="utf-8"))
    print(json.dumps(self_test(obj) if opts.self_test else validate(obj),sort_keys=True))
