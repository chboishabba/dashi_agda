#!/usr/bin/env python3
"""GCC 1993 pre-response archival source-grade and time-index audit.

The dated source catalogue and selected excerpts are not substitute
for authentic original PDF bytes, complete-document coding, or effects.
"""
import argparse
import copy
import json
from datetime import date
from pathlib import Path

PATH=Path(__file__).resolve().parents[1]/"Docs/research/ccdcoe_p3_gcc_original_pre_response_baseline_20261109.json"
EXPECTED={
"gcc_1993_01_04_press_outreach":("1993-01-04","archive_description","1993-climate-expertise-news-release"),
"gcc_1993_03_08_policy_statement":("1993-03-08","archive_quoted_original_excerpt","1993-us-national-action-plan-recommendations"),
"gcc_1993_03_10_model_release":("1993-03-10","archive_description","1993-natural-warming-models-national-action-plan"),
"gcc_1993_undated_expert_brochure":(None,"archive_quoted_original_excerpt","1993-selected-climate-change-quotes")}
BASE="https://www.climatefiles.com/denial-groups/global-climate-coalition-collection/"
def require(ok,reason):
    if not ok:raise ValueError(reason)
def check(m):
    require(m.get("schema")=="dashi.ccdcoe.p3.original_gcc_pre_response_baseline.v1","schema")
    rows=m["objects"]; ids=[r["id"] for r in rows]
    require(len(rows)==len(EXPECTED) and len(set(ids))==len(EXPECTED) and set(ids)==set(EXPECTED),"source identity")
    byid={r["id"]:r for r in rows}
    for key,(day,grade,slug) in EXPECTED.items():
        row=byid[key]
        require(row["date"]==day and row["source_grade"]==grade,"archive source date/grade")
        require(row["url"]==BASE+slug+"/","original archive locator")
        require(row["original_actor"].startswith("Global Climate Coalition"),"originator")
        require(row["day_precision"]==("archive_calendar_date" if day else "circa_1993_unordered"),"date precision")
        require(row["archive_excerpt_present"] is (grade=="archive_quoted_original_excerpt"),"selected excerpt stage")
        require(row["original_bytes_authenticated"] is False and row["independent_coding_complete"] is False,"unsupported original-byte/review promotion")
        require(bool(row["topic_tags"]) and len(set(row["topic_tags"]))==len(row["topic_tags"]),"coding topics")
        if day:require(date.fromisoformat(day).isoformat()==day,"bad calendar date")
    require(byid["gcc_1993_03_08_policy_statement"]["date"]<byid["gcc_1993_03_10_model_release"]["date"],"missing policy-before-release baseline")
    require(byid["gcc_1993_undated_expert_brochure"]["date"] is None,"undated brochure ordered")
    claims=m["claims"]
    must={"baseline_8march_beyond_10march","baseline_before_newspaper","brochure_undated","catalogue_quote_not_verified_full_document"}
    require(len(claims)==len(must) and {c["claim_id"] for c in claims}==must,"claims identities")
    require(all(c["causal_link_established"] is False for c in claims),"date or quote promoted to effect")
    require(len(m["negative_controls"])>=5,"adversarial controls removed")
    return {"distinct_original_source_catalogue_objects":len(rows),"archive_quoted_excerpt_sources":2,
            "authenticated_original_PDF_bytes":0,"independent_coded_original_passages":0,
            "identified_communications_effects":0}
def self_test(data):
    accepted=check(data)
    changes=[
        ("remove_source",lambda x:x["objects"].pop()),
        ("fake_original_bytes",lambda x:x["objects"][1].update(original_bytes_authenticated=True)),
        ("promote_independent_coding",lambda x:x["objects"][3].update(independent_coding_complete=True)),
        ("postdate_policy",lambda x:x["objects"][1].update(date="1993-03-12")),
        ("date_undated_brochure",lambda x:x["objects"][3].update(date="1993-02-01")),
        ("promote_historic_causality",lambda x:x["claims"][0].update(causal_link_established=True)),
        ("miscredit_source",lambda x:x["objects"][2].update(original_actor="Boyce Rensberger")),
        ("invent_full_excerpt",lambda x:x["objects"][2].update(archive_excerpt_present=True)),
        ("switch_locator",lambda x:x["objects"][1].update(url="https://example.org")),
        ("duplicate_source",lambda x:x["objects"].append(copy.deepcopy(x["objects"][0]))),
        ("erase_counterhypotheses",lambda x:x.update(negative_controls=[]))]
    for name,edit in changes:
        m=copy.deepcopy(data);edit(m)
        try:check(m)
        except (ValueError,KeyError,TypeError):continue
        raise AssertionError("negative control admitted: "+name)
    return dict(accepted,negative_controls=len(changes))
if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--self-test",action="store_true")
    args=p.parse_args();m=json.loads(PATH.read_text(encoding="utf-8"))
    print(json.dumps(self_test(m) if args.self_test else check(m),sort_keys=True,indent=2))
