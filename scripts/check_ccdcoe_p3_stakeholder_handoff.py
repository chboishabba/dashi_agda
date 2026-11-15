#!/usr/bin/env python3
"""Admissibility audit for original G20/C20/B20 handoff evidence.

Attribution and chronology only. No documented handoff is silently
promoted into authorship, negotiator uptake, or policy causation.
"""
import json
from pathlib import Path
PATH=Path(__file__).resolve().parents[1]/"Docs/research/ccdcoe_p3_stakeholder_handoff_evidence.json"
EXPECTED={
 "c20_2015_handoff":("2015-09-16","turkish_presidency_report_of_receipt","documented_receipt"),
 "b20_2015_reported_presentation":("2015-09","ICC_participant_retrospective_report","attributed_report_of_presentation"),
 "ministerial_2015_prior_text":("2015-10-02","original_ministerial_adopted_text","published_adopted_text"),
 "b20_energy_2015_statement":("2015-10-12","original_stakeholder_document","published_recommendation")}
def require(condition,why):
    if not condition: raise ValueError(why)
def check(d):
    require(d.get("schema")=="dashi.ccdcoe.p3.stakeholder_handoff.v1","schema")
    rows=d["events"]; byid={x["id"]:x for x in rows}
    require(len(rows)==len(byid)==4 and set(byid)==set(EXPECTED),"source identities")
    for k,(date,kind,stage) in EXPECTED.items():
        r=byid[k]
        require((r["event_date"],r["source_kind"],r["evidentiary_stage"])==(date,kind,stage),"source type/date altered")
        require(r["source_url"].startswith("https://"),"original source URL")
        for field in ("draft_version_identity","adopted_clause_uptake","causal_policy_influence"):
            require(r[field] is None,"unsupported evidence promoted: "+field)
    require(byid["ministerial_2015_prior_text"]["event_date"] <
            byid["b20_energy_2015_statement"]["event_date"],"later text backdated")
    return {"documented_C20_receipt":True,"attributed_B20_presentation":True,
            "ministerial_before_B20_publication":True,
            "proven_policy_clause_uptake":False,"causal_attribution":False}
def self_test(d):
    check(d)
    for key,field,value in (
        ("c20_2015_handoff","adopted_clause_uptake","Paris Article 4"),
        ("b20_2015_reported_presentation","causal_policy_influence",True),
        ("ministerial_2015_prior_text","event_date","2015-10-15"),
        ("b20_energy_2015_statement","draft_version_identity","unknown asserted original")):
        bad=json.loads(json.dumps(d)); next(x for x in bad["events"] if x["id"]==key)[field]=value
        try: check(bad)
        except ValueError: pass
        else: raise AssertionError("negative control accepted "+field)
    return dict(check(d),negative_controls=4)
if __name__=="__main__":
    import argparse
    a=argparse.ArgumentParser();a.add_argument("--self-test",action="store_true")
    args=a.parse_args()
    data=json.loads(PATH.read_text(encoding="utf-8"))
    print(json.dumps(self_test(data) if args.self_test else check(data),sort_keys=True))
