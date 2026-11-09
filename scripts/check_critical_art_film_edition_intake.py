#!/usr/bin/env python3
"""Fail-closed intake for original film/edition/scene claims.

Mechanical receipts only: content hashes and exact text passage can be
checked, but the code cannot certify reviewer independence, licensing,
semantic accuracy or actual audience psychology.  No original film
frames/quotes are shipped with this repository.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
MANIFEST=ROOT/"Docs/research/critical_art_film_edition_scene_intake_20261109.json"
EXPECTED={"leon_1994":1994,"dont_look_up_2021":2021,"planet_of_the_humans_2020":2020}
SHA=re.compile(r"^[0-9a-f]{64}$")
def require(ok,why):
    if not ok: raise ValueError(why)

def source_file(base,rel):
    require(isinstance(rel,str) and rel and not Path(rel).is_absolute(),"relative source path")
    file=(base/rel).resolve()
    require(file.is_relative_to(base.resolve()) and file.is_file(),"missing/escaping source file")
    return file

def check(data,base=ROOT):
    require(data.get("schema")=="dashi.critical_art.edition_scene_intake.v1","schema mismatch")
    works=data["works"]
    require(len(works)==len(EXPECTED),"three selected works")
    require({w["id"] for w in works}==set(EXPECTED),"identities")
    total_editions=total_claims=0
    for work in works:
        require(work["publication_year"]==EXPECTED[work["id"]],"publication year")
        require(bool(work["film_original_creators"].strip()),"missing film creators")
        editions=work["editions"]
        require(len({e["edition_id"] for e in editions})==len(editions),"duplicate editions")
        known={e["edition_id"]:e for e in editions}
        for ed in editions:
            require(ed["work_id"]==work["id"],"cross-work source")
            require(ed["edition_id"].strip() and ed["edition_label"].strip(),"edition provenance")
            require(ed["original_source_url"].startswith("https://"),"original locator")
            require(SHA.fullmatch(ed["sha256"]) is not None,"sha256 syntax")
            f=source_file(base,ed["relative_path"])
            raw=f.read_bytes()
            require(hashlib.sha256(raw).hexdigest()==ed["sha256"],"bytes differ")
            require(bool(ed.get("license_or_access_note","").strip()),"access note")
            # A file hash establishes local-byte integrity, not an authenticated
            # film edition. That remains a separate human review obligation.
            total_editions+=1
        ids=set()
        for claim in work["claims"]:
            require(claim["claim_id"] not in ids,"duplicate claim")
            ids.add(claim["claim_id"])
            ed=known.get(claim["edition_id"])
            require(ed is not None,"claim without edition")
            require(claim["channel"] in ("character_conduct","cinematic_form","spectator_testimony","critical_interpretation"),"channel")
            require(isinstance(claim["start_seconds"],int) and type(claim["start_seconds"]) is int,"start time")
            require(isinstance(claim["end_seconds"],int) and type(claim["end_seconds"]) is int,"end time")
            require(0<=claim["start_seconds"]<claim["end_seconds"],"invalid interval")
            require(claim["original_observation"].strip(),"empty observation")
            require(claim["source_evidence_locator"].strip(),"missing source locator")
            require(claim["original_claim_author"].strip(),"missing interpretation owner")
            require(claim["review_stage"] in ("candidate","reviewed_original"),"stage")
            if claim["review_stage"]=="reviewed_original":
                require(bool(claim.get("reviewer_id","").strip()),"reviewer identity required")
                require(bool(claim.get("review_receipt","").strip()),"reviewer receipt required")
                require(bool(claim.get("independent_second_review","").strip()),"independent review required")
                require(claim["reviewer_id"] != claim["independent_second_review"],"self-review only")
                # Independent receipt still requires separate human confirmation.
            require(claim.get("measured_audience_effect") is None,"audience effect asserted")
            require(claim.get("hostile_operation_identified") is None,"warfare effect asserted")
            total_claims+=1
    return {"registered_works":len(works),"verifiable_local_edition_files":total_editions,
            "scene_claims":total_claims,
            "independently_confirmed_film_observations":0,
            "real_world_audience_effects_verified":0}

def self_test():
    m=json.loads(MANIFEST.read_text(encoding="utf-8"))
    positive=check(m)
    import copy
    for modifier in ("duplicate","bad_year","unlocated_claim","bad_author"):
        d=copy.deepcopy(m)
        if modifier=="duplicate":d["works"].append(copy.deepcopy(d["works"][0]))
        if modifier=="bad_year":d["works"][0]["publication_year"]=1998
        if modifier=="bad_author":d["works"][1]["film_original_creators"]=""
        if modifier=="unlocated_claim":
            d["works"][0]["claims"]=[dict(claim_id="x",edition_id="fake",channel="cinematic_form",
              start_seconds=0,end_seconds=1,original_observation="sample",
              source_evidence_locator="none",original_claim_author="none",review_stage="candidate")]
        try:check(d)
        except (ValueError,KeyError):pass
        else:raise AssertionError("negative fixture admitted "+modifier)
    return dict(positive,negative_controls=4)

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--self-test",action="store_true")
    a=p.parse_args()
    result=self_test() if a.self_test else check(json.loads(MANIFEST.read_text(encoding="utf-8")))
    print(json.dumps(result,sort_keys=True,indent=2))
