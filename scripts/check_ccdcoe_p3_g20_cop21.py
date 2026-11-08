#!/usr/bin/env python3
"""DASHI G20-COP21 source-scoped comparison, never actor/causal fusion.

This is a *bounded original-document clause-ledger* audit, not automatic
political persuasion detection. Without externally supplied ORIGINAL
document byte files, verified extract profiles and reviewed passage text,
the tool checks only SOURCE-PUBLISHED editorial clause anchors.

Usage:
  python scripts/check_ccdcoe_p3_g20_cop21.py --self-test
  python scripts/check_ccdcoe_p3_g20_cop21.py
  python scripts/check_ccdcoe_p3_g20_cop21.py --source-map verified.json
The source-map is an object mapping document id to:
  {"raw_file":"relative original.html", "raw_sha256":"64 hex...",
   "extracted_file":"relative extracted.txt", "extractor_receipt":"...",
   "human_review_receipt":"..."}.
Original and extracted files must exist under --source-root. For
PDFs, extracted_file must be supplied separately with explicit profile;
the tool does not pretend reading copied PDF bytes is textual review.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
MANIFEST=ROOT/"Docs/research/ccdcoe_p3_g20_cop21_attribution_manifest.json"
EXPECTED_DOC_IDS={
 "brisbane2014","antalya2015","parisDecision2015","parisArticle4",
 "hamburgUS2017","hamburgOtherLeaders2017","c20Turkey2015",
 "b20Turkey2015","gccHarrison"
}
SPEAKER_MAP={
 "brisbane2014":"G20 leaders",
 "antalya2015":"G20 leaders",
 "parisDecision2015":"UNFCCC COP21 Parties",
 "parisArticle4":"Paris Agreement Parties",
 "hamburgUS2017":"United States position recorded by G20 leaders",
 "hamburgOtherLeaders2017":"Other G20 leaders excluding the US",
 "c20Turkey2015":"Civil 20 Turkey participant organisations",
 "b20Turkey2015":"Business 20 Turkey taskforces",
 "gccHarrison":"E. Bruce Harrison Company"
}
SAFE_SPEECH_ACTS={
 "leaders_adopted","treaty_adoption_decision","treaty_legal_obligation",
 "explicit_dissent","leaders_adopted_excluding_US",
 "civil_society_recommendation","business_recommendation","agency_self_report"
}

def assert_present_or_stop(check: bool, message: str) -> None:
    if not check:
        raise ValueError(message)

def validate(m: dict) -> dict:
    assert_present_or_stop(
        m.get("schema")=="dashi.ccdcoe.p3.g20_cop21_attribution.v1",
        "Unexpected schema")
    docs=m["documents"]; by_id={r["id"]:r for r in docs}
    assert_present_or_stop(len(docs)==len(EXPECTED_DOC_IDS) and
                           set(by_id)==EXPECTED_DOC_IDS,"Source set mismatch")
    for k,r in by_id.items():
        assert_present_or_stop(r["author"]==SPEAKER_MAP[k], "Author mismatch: "+k)
        assert_present_or_stop(r["speech_act"] in SAFE_SPEECH_ACTS,
                               "Unexpected speech act: "+k)
        assert_present_or_stop(r["url"].startswith("https://"),
                               "Original source URI missing")
        assert_present_or_stop(r["raw_sha256"] is None and
                               r["review_receipt"] is None,
                               "Do not promote unreviewed original bytes in manifest")
        assert_present_or_stop(r["source_endorses_DASHI"] is False and
                               r["independent_actor_policy_transmission"] is None,
                               "Source cannot be promoted to consent/causality")
        if not r["date_exact"]:
            assert_present_or_stop(r["event_date"] is None,
                                   "Invented exact date: "+k)
    claims=m["bounded_claims"]
    assert_present_or_stop(len(claims)==10, "Ten intentionally bounded rows required")
    assert_present_or_stop(len({r["id"] for r in claims})==10,
                           "Claim IDs must be unique")
    for claim in claims:
        r=by_id[claim["source"]]
        assert_present_or_stop(claim["speaker"]==r["author"] and
                               claim["source_type"]==r["speech_act"],
                               "Speaker-to-claim mismatch: "+claim["id"])
        if claim["source"]=="b20Turkey2015":
            assert_present_or_stop(claim["anchor"] is None and
                                   claim["action"]=="source_index_only",
                                   "B20 document was not reviewed")
        else:
            assert_present_or_stop(isinstance(claim["anchor"],str) and
                                   len(claim["anchor"])>=12,
                                   "Original clause anchor missing")
        assert_present_or_stop(
            claim["action"]!="independently_measured_influence",
            "Causal influence not observed")
    assert_present_or_stop(
        next(r for r in claims if r["id"]=="hamburg_us")["speaker"] !=
        next(r for r in claims if r["id"]=="hamburg_other")["speaker"],
        "US and other leaders have different statement scope")
    assert_present_or_stop(
        by_id["parisArticle4"]["speech_act"]=="treaty_legal_obligation" and
        by_id["c20Turkey2015"]["speech_act"]=="civil_society_recommendation",
        "A stakeholder request is not a treaty provision")
    timing=m["legal_temporal_scope"]
    assert_present_or_stop(
        timing["paris_adoption"]=="2015-12-12" and
        timing["paris_treaty_entry_into_force"]=="2016-11-04",
        "Paris adoption must not be confused with legal entry into force")
    assert_present_or_stop(
        timing["hamburg_2017_us_statement"].startswith("2017-07-08 announcement"),
        "Hamburg US announcement is not completed 2017 treaty exit")
    assert_present_or_stop(
        timing["no_assumption_of_country_specific_legal_or_emissions_compliance"],
        "Legal agreement is not country emissions compliance")
    guards=m["admission_guards"]
    assert_present_or_stop(all(v is True for k,v in guards.items()
                               if k not in ("same_object_actor_to_negotiator_or_decision_trail",
                                            "financial_or_lobbying_direct_receipt",
                                            "emissions_impact")),"Attribution safeguards missing")
    assert_present_or_stop(all(guards[k] is None for k in (
        "same_object_actor_to_negotiator_or_decision_trail",
        "financial_or_lobbying_direct_receipt","emissions_impact")),
        "Unsupported cross-institution influence")
    assert_present_or_stop(guards["paris_adoption_date_is_not_entry_into_force"] and
                           guards["us_announced_withdrawal_is_not_2017_effective_treaty_withdrawal"],
                           "Treaty temporality collapsed")
    assert_present_or_stop(m["status"]["summit_causal_influence_identified"] is False,
                           "Do not infer campaign influence from shared language")
    counts=Counter(r["source"] for r in claims)
    return {"schema":"dashi.ccdcoe.p3.institutional_bounded_comparison.v1",
            "distinct_source_objects":len(docs),"selected_clause_rows":len(claims),
            "claim_counts_by_original_author_source":dict(sorted(counts.items())),
            "us_position_and_other_leaders_remain_distinct":True,
            "stakeholder_recommendations_are_not_adoptions":True,
            "demonstrated_GCC_to_G20_actor_transmission":False,
            "causal_influence_estimate":None,
            "original_bytes_verified":False,
            "interpretation":"Selected source-specific documentary clauses, not random or complete sampling"}

def verify_archive(m: dict, rows: dict, source_root: Path) -> dict:
    root=source_root.resolve(strict=True)
    assert_present_or_stop(root.is_dir(),"Source root must be existing directory")
    known={r["id"]:r for r in m["documents"]}
    assert_present_or_stop(set(rows)<=set(known),"Unknown source file identity")
    results={}
    for sid,source in rows.items():
        expected={"raw_file","raw_sha256","extracted_file",
                  "extractor_receipt","human_review_receipt"}
        assert_present_or_stop(set(source)==expected,"Missing/extra receipt fields")
        assert_present_or_stop(
            all(source.get(k) for k in expected),"Empty reviewer/source receipt")
        def located(name: str) -> Path:
            rel=Path(source[name])
            assert_present_or_stop(
                not rel.is_absolute() and ".." not in rel.parts,"Unsafe relative path")
            p=root/rel
            assert_present_or_stop(not p.is_symlink(),"Source symlink rejected")
            p=p.resolve(strict=True)
            assert_present_or_stop(
                p.is_relative_to(root) and p.is_file(),"Source outside archive")
            return p
        raw=located("raw_file").read_bytes()
        digest=hashlib.sha256(raw).hexdigest()
        assert_present_or_stop(digest==source["raw_sha256"],"Original bytes mismatch")
        text=located("extracted_file").read_text(encoding="utf-8")
        expected_anchors=[row["anchor"] for row in m["bounded_claims"]
                          if row["source"]==sid and row["anchor"] is not None]
        text=" ".join(text.split()).casefold()
        for anchor in expected_anchors:
            assert_present_or_stop(" ".join(anchor.split()).casefold() in text,
                                   "Source-specific clause absent: "+sid+" "+anchor)
        results[sid]={"raw_sha256":digest,"verified_anchors":len(expected_anchors),
                      "extractor_receipt":source["extractor_receipt"],
                      "human_review_receipt":source["human_review_receipt"],
                      "status":"candidate_passage_text_source-byte-matched_not_semantic_PNF_admitted"}
    return results

def self_test() -> None:
    import tempfile
    m=json.loads(MANIFEST.read_text(encoding="utf-8"))
    out=validate(m)
    assert out["selected_clause_rows"]==10
    changed=json.loads(json.dumps(m))
    next(x for x in changed["bounded_claims"] if x["id"]=="hamburg_other")[
        "speaker"]=SPEAKER_MAP["hamburgUS2017"]
    try: validate(changed)
    except ValueError: pass
    else: raise AssertionError("Wrong Hamburg statement owner admitted")
    changed=json.loads(json.dumps(m))
    next(x for x in changed["bounded_claims"] if x["id"]=="b20_index")[
        "action"]="adopted_communicated_position"
    try: validate(changed)
    except ValueError: pass
    else: raise AssertionError("B20 index promoted to adopted decision")
    with tempfile.TemporaryDirectory() as d:
        root=Path(d)
        (root/"original.html").write_bytes(b"<html>original source bytes</html>")
        (root/"text.txt").write_text(
            "Our actions will support sustainable development, economic growth, and certainty for business and investment. "
            "at the 21st Conference of the Parties (COP21) in Paris in 2015",encoding="utf-8")
        receipt={"raw_file":"original.html",
                 "raw_sha256":hashlib.sha256(
                     (root/"original.html").read_bytes()).hexdigest(),
                 "extracted_file":"text.txt",
                 "extractor_receipt":"LOCAL-TEST-extractor",
                 "human_review_receipt":"LOCAL-TEST-human"}
        assert verify_archive(m,{"brisbane2014":receipt},root)[
            "brisbane2014"]["verified_anchors"]==2
        bad=dict(receipt,raw_sha256="0"*64)
        try: verify_archive(m,{"brisbane2014":bad},root)
        except ValueError: pass
        else: raise AssertionError("Tampered primary source accepted")
    print("PASS: documentary attribution, Hamburg opposition, B20 nonpromotion, hash/passage and negative fixtures")

def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--self-test",action="store_true")
    p.add_argument("--source-map",type=Path)
    p.add_argument("--source-root",type=Path)
    p.add_argument("--output",type=Path)
    a=p.parse_args()
    if a.self_test:
        self_test();return
    m=json.loads(MANIFEST.read_text(encoding="utf-8"))
    result=validate(m)
    if a.source_map is not None:
        if a.source_root is None:
            p.error("--source-root required with --source-map")
        rows=json.loads(a.source_map.read_text(encoding="utf-8"))
        result["archive_source_receipts"]=verify_archive(m,rows,a.source_root)
        result["original_bytes_verified"]=len(rows)>0
    if a.output:
        a.output.parent.mkdir(parents=True,exist_ok=True)
        a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n",
                            encoding="utf-8")
    print(json.dumps(result,sort_keys=True))

if __name__=="__main__":
    main()
