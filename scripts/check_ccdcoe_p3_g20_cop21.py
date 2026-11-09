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
 "b20Turkey2015","gccHarrison","g20EnergyMinisters2015","b20EnergyForum2015"
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
 "gccHarrison":"E. Bruce Harrison Company",
 "g20EnergyMinisters2015":"G20 Energy Ministers",
 "b20EnergyForum2015":"B20 Energy Forum participants and G20-B20 interaction participants"
}
SAFE_SPEECH_ACTS={
 "leaders_adopted","treaty_adoption_decision","treaty_legal_obligation",
 "explicit_dissent","leaders_adopted_excluding_US",
 "civil_society_recommendation","business_recommendation","agency_self_report",
 "ministerial_communique","business_forum_recommendation"
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
    assert_present_or_stop(len(claims)==15, "15 intentionally bounded rows required")
    assert_present_or_stop(len({r["id"] for r in claims})==len(claims),
                           "Every claim row must have a unique ID")
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
    chronology=m["ordered_source_events"]
    assert_present_or_stop(
        [e["date"] for e in chronology]==[
            "2015-10-02","2015-10-12","2015-11-16","2015-12-12"] and
        [e["source"] for e in chronology]==[
            "g20EnergyMinisters2015","b20EnergyForum2015",
            "antalya2015","parisDecision2015"],
        "Ministerial to business to leaders to COP ordering lost")
    stakeholders=m["b20_event_attribution"]
    assert_present_or_stop(
        stakeholders["document_id"]=="b20EnergyForum2015" and
        stakeholders["original_date"]=="2015-10-12",
        "Source-dated B20 original statement identity wrong")
    for guard in (
        "event_participation_does_not_prove_individual_clause_authorship",
        "source_input_does_not_mean_institutional_endorsement_of_all_recommendations",
        "business_participants_are_not_summit_leaders",
        "october_12_submission_cannot_cause_october_2_ministerial_text"):
        assert_present_or_stop(stakeholders[guard] is True,
                               "B20 participants / chronology must not be fused")
    assert_present_or_stop(
        stakeholders["historically_confirmed_same_actor_to_November_G20_drafting"] is None and
        stakeholders["speaker_specific_quotation_origin_identified"] is None,
        "Original B20 speaker author and G20 drafting trail unproven")
    assert_present_or_stop(
        {r["id"] for r in claims if r["source"]=="b20EnergyForum2015"} == {
            "b20_carbon_pricing","b20_participation","b20_subsidies"} and
        {r["id"] for r in claims if r["source"]=="g20EnergyMinisters2015"} == {
            "ministers_clean","ministers_cop21"},
        "Original October 2015 document-level claim identity lost")
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
    studies=m["independent_compliance_studies"]
    assert_present_or_stop(len(studies)==2,
                           "Two distinct original compliance research owners required")
    first,second=studies
    assert_present_or_stop(
        first["id"]=="brisbane2014_final_G20RG" and
        second["id"]=="antalya2015_final_G20RG",
        "Research author/period assignment incorrect")
    assert_present_or_stop(
        (first["selected_monitored_commitments"],
         first["total_summit_commitments"])==(17,205) and
        (second["selected_monitored_commitments"],
         second["total_summit_commitments"])==(17,113),
        "Sampling frame/commitment denominator confusion")
    a={r["topic"]:r for r in first["scores"]}
    b={r["topic"]:r for r in second["scores"]}
    assert_present_or_stop(
        {k:(v["reported_score_hundredths"],v["reported_percent"]) for k,v in a.items()}=={
        "climate_change":(10,55),
        "clean_energy_technology":(90,95),
        "fossil_fuel_subsidies":(-45,28)} and
        {k:(v["reported_score_hundredths"],v["reported_percent"]) for k,v in b.items()}=={
        "fossil_fuel_subsidies":(-35,33)},
        "Original published topic-specific compliance summary mismatch")
    for study in studies:
        assert_present_or_stop(study["source_url"].startswith("https://g20.utoronto.ca/") or
                               study["source_url"].startswith("https://www.g20.utoronto.ca/"),
                               "Missing original research-report source")
        assert_present_or_stop(
            study["original_evaluators_endorse_DASHI"] is False and
            study["independently_proven_emissions_effect"] is None and
            study["full_original_member_level_reanalysis"] is False,
            "Research scoring cannot be promoted into endorsement or physical effect")
    assert_present_or_stop(
        second["evaluation_start"]>first["evaluation_start"] and
        second["evaluation_end"]>first["evaluation_end"],
        "Longitudinal evaluation periods lost")
    comp=m["compliance_scope_guard"]
    assert_present_or_stop(
        all(v is True for k,v in comp.items() if k not in (
            "emissions_change_inferred","original_author_endorsement_inferred")) and
        comp["emissions_change_inferred"] is None and
        comp["original_author_endorsement_inferred"] is False,
        "Original G20 Research Group measurement scope and authorship lost")
    assert_present_or_stop(
        m["status"]["published_selected_commitment_compliance_observations_located"],
        "Published actual implementation measurement omitted")
    counts=Counter(r["source"] for r in claims)
    return {"schema":"dashi.ccdcoe.p3.institutional_bounded_comparison.v1",
            "distinct_source_objects":len(docs),"selected_clause_rows":len(claims),
            "independent_scored_commitment_reports":len(studies),
            "brisbane_climate_percent":a["climate_change"]["reported_percent"],
            "brisbane_clean_energy_percent":a["clean_energy_technology"]["reported_percent"],
            "brisbane_fossil_percent":a["fossil_fuel_subsidies"]["reported_percent"],
            "antalya_fossil_percent":b["fossil_fuel_subsidies"]["reported_percent"],
            "fossil_percent_difference_descriptive_only":b["fossil_fuel_subsidies"]["reported_percent"] - a["fossil_fuel_subsidies"]["reported_percent"],
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
    assert out["selected_clause_rows"]==15
    changed=json.loads(json.dumps(m))
    next(x for x in changed["bounded_claims"] if x["id"]=="hamburg_other")[
        "speaker"]=SPEAKER_MAP["hamburgUS2017"]
    try: validate(changed)
    except ValueError: pass
    else: raise AssertionError("Wrong Hamburg statement owner admitted")
    changed=json.loads(json.dumps(m))
    changed["b20_event_attribution"]["october_12_submission_cannot_cause_october_2_ministerial_text"]=False
    try: validate(changed)
    except ValueError: pass
    else: raise AssertionError("Later B20 report promoted into earlier ministers text")
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
