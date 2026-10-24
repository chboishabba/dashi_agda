#!/usr/bin/env python3
"""Ibrahim / snowball provenance regression for a CASE-SPECIFIC research ledger.

The generic theory and author/source identities belong to existing
DASHI.Wikimedia.IbrahimSnowballInvestigativeClaimSourceLineageBidiExact.
This code audits declared graph consistency, not external events or labs.
Never upgrade uninspected citations, repeated speakers or reported numbers
to independent witness, experimental replication or mechanism.
"""
from __future__ import annotations
from collections import Counter
import argparse
import json
from pathlib import Path

DEFAULT = (Path(__file__).resolve().parents[1] / "docs" / "research"
           / "hardt-ibrahim-crosslineage-caseledger-20261025.json")

PROHIBITED = {
    frozenset(("H_ALPHA_80", "H_ASSASSINATION")),
    frozenset(("H_PHASE_TORUS", "H_ASSASSINATION")),
    frozenset(("C_GENTRY", "H_ASSASSINATION")),
    frozenset(("R_FIELD_TABLE", "H_ASSASSINATION")),
    frozenset(("WBS99", "C_GENTRY")),
    frozenset(("NOBEL26", "H_ASSASSINATION")),
}

def _unique(rows, key, name):
    ids=[x[key] for x in rows]
    if len(ids)!=len(set(ids)):
        raise ValueError("duplicate "+name+" identity")
    return {x[key]: x for x in rows}

def audit(data):
    """Validate documentary SOURCE roles; never infer physical truth."""
    if data.get("schema") != "dashi.hardt_ibrahim_case_source_genealogy.v1":
        raise ValueError("unknown versioned case ledger")
    claims=_unique(data["claims"],"id","claim")
    sources=_unique(data["sources"],"id","source carrier")
    if len(data["claims"])<6 or len(data["sources"])<13:
        raise ValueError("source/claim coverage below audited inventory")
    for s in sources.values():
        if not s["author_root"] or not s["original_author"] or not s["inspection"]:
            raise ValueError("lost creator or acquisition provenance")
        if not s.get("limits"):
            raise ValueError("unbounded original source promotion")
        if any(c not in claims for c in s["claims"]):
            raise ValueError("unknown claim edge from original source")
    for e in data["edges"]:
        if e["from"] not in sources or e["to"] not in sources:
            raise ValueError("lineage endpoint does not exist")
        if e["claim"] not in claims:
            raise ValueError("unknown claim edge")
        if not e.get("state") or not e.get("relation"):
            raise ValueError("unattributed dependency edge")
    if not all(x.get("first_unpaid") and x.get("proof_status")
               for x in claims.values()):
        raise ValueError("claim missing first original-document payment")
    forbidden={frozenset((x["lhs"],x["rhs"]))
               for x in data["explicit_nonjoins"]}
    if not PROHIBITED.issubset(forbidden):
        raise ValueError("missing hard negative claim/source join")

    article=sources["H17_JOURNAL"]
    blog=sources["H17_BLOG"]
    manuscript=sources["H_MANUSCRIPT"]
    if (article["date"]!="2017-08-24"
        or "opinion" not in article["type"]
        or not article["inspection"].startswith("original_pdf")
        or article["author_root"]!=blog["author_root"]):
        raise ValueError("original 2017 Opinion cannot become independent replication")
    if ("bibliography_reference_only" not in manuscript["inspection"]
        or manuscript["type"]!="identified_not_acquired"
        or "How High Delta people can influence" not in manuscript["carrier"]):
        raise ValueError("uninspected Hardt manuscript was falsely promoted")

    a80=[s for s in sources.values() if "H_ALPHA_80" in s["claims"]]
    events=[s for s in sources.values() if "H_ASSASSINATION" in s["claims"]]
    if len(a80)<2 or any("H_ASSASSINATION" in s["claims"] for s in a80):
        raise ValueError("alpha-occipital 80 percent conflated with alleged outcomes")
    if len(events)<2 or {s["author_root"] for s in events}!={"James V. Hardt"}:
        raise ValueError("independent historical witness inferred from repeated Hardt speaker")
    if any(s.get("independent_event_witness") is True for s in events):
        raise ValueError("no independently authenticated event witness in inspected documents")

    croft=[s for s in sources.values() if "C_GENTRY" in s["claims"]
           and s["id"]!="C_GENTRY_ORIGINAL"]
    if {s["author_root"] for s in croft}!={"Don Croft"}:
        raise ValueError("Gentry/Flanagan testimonial carrier counted as new witness")
    if sources["C_GENTRY_ORIGINAL"]["inspection"]!="not_located":
        raise ValueError("original Gentry instructions not acquired")
    if sources["WBS99"]["author_root"]=="Gentry Smith":
        raise ValueError("Wilbert Brockhouse Smith mistakenly joined to Gentry")

    field_claim={"R13","R24"}
    if not field_claim.issubset(sources):
        raise ValueError("either original field paper is missing")
    if not all("R_FIELD_TABLE" in sources[s]["claims"] for s in field_claim):
        raise ValueError("field table comparison loses primary-source author")
    pairs=data["concordance"]
    if len(pairs)!=3 or len({row["current_a"] for row in pairs})!=3:
        raise ValueError("expected three distinct published current settings")
    for row in pairs:
        if row["b2013_mt"]!=row["b2024_mt"]:
            raise ValueError("reported numerical concordance lost")
        if row.get("raw_trace_same_proved") is not False:
            raise ValueError("same reported numbers are not a raw-data join")
    if any(s.get("independent_event_witness") for s in (sources["R13"],sources["R24"])):
        raise ValueError("published ordinary coil instrument is not Hardt event witness")

    # Named documentary source carriers vs alleged-event eyewitnesses remain
    # distinct denominators. A new REPRINT by Hardt may increase carriers
    # but cannot increase original first-person authors or verified trials.
    return {
      "status":"DOCUMENTARY_CASE_LEDGER_CONSISTENT_NOT_PHYSICS_VERIFIED",
      "claims":len(claims),"source_carriers":len(sources),
      "lineage_edges":len(data["edges"]),"forbidden_crossjoins":len(forbidden),
      "hardt_allegation_carriers":len(events),
      "hardt_allegation_speaker_roots":len({s["author_root"] for s in events}),
      "independent_event_witness_records_present":0,
      "measured_remote_target_attempts_present":0,
      "crofts_first_person_witness_roots":len({s["author_root"] for s in croft}),
      "original_gentry_instruction_acquired":False,
      "published_field_pair_matches":len(pairs),
      "field_raw_trace_independence":"UNRESOLVED",
      "hardt_2017_publication_type":"Opinion",
      "unpublished_hardt_reference_10_body_acquired":False,
      "missing_original_source_payment":claims["H_GENERAL"]["first_unpaid"],
      "truth_proved_by_original_source_role":False,
      "new_quantum_or_maxwell_field_observed":False,
      "historical_crime_corroborated":False,
    }

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--ledger",type=Path,default=DEFAULT)
    args=p.parse_args()
    result=audit(json.loads(args.ledger.read_text(encoding="utf-8")))
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=="__main__":
    main()
