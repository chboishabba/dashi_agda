#!/usr/bin/env python3
"""Static source/roadmap consistency check for the YM Clay PH0-PH4 max cut.

Use from the dashi_agda checkout. This is NOT an Agda typechecker, not a
physical theorem certificate, and does not contact GitHub or run CI.
"""
from __future__ import annotations
from pathlib import Path
import argparse
import json

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "Docs/physics"
MANIFEST = DOCS / "YMClayEndpointPhaseLemmaManifest20261108.json"
ROADMAP = DOCS / "YMClayRoadmapPhasesDeliverablesExactLemmas20261108.md"
REFERENCE = DOCS / "YMClayMinimalEndpointMaxCut20261107.md"
LEMMA_IDS = [f"YM{i:02d}" for i in range(1,11)]
PHASE_IDS = [f"PH{i}" for i in range(5)]
NONCLAY = {"signature31", "five_dimensional_KK", "monster"}

def validate():
    obj=json.loads(MANIFEST.read_text(encoding="utf8"))
    body=ROADMAP.read_text(encoding="utf8")
    old=REFERENCE.read_text(encoding="utf8")
    assert obj["as_of"]=="2026-11-08"
    assert obj["pr"]==1444
    assert obj["terminal_status"]!="completed"
    assert [x["id"] for x in obj["lemmas"]]==LEMMA_IDS
    assert [x["id"] for x in obj["phases"]]==PHASE_IDS
    assert set(obj["separate_non_clay_lanes"])==NONCLAY
    assert all(x["clay_prerequisite"] is False for x in obj["separate_non_clay_lanes"].values())
    ids=set(LEMMA_IDS)
    phase_coverage={p:[] for p in LEMMA_IDS}
    for phase in obj["phases"]:
        assert phase["acceptance"] and phase["deliverable"],phase["id"]
        for name in phase["lemmas"]:
            assert name in ids
            phase_coverage[name].append(phase["id"])
    assert all(v for v in phase_coverage.values()),phase_coverage
    targets=[]
    for lemma in obj["lemmas"]:
        assert lemma["status"] in ("open_physical_input","open_external_extension")
        assert lemma["target"] and lemma["missing"]
        targets.append(lemma["target"])
        for dep in lemma["depends"]:
            assert dep in ids and int(dep[2:])<int(lemma["id"][2:]), (lemma["id"],dep)
        assert lemma["source_owners"], lemma["id"]
        for owner in lemma["source_owners"]:
            p=ROOT / owner
            assert p.is_file(), f"unresolved exact source owner {owner} for {lemma['id']}"
        assert lemma["id"] in body,lemma["id"]
        assert f"`{lemma['target']}`" in body, lemma["target"]
    assert len(set(targets))==len(targets)
    for p in PHASE_IDS:
        assert p in body
    for term in ("R443","R445","R320","R333","3+1","196884","same","OS","interacting"):
        assert term in body,(term,"missing selected source caveat")
    expected_families = ("A3", "T1", "T5", "B1", "B2", "G1", "H6")
    latest = obj["reconciled_against_latest_source"]
    assert latest["critical_family_ids"] == list(expected_families)
    families = obj["latest_seven_family_cut"]
    assert [row["id"] for row in families] == list(expected_families)
    assert latest["critical_path_owner"].endswith("YangMillsClayCriticalPathRound572Exact.agda")
    for family in families:
        assert (ROOT / family["owner"]).is_file(), family["owner"]
        assert family["already_paid"] and family["original_remaining"]
        assert all(lemma_id in ids for lemma_id in family["maps_to"])
        assert family["id"] in body
    for lemma in obj["lemmas"]:
        assert lemma["already_paid"], f"forgot existing source for {lemma['id']}"
    assert "R569" in body and "R572" in body, "missing latest actual-group and critical path audit"
    assert "YMClayRoadmapPhasesDeliverablesExactLemmas20261108.md" in old, (
        "the preexisting main max-cut reference must point to new canonical roadmap"
    )
    print(f"PASS YM phase status: {len(obj['phases'])} phases, {len(obj['lemmas'])} open exact targets")
    print("PASS source owners exist, all dependencies ordered, all owners named, old max-cut references canon")
    print("PASS 3+1 / KK / Monster separated from standalone Clay prerequisites")
    print("SCOPE: documentation/static consistency only; NOT Agda acceptance or mass-gap result")

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--check",action="store_true",help="validate manuscript and exact-source ledger")
    parser.parse_args()
    validate()
