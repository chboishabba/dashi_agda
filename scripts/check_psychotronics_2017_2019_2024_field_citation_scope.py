#!/usr/bin/env python3
"""Case-specific 2017 -> 2019 -> 2024 citation-scope audit.

Original experimental ownership:
Pandey et al., Scientific Reports 7:2726 (2017);
Saikia et al., ACS Chemical Neuroscience 10:2250-2262 (2019);
Ramírez-Galindo et al., Revista Mexicana de Física 70:030901 (2024).
New source comparison: Johl Brown with OpenAI ChatGPT assistance.
No clinical/physics validation or 60-percent Rodin/Helmholtz result.
"""
from __future__ import annotations
import argparse
import csv
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LANDSCAPE = ROOT / "docs/research/psychotronics-phase1-literature-landscape-20261025.csv"
EDGES = ROOT / "docs/research/psychotronics-phase1-lineage-edges-20261025.csv"
PAPERS = {
    "P1-78": ("2017", "10.1038/s41598-017-02609-z"),
    "P1-40": ("2019", "10.1021/acschemneuro.8b00490"),
    "P1-37": ("2024", "10.31349/RevMexFis.70.030901"),
}
SHARED_AUTHOR_COUNT = 6

def rows(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))

def audit(sources: list[dict[str, str]], edges: list[dict[str, str]]) -> dict:
    seen = [r["id"] for r in sources]
    if len(seen) != len(set(seen)):
        raise ValueError("duplicate documentary source ID")
    if len([r["edge"] for r in edges]) != len(set(r["edge"] for r in edges)):
        raise ValueError("duplicate documentary edge ID")
    lookup = {r["id"]: r for r in sources}
    for key, (year, doi) in PAPERS.items():
        if key not in lookup:
            raise ValueError(f"missing original study {key}")
        r = lookup[key]
        if year not in r["date_or_period"]:
            raise ValueError(f"wrong original year {key}")
        if doi.lower() not in (r["original_work"] + " " + r["carrier_and_inspection"] + " " + r["locator"]).lower():
            raise ValueError(f"wrong original DOI {key}")
    if any(x["source_id"] not in lookup or x["target_id"] not in lookup for x in edges):
        raise ValueError("unresolved source endpoint")
    direct = {r["edge"]: r for r in edges}
    for edge_id, source_id, target_id in (
        ("E121", "P1-78", "P1-40"), ("E122", "P1-78", "P1-37")
    ):
        if edge_id not in direct:
            raise ValueError(f"missing exact source edge {edge_id}")
        r = direct[edge_id]
        if (r["source_id"], r["target_id"]) != (source_id, target_id):
            raise ValueError(f"misjoined source edge {edge_id}")
    # Credited human researchers, not independent sample units.
    def author_names(k: str) -> set[str]:
        return {x.strip().casefold().replace(".", "") for x in
                lookup[k]["authorial_root"].split(";") if x.strip()}
    a, b = author_names("P1-78"), author_names("P1-40")
    same = a & b
    if len(same) != SHARED_AUTHOR_COUNT:
        raise ValueError(f"unexpected credited author overlap: {sorted(same)}")
    if "0.6t" not in lookup["P1-78"]["claim_scope"].casefold():
        raise ValueError("lost original 2017 magnetic exposure")
    if "15" not in lookup["P1-40"]["claim_scope"]:
        raise ValueError("lost original 2019 EF endpoint")
    return {
        "original_source_roles": sorted(PAPERS),
        "shared_2017_2019_named_authors": sorted(same),
        "shared_author_count": len(same),
        "distinct_original_articles": 3,
        "2017_2019_independent_research_groups_proven": False,
        "2017_FF_experiment_is_2024_Rodin_coil": False,
        "2017_0_6T_is_2024_1_2mT": False,
        "2024_reference24_match_coil_60percent_proven": False,
        "2019_full_main_article_checked": False,
        "2017_original_full_HTML_checked": True,
        "author_conduct_or_clinical_effect_established": False,
        "study_overlap_is_not_repeated_biological_evidence": True,
    }

def self_test() -> dict:
    from copy import deepcopy
    s, e = rows(LANDSCAPE), rows(EDGES)
    audit(s, e)
    cases = 0
    for kind in ("source_id", "year", "author_overlap", "edge_target", "missing"):
        ss, ee = deepcopy(s), deepcopy(e)
        if kind == "source_id":
            next(r for r in ss if r["id"] == "P1-78")["id"] = "P1-40"
        elif kind == "year":
            next(r for r in ss if r["id"] == "P1-78")["date_or_period"] = "2008"
        elif kind == "author_overlap":
            next(r for r in ss if r["id"] == "P1-78")["authorial_root"] = "Other research team"
        elif kind == "edge_target":
            next(r for r in ee if r["edge"] == "E122")["target_id"] = "P1-40"
        else:
            ss = [r for r in ss if r["id"] != "P1-78"]
        try:
            audit(ss, ee)
        except ValueError:
            cases += 1
        else:
            raise AssertionError(f"source provenance mutation not rejected: {kind}")
    assert cases == 5
    return {"source_adversarial_regressions_passed": cases,
            "no_Rodin_60percent_promotion": True,
            "original_2019_main_text_still_unpaid": True}

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--self-test", action="store_true")
    args = p.parse_args()
    outcome = audit(rows(LANDSCAPE), rows(EDGES))
    if args.self_test:
        outcome["self_test"] = self_test()
    print(json.dumps(outcome, sort_keys=True, indent=2))

if __name__ == "__main__":
    main()
