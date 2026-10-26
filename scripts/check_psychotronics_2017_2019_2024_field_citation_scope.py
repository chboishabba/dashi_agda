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
PATENT_PCT = "PCT/IN2018/050452"
PATENT_WIPO = "WO2019012556A1"
PATENT_SOURCE = "P1-80"

def inventor_name_core(name: str) -> str:
    """First and family name only to handle credited optional middle initial."""
    pieces = name.strip().casefold().replace(".", "").split()
    if len(pieces) < 2:
        raise ValueError("unparseable inventor or author name")
    return pieces[0] + " " + pieces[-1]

def exact_patent_identity(lookup: dict[str, dict[str, str]], direct: dict[str, dict[str, str]]) -> dict:
    """Original PCT exact identifier across WIPO and ACS author disclosure.

    This documents published device claims, NOT experimental or medical proof.
    Do not conflate inventor overlap with independent research cohort counts.
    """
    if PATENT_SOURCE not in lookup:
        raise ValueError("original WIPO patent source missing")
    patent = lookup[PATENT_SOURCE]
    paper = lookup["P1-40"]
    if PATENT_PCT not in (patent["original_work"] + " " + patent["carrier_and_inspection"]):
        raise ValueError("patent application mismatch")
    if PATENT_WIPO not in patent["original_work"] or PATENT_WIPO not in patent["locator"]:
        raise ValueError("WIPO patent publication identity mismatch")
    if PATENT_PCT not in (paper["carrier_and_inspection"] + " " + paper["claim_scope"]):
        raise ValueError("2019 original ACS COI failed exact patent ID join")
    if "17 cm" not in patent["claim_scope"] or "electrode" not in patent["claim_scope"].casefold():
        raise ValueError("original patent electrode geometry lost")
    if "Rodin" not in patent["not_established"] or "Helmholtz" not in patent["not_established"]:
        raise ValueError("patent-to-Rodin nonpromotion gate missing")
    # Exact first/family name matching only among *explicitly credited* humans.
    # The P1-80 semicolon-separated last member is the institutional assignee,
    # which must not accidentally be counted as a seventh human inventor.
    names = patent["authorial_root"].split(";")
    human = [n for n in names if "Indian Institute of Technology" not in n]
    if len(human) != 6:
        raise ValueError("unexpected inventor count")
    patent_people = {inventor_name_core(n) for n in human}
    if len(patent_people) != 6:
        raise ValueError("duplicate inventor identity")
    for original in ("P1-78", "P1-40"):
        authors = {inventor_name_core(n) for n in lookup[original]["authorial_root"].split(";")}
        if not patent_people <= authors:
            raise ValueError(f"original named research team mismatch {original}")
    for edge_id, source_id, target_id in (
        ("E125", "P1-80", "P1-40"),
        ("E126", "P1-80", "P1-37"),
        ("E127", "P1-80", "P1-78"),
    ):
        if edge_id not in direct:
            raise ValueError("missing exact original patent lineage edge")
        edge = direct[edge_id]
        if (edge["source_id"], edge["target_id"]) != (source_id, target_id):
            raise ValueError("mismatched original patent graph join")
    return {
        "original_patent_publication": PATENT_WIPO,
        "original_application": PATENT_PCT,
        "exact_original_article_COI_join": True,
        "six_original_inventor_names_match_2017_and_2019_papers": True,
        "patent_proposed_device": "17 cm aluminium electrode electric field",
        "patent_is_2024_Rodin_or_Helmholtz_coil": False,
        "medical_treatment_effect_proved": False,
        "2019_full_article_or_SI_inspected": False,
        "2024_claimed_60percent_match_coil_effect_proved": False,
    }



TAU_SOURCE = "P1-84"
TAU_DOI = "10.1039/C8RA09993F"

def tau_2019_source_distinction(lookup: dict[str, dict[str, str]],
                                direct: dict[str, dict[str, str]]) -> dict:
    """Exact original tau paper DOI/author/endpoint and directional links.

    RSC article and PMC9060620 are two carriers of ONE published study.
    No experiment in this consumer can be transmuted into a Rodin magnetic
    comparison, an Alzheimer's treatment result, or a second Saikia assay.
    """
    if TAU_SOURCE not in lookup:
        raise ValueError("missing original tau publication P1-84")
    article = lookup[TAU_SOURCE]
    if "2019" not in article["date_or_period"] or TAU_DOI.casefold() not in (
        article["original_work"] + " " + article["locator"]).casefold():
        raise ValueError("wrong original RSC tau DOI/date")
    if "VQIVYK" not in article["claim_scope"] or "VQIINK" not in article["claim_scope"]:
        raise ValueError("original tau peptide endpoints lost")
    if not all(z in article["claim_scope"] for z in ("150", "300", "ThT")):
        raise ValueError("original tau EF exposure/readout missing")
    if not all(z in article["not_established"] for z in ("Rodin", "Helmholtz")):
        raise ValueError("tau paper promoted to other instrument")
    authors = {inventor_name_core(n) for n in article["authorial_root"].split(";")}
    original_2017 = {inventor_name_core(n) for n in lookup["P1-78"]["authorial_root"].split(";")}
    original_acs = {inventor_name_core(n) for n in lookup["P1-40"]["authorial_root"].split(";")}
    if len(authors) != 5 or len(authors & original_2017) != 3 or len(authors & original_acs) != 4:
        raise ValueError("original RSC/2017/ACS named authors misjoined")
    for edge_id, target_id in (("E131", "P1-78"), ("E132", "P1-40"), ("E133", "P1-37")):
        edge = direct.get(edge_id)
        if edge is None or (edge["source_id"], edge["target_id"]) != (TAU_SOURCE, target_id):
            raise ValueError("original tau directed lineage edge misjoined")
    return {
        "original_tau_DOI": TAU_DOI,
        "separate_original_experiment": True,
        "same_original_2019_article_RSC_and_PMC_carrier": True,
        "credited_researchers_overlapping_2017": 3,
        "credited_researchers_overlapping_2019_ACS": 4,
        "human_clinical_efficacy_established": False,
        "Rodin_Helmholtz_60percent_comparison_established": False,
        "ACS_full_main_text_inspected": False,
    }

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
    patent = exact_patent_identity(lookup, direct)
    tau = tau_2019_source_distinction(lookup, direct)
    return {
        "separate_original_2019_RSC_tau_study": tau,
        "WIPO_original_patent_and_2019_ACS_disclosure": patent,
        "original_source_roles": sorted(PAPERS) + [PATENT_SOURCE, TAU_SOURCE],
        "shared_2017_2019_named_authors": sorted(same),
        "shared_author_count": len(same),
        "distinct_original_articles": 4,
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
    for kind in ("source_id", "year", "author_overlap", "edge_target", "missing",
                 "patent_number", "patent_disclosure", "patent_inventor",
                 "patent_hardware", "patent_edge", "missing_patent",
                 "tau_DOI", "tau_authors", "tau_coil_promotion", "tau_edge"):
        ss, ee = deepcopy(s), deepcopy(e)
        if kind == "source_id":
            next(r for r in ss if r["id"] == "P1-78")["id"] = "P1-40"
        elif kind == "year":
            next(r for r in ss if r["id"] == "P1-78")["date_or_period"] = "2008"
        elif kind == "author_overlap":
            next(r for r in ss if r["id"] == "P1-78")["authorial_root"] = "Other research team"
        elif kind == "edge_target":
            next(r for r in ee if r["edge"] == "E122")["target_id"] = "P1-40"
        elif kind == "missing":
            ss = [r for r in ss if r["id"] != "P1-78"]
        elif kind == "patent_number":
            next(r for r in ss if r["id"] == "P1-80")["original_work"] = "Unrelated patent"
        elif kind == "patent_disclosure":
            next(r for r in ss if r["id"] == "P1-40")["carrier_and_inspection"] = "abstract only; no original COI"
        elif kind == "patent_inventor":
            next(r for r in ss if r["id"] == "P1-80")["authorial_root"] = "Unrelated inventor"
        elif kind == "patent_hardware":
            next(r for r in ss if r["id"] == "P1-80")["claim_scope"] = "unrelated apparatus"
        elif kind == "patent_edge":
            next(r for r in ee if r["edge"] == "E125")["target_id"] = "P1-37"
        elif kind == "missing_patent":
            ss = [r for r in ss if r["id"] != "P1-80"]
        elif kind == "tau_DOI":
            next(r for r in ss if r["id"] == "P1-84")["original_work"] = "unrelated 2019 study"
            next(r for r in ss if r["id"] == "P1-84")["locator"] = "https://doi.org/10.0000/wrong"
        elif kind == "tau_authors":
            next(r for r in ss if r["id"] == "P1-84")["authorial_root"] = "Unrelated author"
        elif kind == "tau_coil_promotion":
            next(r for r in ss if r["id"] == "P1-84")["not_established"] = "Clinical Rodin benefit proven"
        else:
            next(r for r in ee if r["edge"] == "E133")["target_id"] = "P1-40"
        try:
            audit(ss, ee)
        except ValueError:
            cases += 1
        else:
            raise AssertionError(f"source provenance mutation not rejected: {kind}")
    assert cases == 15
    return {"source_adversarial_regressions_passed": cases,
            "patent_COI_and_original_claims_bounded": True,
            "2019_RSC_tau_remains_distinct_from_ACS_Amyloid_and_2024_Rodin": True,
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
