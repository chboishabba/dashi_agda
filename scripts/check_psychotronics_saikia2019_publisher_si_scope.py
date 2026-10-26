#!/usr/bin/env python3
"""Original 2019 ACS supplementary-information (SI) RECEIPT audit.

Author-original: Saikia et al. 2019, DOI 10.1021/acschemneuro.8b00490,
American Chemical Society. Downstream original: Ramirez-Galindo et al.
2024 DOI 10.31349/RevMexFis.70.030901, Discussion and reference [24].
Source-scope audit: Johl Brown with OpenAI ChatGPT assistance.

This tests the original publisher's public *SI-description metadata*,
NOT the content of the inaccessible SI PDF and NOT any biological effect.
Never promote a subject listing to an independently measured comparison.
"""
from __future__ import annotations
import argparse
import copy
import csv
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RECEIPT = ROOT / "docs/receipts/PsychotronicsSaikia2019ACSSIOriginalPublisherListing20261027.json"
SOURCES = ROOT / "docs/research/psychotronics-phase1-literature-landscape-20261025.csv"
EDGES = ROOT / "docs/research/psychotronics-phase1-lineage-edges-20261025.csv"
ORIGINAL_DOI = "10.1021/acschemneuro.8b00490"

def read_rows(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream))

def audit(receipt: dict, sources: list[dict[str, str]], edges: list[dict[str, str]]) -> dict:
    roots = {r["id"]: r for r in sources}
    directed = {r["edge"]: r for r in edges}
    if len(roots) != len(sources) or len(directed) != len(edges):
        raise ValueError("duplicated canonical source or relationship")
    for r in edges:
        if r["source_id"] not in roots or r["target_id"] not in roots:
            raise ValueError("dangling original-source genealogy edge")
    if receipt.get("receipt_type") != "publisher_supplementary_information_listing_not_pdf":
        raise ValueError("unsupported original SI source state")
    owner = receipt["attribution"]
    if owner["source_id"] != "P1-40" or owner["doi"] != ORIGINAL_DOI:
        raise ValueError("wrong original SI source owner/DOI")
    if ORIGINAL_DOI not in roots["P1-40"]["original_work"] + roots["P1-40"]["carrier_and_inspection"]:
        raise ValueError("2019 ACS original DOI not in canonical source")
    if "SI *topic listing*" not in roots["P1-40"]["carrier_and_inspection"] and (
        "SI PDF body/bytes NOT acquired" not in roots["P1-40"]["carrier_and_inspection"]
    ):
        raise ValueError("source ledger has lost SI-listing-versus-PDF distinction")
    source = receipt["source"]
    if not source["publisher_says_supporting_information_free"]:
        raise ValueError("not original free SI listing")
    if not source["publisher_metadata_only"]:
        raise ValueError("publisher metadata promoted into SI original pages")
    for label in ("actual_si_pdf_bytes_acquired", "direct_si_body_figures_inspected",
                  "full_acs_2019_main_article_acquired"):
        if source[label]:
            raise ValueError(f"cannot assert {label} on listing-only receipt")
    if source["actual_si_pdf_download_url"] is not None or source["actual_si_pdf_sha256"] is not None:
        raise ValueError("fabricated unverified source PDF locator or digest")
    if not source["subject_list"]["MF_effect_on_secondary_aggregations"]:
        raise ValueError("lost relevant original magnetic-field topic")
    if "effect of MF on secondary aggregations" not in source["relevant_original_metadata_description"]:
        raise ValueError("original ACS SI topic wording not present")
    consumer = receipt["citation_consumer"]
    if consumer["original_consumer_reference_number"] != 24:
        raise ValueError("wrong 2024 reference number")
    if consumer["original_consumer_cites_doi"] != ORIGINAL_DOI:
        raise ValueError("2024 citation DOI has been reassigned")
    if directed.get("E59", {}).get("source_id") != "P1-37" or directed["E59"]["target_id"] != "P1-40":
        raise ValueError("wrong original 2024 ref24 directed join")
    if not all(consumer[label] for label in
               ("effect_60_percent_attributed_to_2019_original",
                "SI_metadata_mentions_magnetic_field_topic")):
        raise ValueError("omitted original 2024 citation or publisher SI subject")
    for label in ("SI_metadata_explicitly_names_Rodin_Helmholtz_comparison",
                  "SI_metadata_explicitly_reports_60_percent",
                  "unsupported_inference_that_full_SI_lacks_matching_coils",
                  "inferred_safety_or_clinical_effect", "inferred_author_intent_or_misconduct"):
        if consumer[label]:
            raise ValueError(f"SI description improperly promoted: {label}")
    if any(consumer[label] != "UNRESOLVED_NOT_READ" for label in (
        "matched_Rodin_Helmholtz_apparatus_in_original_SI_body",
        "effect_60_percent_figure_and_denominator_in_original_SI_body")):
        raise ValueError("unread SI body promoted to positive or negative result")
    if not receipt["no_second_independent_experiment_from_SI"]:
        raise ValueError("same study reissued as independent result")
    return {
        "original_article_DOI": ORIGINAL_DOI,
        "same_original_article_source_id": "P1-40",
        "original_downstream_edge": "E59",
        "original_ACS_SI_metadata_topic_MF_secondary_aggregations": True,
        "full_SI_PDF_original_bytes_verified": False,
        "full_ACS_main_text_verified": False,
        "named_magnetic_coil_comparison_source_validated": False,
        "whether_unread_SI_contains_matching_coils": "UNRESOLVED_NOT_READ",
        "statistic_60percent_comparator_confirmed": False,
        "SI_is_an_independent_experiment": False,
        "clinical_efficacy_or_author_misconduct_inferred": False
    }

def self_test(receipt: dict, sources: list[dict[str, str]], edges: list[dict[str, str]]) -> dict:
    audit(receipt, sources, edges)
    cases = (
        ("SI_claimed_read", "source", "direct_si_body_figures_inspected", True),
        ("fake_sha", "source", "actual_si_pdf_sha256", "fake"),
        ("invented_url", "source", "actual_si_pdf_download_url", "https://example.invalid/SI.pdf"),
        ("MF_topic_removed", "source_subject", "MF_effect_on_secondary_aggregations", False),
        ("wrong_doi", "attribution", "doi", "10.1021/wrong"),
        ("no_uncertainty", "citation_consumer", "matched_Rodin_Helmholtz_apparatus_in_original_SI_body", False),
        ("claimed_60pct", "citation_consumer", "SI_metadata_explicitly_reports_60_percent", True),
        ("claim_abstract_absence", "citation_consumer", "unsupported_inference_that_full_SI_lacks_matching_coils", True),
        ("claim_misconduct", "citation_consumer", "inferred_author_intent_or_misconduct", True),
        ("repeated_study", "root", "no_second_independent_experiment_from_SI", False),
    )
    rejected = 0
    for name, section, field, value in cases:
        r = copy.deepcopy(receipt)
        if section == "source_subject":
            r["source"]["subject_list"][field] = value
        elif section == "root":
            r[field] = value
        else:
            r[section][field] = value
        try:
            audit(r, sources, edges)
        except ValueError:
            rejected += 1
        else:
            raise AssertionError(f"provenance error {name} was not rejected")
    # Separate lineage tamper attack: valid SI metadata under wrong target.
    wrong_edges = copy.deepcopy(edges)
    next(row for row in wrong_edges if row["edge"] == "E59")["target_id"] = "P1-84"
    try:
        audit(receipt, sources, wrong_edges)
    except ValueError:
        rejected += 1
    else:
        raise AssertionError("original ref24 source reassignment not rejected")
    assert rejected == 11
    return {"adversarial_cases_rejected": rejected,
            "publisher_metadata_cannot_prove_unread_full_SI_contents": True}

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--self-test", action="store_true")
    args = p.parse_args()
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    sources, edges = read_rows(SOURCES), read_rows(EDGES)
    result = audit(receipt, sources, edges)
    if args.self_test:
        result["self_test"] = self_test(receipt, sources, edges)
    print(json.dumps(result, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
