#!/usr/bin/env python3
"""Compare source-observed Kitzerow Rhea IDs with the existing finite panel.

No invented overlap, biological-context equivalence, whole-author-network
denominator, or reproduced creator diagram. Upstream author/source remains
independent of Rhea chemistry and DASHI selection.

Kitzerow (2024-01), BH4/Folate/Cobalamin/Homocysteine Pathway,
ResearchGate publication 377218425, displayed full-text upload 2025-08-08;
stated source license CC BY-NC-ND 4.0. Input is an explicitly bounded index
of web-view text observations, NOT a verified original PDF transcription.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

SOURCE_SCHEMA = "dashi.kitzerow-primary-chart-rhea-index.v1"
MATRIX_SCHEMA = "dashi.bh4-stoichiometric-matrix.v1"
RESULT_SCHEMA = "dashi.kitzerow-chart-panel-identifier-crosswalk.v1"
RHEA_ID = re.compile(r"RHEA:[0-9]+$")


def compare(chart: dict, matrix: dict) -> dict:
    if chart.get("schema") != SOURCE_SCHEMA or matrix.get("schema") != MATRIX_SCHEMA:
        raise ValueError("chart and matrix must retain exact source ABI")
    if chart.get("creator") != "Kimberly Kitzerow":
        raise ValueError("original creator attribution lost")
    if not str(chart.get("publication_page", "")).startswith(
        "https://www.researchgate.net/publication/377218425_"
    ):
        raise ValueError("source URL missing")
    for field in ("declared_publication_month", "observed_full_text_upload_date",
                  "license_declared", "disclosure_scope"):
        if not chart.get(field):
            raise ValueError("source date/license/scope is incomplete: " + field)
    if any(chart.get(k) is not False for k in (
        "whole_proprietary_network_reconstructed",
        "primary_claims_paid_by_source_index",
        "same_compartment_flux_paid")):
        raise ValueError("source index improperly promoted")
    rows = chart.get("rhea_identifiers")
    if not isinstance(rows, list) or not rows:
        raise ValueError("no bounded chart observations")
    ids = []
    locators = {}
    for row in rows:
        rid = row.get("rhea_id")
        ln = row.get("web_text_line")
        if not isinstance(rid, str) or not RHEA_ID.fullmatch(rid):
            raise ValueError("Rhea reaction identifier invalid")
        if not isinstance(ln, int) or ln <= 0:
            raise ValueError("source observation missing line anchor")
        ids.append(rid)
        # Web extraction lines are reader coordinates, not actual URL fragments.
        locators[rid] = {
            "source_url": chart["publication_page"],
            "web_text_line": ln,
            "locator_kind": "web-extracted-text-line-not-original-pdf-page",
        }
    if len(set(ids)) != len(ids):
        raise ValueError("duplicate source reaction id")
    panel_rows = matrix.get("reaction_index")
    if not isinstance(panel_rows, list) or any(
        not isinstance(r, str) or not RHEA_ID.fullmatch(r) for r in panel_rows
    ) or len(panel_rows) != len(set(panel_rows)):
        raise ValueError("invalid finite-panel Rhea reaction set")
    chart_set, panel_set = set(ids), set(panel_rows)
    overlap = sorted(chart_set & panel_set)
    return {
        "schema": RESULT_SCHEMA,
        "creator": chart["creator"],
        "creator_work": chart["title"],
        "creator_work_source": chart["publication_page"],
        "creator_publication_month_declared": chart["declared_publication_month"],
        "full_text_upload_date_observed": chart["observed_full_text_upload_date"],
        "source_license": chart["license_declared"],
        "source_text_observation_scope": chart["disclosure_scope"],
        "creator_chart_observed_rhea_id_count": len(chart_set),
        "dashi_finite_panel_rhea_id_count": len(panel_set),
        "literal_rhea_identifier_intersection": overlap,
        "creator_chart_observed_only": sorted(chart_set - panel_set),
        "dashi_finite_panel_only": sorted(panel_set - chart_set),
        "source_line_locators": {k: locators[k] for k in sorted(locators)},
        "external_reaction_owner": "Rhea",
        "formalisation_owner": "DASHI",
        "creator_entire_network_reaction_count": None,
        "creator_network_coverage_ratio": None,
        "source_pdf_binary_verified": False,
        "same_physiological_reaction_verified": False,
        "matches_creator_causal_hypothesis": False,
        "quantitative_flux_established": False,
        "unresolved": [
            "complete creator-held BioGene network unavailable in the public source",
            "source original PDF/figure revision and line-to-geometry pairing",
            "reaction direction, compartment, isoform, kinetic and exchange context",
            "author proposed causal graph vs prior-art biochemical reactions",
        ],
    }

def compare_text_candidate_index(extracted: dict, matrix: dict) -> dict:
    """Compare all source-text observed IDs without promoting their authority.

    The caller supplies an index of authorized local UTF-8 text. This
    cannot establish the completeness of the author's original PDF or
    the full proprietary BioGene pathway network.
    """
    if extracted.get("schema") != "dashi.kitzerow-chart-source-text-identifier-candidates.v1":
        raise ValueError("wrong source-text candidate ABI")
    if extracted.get("creator") != "Kimberly Kitzerow":
        raise ValueError("source text creator identity mismatch")
    if not extracted.get("source_url", "").startswith(
        "https://www.researchgate.net/publication/377218425_"
    ):
        raise ValueError("unrecognized creator source")
    if not extracted.get("source_utf8_sha256") or not extracted.get("source_revision"):
        raise ValueError("source observation lacks digest or revision")
    if any(extracted.get(k) is not expected for k, expected in (
        ("candidate_only", True),
        ("source_is_faithful_publisher_binary", False),
        ("creator_pdf_figure_geometry_verified", False),
        ("not_creator_full_network_coverage", True),
        ("establishes_physical_flux", False),
        ("establishes_causal_model", False),
    )):
        raise ValueError("unearned text-source promotion")
    ids = extracted.get("text_observed_reaction_ids")
    rows = extracted.get("occurrences")
    if not isinstance(ids, list) or not isinstance(rows, list):
        raise ValueError("source text candidate record incomplete")
    if not ids or len(ids) != len(set(ids)) or any(
        not isinstance(rid, str) or not RHEA_ID.fullmatch(rid) for rid in ids
    ):
        raise ValueError("invalid source-observed identifier set")
    if not rows or {x.get("rhea_id") for x in rows} != set(ids):
        raise ValueError("source occurrences do not cover all observed IDs")
    for entry in rows:
        if (not isinstance(entry.get("source_text_line"), int)
                or entry["source_text_line"] <= 0
                or not isinstance(entry.get("normalized_line_column"), int)
                or entry["normalized_line_column"] <= 0
                or entry.get("review_status") != "candidate-unverified-figure-location"):
            raise ValueError("source occurrence has missing/invalid text anchors")
    panel_ids = matrix.get("reaction_index")
    if matrix.get("schema") != MATRIX_SCHEMA or not isinstance(panel_ids, list):
        raise ValueError("matrix ABI invalid")
    if len(panel_ids) != len(set(panel_ids)) or any(
        not isinstance(rid, str) or not RHEA_ID.fullmatch(rid) for rid in panel_ids
    ):
        raise ValueError("invalid finite-panel identifiers")
    chart_set, panel_set = set(ids), set(panel_ids)
    return {
        "schema": RESULT_SCHEMA,
        "creator": "Kimberly Kitzerow",
        "creator_work_source": extracted["source_url"],
        "source_text_revision": extracted["source_revision"],
        "source_utf8_sha256": extracted["source_utf8_sha256"],
        "source_basis": "caller-supplied-text-observation-candidate",
        "creator_chart_observed_rhea_id_count": len(chart_set),
        "dashi_finite_panel_rhea_id_count": len(panel_set),
        "literal_rhea_identifier_intersection": sorted(chart_set & panel_set),
        "creator_chart_observed_only": sorted(chart_set - panel_set),
        "dashi_finite_panel_only": sorted(panel_set - chart_set),
        "source_text_occurrence_count": len(rows),
        "source_occurrences": rows,
        "creator_entire_network_reaction_count": None,
        "creator_network_coverage_ratio": None,
        "source_pdf_binary_verified": False,
        "same_physiological_reaction_verified": False,
        "matches_creator_causal_hypothesis": False,
        "quantitative_flux_established": False,
        "external_reaction_owner": "Rhea",
        "formalisation_owner": "DASHI",
        "unresolved": [
            "source text was caller-supplied, not authenticated as original PDF",
            "chart geometry and original PDF passages unverified",
            "complete proprietary BioGene network remains unknown",
            "same-context compartment, reaction direction and kinetics are unverified",
        ],
    }


def compare_chart_and_optional_text(chart: dict, matrix: dict,
                                    source_text: dict | None = None) -> dict:
    base = compare(chart, matrix)
    if source_text is not None:
        base["local_source_text_observation"] = compare_text_candidate_index(
            source_text, matrix)
        base["source_observations_are_distinct"] = True
    return base


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--chart", type=Path, default=Path(
        "docs/biology/KitzerowPublishedRheaChartObservedIndex.v1.json"))
    p.add_argument("--matrix", type=Path, required=True)
    p.add_argument("--source-text-index", type=Path,
                   help="optional candidate-only index produced from user-authorized local source text")
    p.add_argument("-o", "--output", type=Path, required=True)
    a = p.parse_args()
    text_index = json.loads(a.source_text_index.read_text()) if a.source_text_index else None
    result = compare_chart_and_optional_text(
        json.loads(a.chart.read_text()), json.loads(a.matrix.read_text()), text_index)
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "chart_source_ids": result["creator_chart_observed_rhea_id_count"],
        "panel_ids": result["dashi_finite_panel_rhea_id_count"],
        "observed_overlap": len(result["literal_rhea_identifier_intersection"]),
        "whole_creator_coverage": "unknown",
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
