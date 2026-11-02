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
        locators[rid] = chart["publication_page"] + "#L" + str(ln)
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


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--chart", type=Path, default=Path(
        "docs/biology/KitzerowPublishedRheaChartObservedIndex.v1.json"))
    p.add_argument("--matrix", type=Path, required=True)
    p.add_argument("-o", "--output", type=Path, required=True)
    a = p.parse_args()
    result = compare(json.loads(a.chart.read_text()), json.loads(a.matrix.read_text()))
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
