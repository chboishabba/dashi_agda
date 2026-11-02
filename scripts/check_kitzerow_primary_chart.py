#!/usr/bin/env python3
"""Negative controls for creator-chart identity, chronology and incomplete coverage."""
from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from compare_kitzerow_primary_chart import compare

ROOT = Path(__file__).resolve().parents[1]
CHART = ROOT / "docs/biology/KitzerowPublishedRheaChartObservedIndex.v1.json"


def rejects(chart: dict, matrix: dict) -> None:
    try:
        compare(chart, matrix)
    except ValueError:
        return
    raise AssertionError("invalid Kitzerow crosswalk was accepted")


def main() -> int:
    chart = json.loads(CHART.read_text())
    matrix = {"schema": "dashi.bh4-stoichiometric-matrix.v1",
              "reaction_index": ["RHEA:21708", "RHEA:99999"]}
    x = compare(chart, matrix)
    assert x["creator_chart_observed_rhea_id_count"] == 8
    assert x["dashi_finite_panel_rhea_id_count"] == 2
    assert x["literal_rhea_identifier_intersection"] == ["RHEA:21708"]
    assert x["creator_network_coverage_ratio"] is None
    assert x["source_pdf_binary_verified"] is False
    assert x["same_physiological_reaction_verified"] is False
    assert "RHEA:99999" in x["dashi_finite_panel_only"]
    assert compare(chart, matrix) == x

    b = deepcopy(chart); b["whole_proprietary_network_reconstructed"] = True
    rejects(b, matrix)
    b = deepcopy(chart); b["primary_claims_paid_by_source_index"] = True
    rejects(b, matrix)
    b = deepcopy(chart); b["rhea_identifiers"].append(b["rhea_identifiers"][0])
    rejects(b, matrix)
    b = deepcopy(chart); b["rhea_identifiers"][0]["web_text_line"] = 0
    rejects(b, matrix)
    b = deepcopy(matrix); b["reaction_index"] = ["RHEA:21708", "RHEA:21708"]
    rejects(chart, b)
    b = deepcopy(matrix); b["reaction_index"] = ["CHEBI:12"]
    rejects(chart, b)
    print("Kitzerow original-source Rhea crosswalk regression: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
