#!/usr/bin/env python3
"""Negative controls for creator-chart identity, chronology and incomplete coverage."""
from __future__ import annotations

import json
import re
from copy import deepcopy
from pathlib import Path
from compare_kitzerow_primary_chart import compare, compare_text_candidate_index, compare_chart_and_optional_text
from index_kitzerow_chart_source_text import index_text

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
    # Prevent independent drift between the checked manual JSON observation
    # and the small Agda source-typed list. Agda is the golden formal owner.
    creator_owner = ROOT / "DASHI/Biology/BH4CreatorChartSourceBridgeExact.agda"
    creator_text = creator_owner.read_text(encoding="utf-8")
    chart_block = creator_text.split("observedSourceRheaIds =\n", 1)[1].split(
        "\n\nobservedSourceRheaIdCount :", 1)[0]
    agda_chart_ids = re.findall(r'"(RHEA:[0-9]+)"', chart_block)
    json_chart_ids = [item["rhea_id"] for item in chart["rhea_identifiers"]]
    assert len(agda_chart_ids) == len(json_chart_ids) == 8
    assert len(set(agda_chart_ids)) == len(agda_chart_ids)
    assert sorted(agda_chart_ids) == sorted(json_chart_ids)
    # Compare the real source-observed 8 IDs to the actual Agda golden
    # finitePanelReactionIds owner (not the synthetic fixture above).
    owner = ROOT / "DASHI/Biology/Molecular/BH4ExecutedPanelReactionReceiptExact.agda"
    owner_text = owner.read_text(encoding="utf-8")
    finite_src = owner_text.split("finitePanelReactionIds =\n", 1)[1].split(
        "\n\nresidualPanelReactionIds :", 1)[0]
    canonical_ids = re.findall(r'"(RHEA:[0-9]+)"', finite_src)
    assert len(canonical_ids) == 12 and len(set(canonical_ids)) == 12
    actual = compare(chart, {"schema": "dashi.bh4-stoichiometric-matrix.v1",
                             "reaction_index": canonical_ids})
    # Source-index cardinality 8 is not a whole-author-network denominator.
    assert actual["literal_rhea_identifier_intersection"] == []
    assert len(actual["creator_chart_observed_only"]) == 8
    assert len(actual["dashi_finite_panel_only"]) == 12
    assert actual["creator_network_coverage_ratio"] is None

    # Original-chart source-text indexing is an optional *additional*
    # candidate observation; it must not replace the manually inspected
    # source ID set or claim a complete creator network.
    extracted = index_text(
        b"Rhea:21708\nRhea 10112\nRhea:21708\n",
        source_url=chart["publication_page"],
        source_revision="source-text-observation:2026-11-02",
    )
    alt = compare_text_candidate_index(extracted, matrix)
    assert alt["literal_rhea_identifier_intersection"] == ["RHEA:21708"]
    assert alt["creator_chart_observed_rhea_id_count"] == 2
    assert alt["source_text_occurrence_count"] == 3
    assert alt["creator_network_coverage_ratio"] is None
    joined = compare_chart_and_optional_text(chart, matrix, extracted)
    assert joined["local_source_text_observation"] == alt
    assert joined["creator_chart_observed_rhea_id_count"] == 8
    tampered = deepcopy(extracted)
    tampered["candidate_only"] = False
    try:
        compare_text_candidate_index(tampered, matrix)
    except ValueError:
        pass
    else:
        raise AssertionError("source text was automatically promoted")

    print("Kitzerow original-source Rhea crosswalk regression: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
