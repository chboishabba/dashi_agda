#!/usr/bin/env python3
"""Offline acceptance for creator-first Rhea acquisition using injected responses."""
from __future__ import annotations

import json
import tempfile
from copy import deepcopy
from pathlib import Path

from acquire_rhea_chebi_bh4_reactions import (
    acquire_source_chart, extract_source_chart_rhea,
)

ROOT = Path(__file__).resolve().parents[1]
CHART = ROOT / "docs/biology/KitzerowPublishedRheaChartObservedIndex.v1.json"


def reject(chart: dict) -> None:
    try:
        extract_source_chart_rhea(chart)
    except ValueError:
        return
    raise AssertionError("unlicensed creator-source index passed")


def main() -> int:
    src = json.loads(CHART.read_text(encoding="utf-8"))
    expected = extract_source_chart_rhea(src)
    assert len(expected) == 8 and expected == sorted(expected)
    assert "RHEA:21708" in expected
    fake = lambda rid: {
        "rhea_id": rid, "formula_charge_ready": False,
        "raw_sha256": "fixture-not-real-source",
        "participant_sparql_response_sha256": "fixture-not-real-source",
        "participants": [],
    }
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "chart.json"
        path.write_text(json.dumps(src), encoding="utf-8")
        packet, code = acquire_source_chart(path, reaction_fetcher=fake)
        assert code == 0 and not packet["errors"]
        assert packet["schema"] == "dashi.rhea-chebi-bh4-source-chart.v1"
        assert packet["rhea_rows_acquired"] == 8
        assert packet["source_rhea_ids_requested"] == expected
        assert packet["source_chart_pdf_sha256_verified"] is False
        assert packet["whole_creator_network_complete"] is False
        assert packet["promotion_boundary"]["creator_selected_pathway_is_DASHI_finite_panel"] is False
        assert packet["formula_charge_ready_reactions"] == 0

        def partially_failed(rid: str) -> dict:
            if rid == expected[0]:
                raise RuntimeError("fixture acquisition error, not biological absence")
            return fake(rid)

        incomplete, exit_code = acquire_source_chart(path, reaction_fetcher=partially_failed)
        assert exit_code == 3
        assert incomplete["rhea_rows_failed"] == 1
        assert incomplete["complete_reaction_identity_acquisition"] is False
        assert len(incomplete["errors"]) == 1

        wrong_id, exit_code = acquire_source_chart(
            path, reaction_fetcher=lambda rid: {"rhea_id": "RHEA:99999"})
        assert exit_code == 3
        assert len(wrong_id["reactions"]) == 0

    modified = deepcopy(src)
    modified["rhea_identifiers"].append(deepcopy(modified["rhea_identifiers"][0]))
    reject(modified)
    modified = deepcopy(src)
    modified["creator"] = "Rhea"
    reject(modified)
    modified = deepcopy(src)
    modified["same_compartment_flux_paid"] = True
    reject(modified)
    modified = deepcopy(src)
    modified["rhea_identifiers"][0]["web_text_line"] = True
    reject(modified)
    print("Kitzerow source-first Rhea acquisition regression: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
