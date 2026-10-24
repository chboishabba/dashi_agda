from __future__ import annotations

import json
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from ns_canonical_focus import (  # noqa: E402
    historical_symbol_receipts, load_navigation, new_round_units,
    select_route, validate_local_owners,
)


def test_six_routes_reuse_existing_extraction_config_and_real_owners():
    nav = load_navigation()
    assert len(nav["routes"]) == 6
    assert validate_local_owners(nav) == []
    assert {r["id"] for r in nav["routes"]} == {
        "NS-ABCD", "NS-A", "NS-B", "NS-B4", "NS-B-RESERVE", "NS-CD",
    }


@pytest.mark.parametrize("alias", [
    "R823", "r829", "R830", "R831", "R832", "R833", "r850", "r853",
    "signed-reserve",
])
def test_numbered_aliases_collapse_to_existing_lean_source(alias):
    route = select_route(alias, load_navigation())
    assert route["route"] == "NS-B-RESERVE"
    assert route["owner"]["path"] == "NSBControl/Rational345R823DecisionFreeze.lean"
    assert route["historical_Round_authority"] is False
    assert route["kernel_certified_by_navigation"] is False


def test_positive_periodic_maintains_own_math_boundary():
    nav = load_navigation()
    assert select_route("B", nav)["route"] == "NS-B"
    assert select_route("B4", nav)["route"] == "NS-B4"
    assert select_route("R440", nav)["route"] == "NS-B4"
    assert select_route("C", nav)["route"] == "NS-CD"
    assert select_route("A", nav)["route"] == "NS-A"


def test_ABB4_land_at_source_mathematics_not_abstract_residual_records():
    nav = load_navigation()
    expected = {
        "A": "NSClayFacingAPureAnalysisFrontier20261007Exact.agda",
        "B": "NSClayFacingBPureAnalysisFrontier20261005Exact.agda",
        "B4": "NSTriadKNPhysicalCriticalTouchingDefectR44020261007Exact.agda",
    }
    for route, suffix in expected.items():
        selected = select_route(route, nav)
        assert selected["owner"]["path"].endswith(suffix)
        assert selected["kernel_certified_by_navigation"] is False
        assert len(selected["support"]) <= 3
    b4 = select_route("B4", nav)
    assert any("NSCanonicalB4PhysicalR440AnalyticInterfaceExact" in x["path"]
               for x in b4["support"])
    assert "uninhabited" in b4["status"]


def test_unknown_round_rejected_without_guessing_authority():
    with pytest.raises(ValueError, match="Do not create another Round"):
        select_route("R99999", load_navigation())


def test_duplicate_alias_rejected(tmp_path):
    path = tmp_path / "cfg.json"
    cfg = json.loads((ROOT / "config/ns-round-extraction-targets.json").read_text())
    cfg["canonical_navigation"]["routes"][1]["aliases"].append("R823")
    path.write_text(json.dumps(cfg))
    with pytest.raises(ValueError, match="ambiguous canonical alias"):
        load_navigation(path)


def test_archive_symbol_lookup_is_exact_bounded_and_nonpromoting(tmp_path):
    path = tmp_path / "ns-packages.jsonl"
    rows = [
        {
            "package_id": "p1", "candidate_names": ["signedRateFoo"],
            "disposition": "UNRESOLVED",
            "source_locations": ["oldRound1::signedRateFoo"] * 5,
            "unresolved_residuals": ["signedRateFoo"],
        },
        {
            "package_id": "p2", "candidate_names": ["signedRateFoo"],
            "disposition": "NEGATIVE_RESULT",
            "source_locations": ["oldRound2::signedRateFoo"],
        },
        {
            "package_id": "p3", "candidate_names": ["notSameName"],
            "disposition": "SUPERSEDED_EXACT",
        },
    ]
    path.write_text("".join(json.dumps(row) + "\n" for row in rows))
    result = historical_symbol_receipts("signedRateFoo", path, limit=1)
    assert result["matching_packages"] == 2
    assert result["dispositions"] == {"NEGATIVE_RESULT": 1, "UNRESOLVED": 1}
    assert result["sample_truncated"] is True
    assert len(result["sample"]) == 1
    assert len(result["sample"][0]["source_locations"]) == 2
    assert result["historical_receipts_establish_proof"] is False
    assert result["no_match_proves_absence"] is False
    assert historical_symbol_receipts("signedRate", path)["matching_packages"] == 0
    with pytest.raises(FileNotFoundError):
        historical_symbol_receipts("x", tmp_path / "missing.jsonl")


def test_guard_blocks_new_numbered_modules_but_not_existing_owner_edits():
    paths = [
        "DASHI/Physics/Closure/NSMysteryRound854Exact.agda",
        "NSBControl/Rational345R854Another.lean",
        "DASHI/Physics/Closure/NSCanonicalClayResidualExact.agda",
        "NSBControl/Rational345R823DecisionFreeze.lean",  # existing edit, not added
    ]
    assert new_round_units(paths[:3]) == paths[:2]
    assert new_round_units(paths[2:]) == [
        "NSBControl/Rational345R823DecisionFreeze.lean"
    ]
    assert new_round_units(["docs/round854.md", "NSCanonicalClayResidualExact.agda"]) == []
