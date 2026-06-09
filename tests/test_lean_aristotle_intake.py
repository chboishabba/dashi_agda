from __future__ import annotations

import json
from pathlib import Path

from scripts.lean_aristotle_intake import (
    DEFAULT_ALLM,
    DEFAULT_LEAN_REPO,
    build_intake,
    main_import_modules,
    selected_request_modules,
    write_outputs,
)


def test_archived_aristotle_allm_counts_19_modules() -> None:
    text = DEFAULT_ALLM.read_text(encoding="utf-8")

    selected = selected_request_modules(text)
    imports = main_import_modules(text)

    assert len(selected) == 20
    assert len(imports) == 19
    assert sorted(Path(name).stem for name in selected if name != "Main.lean") == sorted(imports)
    assert "Main.lean" in selected
    assert "DashiCarrier.lean" in selected
    assert "DashiHierarchy.lean" in selected
    assert "BottPeriodicity.lean" in selected


def test_intake_payload_is_non_promoting_and_distinguishes_current_checkout() -> None:
    payload = build_intake(
        lean_repo=DEFAULT_LEAN_REPO,
        allm_path=DEFAULT_ALLM,
        generated_at="2026-06-07T00:00:00+00:00",
    )

    assert payload["schema"] == "dashi-lean-aristotle-intake-v1"
    assert payload["selected_request_project_lean_file_count"] == 20
    assert payload["selected_request_project_formal_module_count"] == 19
    assert payload["main_import_module_count"] == 19
    assert payload["summary_claims"]["allm_claims_zero_sorry"] is True
    assert payload["summary_claims"]["allm_claims_standard_axioms"] is True
    assert payload["gates"]["archived_request_project_formal_module_count_is_19"] is True
    assert payload["gates"]["archived_request_project_lean_file_count_is_20_including_main"] is True
    assert payload["gates"]["archived_main_imports_match_selected_modules"] is True
    assert payload["gates"]["current_checkout_inspected"] is True
    assert payload["gates"]["current_checkout_is_same_as_archived_request_project"] is False
    assert payload["gates"]["lean_build_rerun"] is False
    assert payload["gates"]["zero_sorry_claim_rerun"] is False
    assert payload["gates"]["authority_promoted"] is False
    assert payload["gates"]["unification_promoted"] is False
    assert payload["current_checkout"]["lean_file_count"] >= 1
    assert payload["intake_digest"]


def test_write_outputs_round_trips_json(tmp_path: Path) -> None:
    payload = build_intake(
        lean_repo=DEFAULT_LEAN_REPO,
        allm_path=DEFAULT_ALLM,
        generated_at="2026-06-07T00:00:00+00:00",
    )

    write_outputs(payload, tmp_path)

    json_path = tmp_path / "lean_aristotle_intake.json"
    md_path = tmp_path / "lean_aristotle_intake.md"
    loaded = json.loads(json_path.read_text(encoding="utf-8"))

    assert loaded["intake_digest"] == payload["intake_digest"]
    assert "`DashiKernel.lean`" in md_path.read_text(encoding="utf-8")
