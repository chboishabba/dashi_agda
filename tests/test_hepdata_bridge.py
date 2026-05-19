from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.hepdata_adapter import (  # type: ignore[import-not-found]
    FAMILY_CROSSWALK_PATH,
    load_family_crosswalk,
    resolve_family_spec,
)
from scripts.hepdata_program_surface import (  # type: ignore[import-not-found]
    PROGRAM_STATUS,
    build_program_surface,
)


FIXTURE_PATH = (
    Path(__file__).resolve().parent / "fixtures" / "hepdata_family_crosswalk_fixture.json"
)


def test_crosswalk_fixture_cases_match_current_mapping() -> None:
    crosswalk = load_family_crosswalk(FAMILY_CROSSWALK_PATH)
    fixture = json.loads(FIXTURE_PATH.read_text(encoding="utf-8"))

    for case in fixture["cases"]:
        family = case["family"]
        expected = case["expected"]
        spec = resolve_family_spec(crosswalk, family)

        assert spec["canonical_family"] == expected["canonical_family"]
        assert spec["measurement"]["npz"] == expected["measurement_npz"]
        assert spec["metrics"] == expected["metrics"]
        assert spec["timeseries"] == expected["timeseries"]
        assert spec["certification_labels"] == expected["certification_labels"]


def test_ptll_table_family_is_not_collapsed_into_compact_ptll_family() -> None:
    crosswalk = load_family_crosswalk(FAMILY_CROSSWALK_PATH)
    fixture = json.loads(FIXTURE_PATH.read_text(encoding="utf-8"))
    left = fixture["non_alias_rule"]["left"]
    right = fixture["non_alias_rule"]["right"]

    left_spec = resolve_family_spec(crosswalk, left)
    right_spec = resolve_family_spec(crosswalk, right)

    assert left_spec["canonical_family"] != right_spec["canonical_family"]
    assert left_spec["measurement"]["npz"] != right_spec["measurement"]["npz"]


def test_program_surface_promotes_validated_measurement_report_path() -> None:
    artifact = {
        "artifact_schema": "dashi-hpdata-empirical-v1",
        "schema_version": "1.0.0",
        "family": {
            "family": "toy-family",
            "measurement": {
                "status": "ok",
                "kind": "npz",
                "path": "toy-family.npz",
                "field_status": {"x": "ok", "y": "ok", "cov": "ok"},
                "x": [1.0, 2.0],
                "y": [3.0, 5.0],
                "cov": [[1.0, 0.0], [0.0, 2.0]],
            },
            "validation_summary": {
                "validation_status": "empirical-artifact-ready",
            },
            "evidence_summary": {
                "counts": {"measurements": 1, "samples": 1},
            },
        },
    }

    surface = build_program_surface(artifact)

    assert surface["program_status"] == PROGRAM_STATUS
    assert surface["gates"]["measurement_ready"] is True
    assert surface["gates"]["projection_eligible"] is True
    assert surface["measurement_summary"]["trace_id"] == "toy-family"
    assert surface["surface_report"]["point_count"] == 2
