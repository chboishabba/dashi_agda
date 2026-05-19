from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.w4w5_pdf_lhapdf_intake_preflight import (  # type: ignore[import-not-found]
    ARTIFACT_SCHEMA,
    build_preflight,
    read_candidate_packet,
)


def test_read_candidate_packet_extracts_w4_w5_binding(tmp_path: Path) -> None:
    packet_path = tmp_path / "ct18_candidate.json"
    packet_path.write_text(
        json.dumps(
            {
                "accepted_dy_luminosity_convention_status": "candidate_local_ct18nlo_convention_not_accepted",
                "accepted_dy_luminosity_first_missing": "missingAcceptedDYLuminosityConventionAuthority",
                "pdf_set": "CT18NLO",
                "set_index": 14400,
                "member": 0,
                "grid_sha256": "grid",
                "info_sha256": "info",
                "archive_sha256": "archive",
                "W4_luminosity_shape": [{"phi": 0.004, "luminosity_proxy": 1.0}],
                "W5_required_correction_factor": 0.8804486068,
                "W5_correction_factor": 1.0506681065158017,
                "W5_abs_gap": 0.17021949971580164,
                "W5_matching_target_luminosity_ratio": 0.7514043986785174,
                "W5_matching_target_luminosity_abs_gap": 0.12904420812148265,
                "W5_t43_denominator_hypothesis_ratio": 0.3348750784006896,
                "W5_t43_denominator_hypothesis_abs_gap": 0.5455735283993104,
            }
        ),
        encoding="utf-8",
    )

    candidate = read_candidate_packet(packet_path)

    assert candidate["present"] is True
    assert candidate["accepted_dy_luminosity_first_missing"] == "missingAcceptedDYLuminosityConventionAuthority"
    assert candidate["w4_candidate_bin_count"] == 1
    assert candidate["w5_t45_over_z_ratio"] == 0.7514043986785174
    assert len(candidate["sha256"]) == 64


def test_build_preflight_preserves_non_promotion_boundary(tmp_path: Path) -> None:
    payload = build_preflight(tmp_path, None)

    assert payload["artifact_schema"] == ARTIFACT_SCHEMA
    assert payload["promotion"] == {
        "w4": False,
        "w5": False,
        "pdf_carrier": False,
        "accepted_dy_convention": False,
    }
    assert payload["provider_authority"]["first_missing"] == "missingAcceptedDYLuminosityConventionAuthority"
    assert payload["w4_w5_correction_output_status"]["w5_t45"].startswith("not emitted")
    assert payload["lhapdf_backed_candidate_run"] == {
        "present": False,
        "status": "not_requested",
    }
