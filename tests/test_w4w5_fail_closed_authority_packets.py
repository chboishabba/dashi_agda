from __future__ import annotations

import json
from pathlib import Path
import sys
from typing import Any

import pytest

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import dy_luminosity_from_authority_packet as dy_authority  # type: ignore[import-not-found]
from scripts import run_w4_z_peak_adequacy as w4_adequacy  # type: ignore[import-not-found]
from scripts import run_w5_t45_pdf_correction as w5_t45  # type: ignore[import-not-found]


CURRENT_CT18_CANDIDATE = ROOT / "scripts" / "data" / "pdf" / "ct18_dashi_pdf_packet.json"
CURRENT_PREFLIGHT = (
    ROOT / "scripts" / "data" / "outputs" / "w4w5_lhapdf_intake_preflight_current.json"
)
ACCEPTED_REPLACEMENT_SCHEMA = (
    ROOT / "scripts" / "data" / "authority_packet.accepted_replacement.schema.json"
)


def adapter_schema_shaped_packet(status: str = "accepted") -> dict[str, Any]:
    return {
        "status": status,
        "provider_name": "fixture provider",
        "provider_role": "test-only schema shape",
        "pdf_set_version": "fixture-pdf-v1",
        "lhapdf_id": "fixture-lhapdf-id",
        "member_id": "0",
        "grid_checksum": "sha256:fixture",
        "scale_convention": "Q = M",
        "rapidity_window": "|y| < 2.4",
        "mass_bin_rule": "fixture mass bins",
        "flavour_weight_rule": "fixture flavour weights",
        "integration_method": "fixture integration",
        "source_citation": "fixture citation",
        "attestation_no_manual_overfit": "fixture attestation",
        "luminosities": {
            "L43": 1.0,
            "L45": 0.8804486068,
            "W4_per_bin_luminosities": [1.0, {"luminosity": 2.0}],
        },
    }


def assert_schema_shaped_packet(packet: dict[str, Any], schema: dict[str, Any]) -> None:
    required = schema["required"]
    assert all(field in packet for field in required)
    assert packet["status"] in schema["properties"]["status"]["enum"]
    assert "candidate_local_ct18nlo_convention_not_accepted" not in schema["properties"]["status"]["enum"]
    assert isinstance(packet["luminosities"], dict)
    assert any(key in packet["luminosities"] for key in ("L43", "L_M43_Y43", "L_50_76", "L_M50_76", "luminosity_43"))
    assert any(key in packet["luminosities"] for key in ("L45", "L_M45_Y45", "L_106_170", "L_M106_170", "luminosity_45"))
    assert any(
        key in packet["luminosities"]
        for key in (
            "W4_per_bin",
            "W4_per_bin_luminosities",
            "W4_luminosity_bins",
            "W4_luminosities",
            "L_W4_bins",
            "z_peak_per_bin_luminosities",
        )
    )


def test_accepted_replacement_schema_is_valid_json_and_shape_only() -> None:
    schema = json.loads(ACCEPTED_REPLACEMENT_SCHEMA.read_text(encoding="utf-8"))

    assert schema["$schema"] == "https://json-schema.org/draft/2020-12/schema"
    assert schema["type"] == "object"
    assert schema["properties"]["status"]["enum"] == ["accepted", "replacement"]
    assert "Passing this schema does not create or imply accepted DY authority" in schema["description"]
    assert_schema_shaped_packet(adapter_schema_shaped_packet(), schema)


def test_candidate_status_shape_is_rejected_by_authority_adapter(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    packet_path = tmp_path / "candidate_status_authority_shape.json"
    packet_path.write_text(
        json.dumps(
            adapter_schema_shaped_packet(
                status="candidate_local_ct18nlo_convention_not_accepted"
            ),
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    output_path = tmp_path / "dy_luminosity_artifact.json"
    w4_authority_path = tmp_path / "w4_authority.json"
    w5_packet_path = tmp_path / "w5_provider_packet.json"

    exit_code = dy_authority.main(
        [
            "--authority-packet",
            str(packet_path),
            "--output",
            str(output_path),
            "--write-w4-authority-json",
            str(w4_authority_path),
            "--write-w5-provider-packet",
            str(w5_packet_path),
        ]
    )

    captured = capsys.readouterr()
    assert exit_code == dy_authority.EXIT_PACKET_INVALID
    assert "authority packet invalid" in captured.err
    assert "authority status must be accepted or replacement" in captured.err
    assert not output_path.exists()
    assert not w4_authority_path.exists()
    assert not w5_packet_path.exists()


def test_schema_shaped_packet_is_not_a_w4_or_w5_authority_receipt(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    schema = json.loads(ACCEPTED_REPLACEMENT_SCHEMA.read_text(encoding="utf-8"))
    packet_path = tmp_path / "schema_shaped_adapter_packet.json"
    packet = adapter_schema_shaped_packet()
    assert_schema_shaped_packet(packet, schema)
    packet_path.write_text(json.dumps(packet, indent=2, sort_keys=True), encoding="utf-8")

    w5_output_path = tmp_path / "w5_receipt.json"
    w5_exit_code = w5_t45.main(
        [
            "--provider-packet",
            str(packet_path),
            "--output",
            str(w5_output_path),
        ]
    )
    w5_captured = capsys.readouterr()
    assert w5_exit_code == w5_t45.EXIT_PROVIDER_PACKET_INVALID
    assert "provider packet invalid" in w5_captured.err
    assert "accepted_dy_luminosity_convention must be an object" in w5_captured.err
    assert not w5_output_path.exists()

    w4_output_path = tmp_path / "w4_adequacy.json"
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "run_w4_z_peak_adequacy.py",
            "--accepted-dy-authority",
            str(packet_path),
            "--measurement-csv",
            str(tmp_path / "measurement.csv"),
            "--measurement-column",
            "measurement",
            "--prediction-csv",
            str(tmp_path / "prediction.csv"),
            "--prediction-column",
            "prediction",
            "--luminosity-csv",
            str(tmp_path / "luminosity.csv"),
            "--luminosity-column",
            "luminosity",
            "--sigma-csv",
            str(tmp_path / "sigma.csv"),
            "--sigma-column",
            "sigma",
            "--output",
            str(w4_output_path),
        ],
    )

    w4_exit_code = w4_adequacy.main()
    w4_captured = capsys.readouterr()
    assert w4_exit_code == w4_adequacy.EXIT_AUTHORITY_MISSING
    assert "blocked: missing accepted DY luminosity convention authority" in w4_captured.err
    assert "authority file is missing required fields" in w4_captured.err
    assert not w4_output_path.exists()


@pytest.mark.parametrize(
    ("packet_path", "expected_error"),
    [
        (CURRENT_CT18_CANDIDATE, "status: expected nonempty string"),
        (CURRENT_PREFLIGHT, "status must be accepted or replacement"),
    ],
)
def test_current_ct18_artifacts_do_not_unlock_w5_t45_runner(
    packet_path: Path,
    expected_error: str,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    output_path = tmp_path / "w5_receipt.json"

    exit_code = w5_t45.main(
        [
            "--provider-packet",
            str(packet_path),
            "--output",
            str(output_path),
        ]
    )

    captured = capsys.readouterr()
    assert exit_code == w5_t45.EXIT_PROVIDER_PACKET_INVALID
    assert "provider packet invalid" in captured.err
    assert expected_error in captured.err
    assert not output_path.exists()


@pytest.mark.parametrize("packet_path", [CURRENT_CT18_CANDIDATE, CURRENT_PREFLIGHT])
def test_current_ct18_artifacts_do_not_unlock_w4_z_peak_runner(
    packet_path: Path,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    output_path = tmp_path / "w4_adequacy.json"
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "run_w4_z_peak_adequacy.py",
            "--accepted-dy-authority",
            str(packet_path),
            "--measurement-csv",
            str(tmp_path / "measurement.csv"),
            "--measurement-column",
            "measurement",
            "--prediction-csv",
            str(tmp_path / "prediction.csv"),
            "--prediction-column",
            "prediction",
            "--luminosity-csv",
            str(tmp_path / "luminosity.csv"),
            "--luminosity-column",
            "luminosity",
            "--sigma-csv",
            str(tmp_path / "sigma.csv"),
            "--sigma-column",
            "sigma",
            "--output",
            str(output_path),
        ],
    )

    exit_code = w4_adequacy.main()

    captured = capsys.readouterr()
    assert exit_code == w4_adequacy.EXIT_AUTHORITY_MISSING
    assert "blocked: missing accepted DY luminosity convention authority" in captured.err
    assert "authority file is missing required fields" in captured.err
    assert not output_path.exists()


@pytest.mark.parametrize(
    ("packet_path", "expected_error"),
    [
        (CURRENT_CT18_CANDIDATE, "status: expected nonempty string"),
        (CURRENT_PREFLIGHT, "authority status must be accepted or replacement"),
    ],
)
def test_current_ct18_artifacts_are_not_authority_adapter_inputs(
    packet_path: Path,
    expected_error: str,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    output_path = tmp_path / "dy_luminosity_artifact.json"
    w4_authority_path = tmp_path / "w4_authority.json"
    w5_packet_path = tmp_path / "w5_provider_packet.json"

    exit_code = dy_authority.main(
        [
            "--authority-packet",
            str(packet_path),
            "--output",
            str(output_path),
            "--write-w4-authority-json",
            str(w4_authority_path),
            "--write-w5-provider-packet",
            str(w5_packet_path),
        ]
    )

    captured = capsys.readouterr()
    assert exit_code == dy_authority.EXIT_PACKET_INVALID
    assert "authority packet invalid" in captured.err
    assert expected_error in captured.err
    assert not output_path.exists()
    assert not w4_authority_path.exists()
    assert not w5_packet_path.exists()
