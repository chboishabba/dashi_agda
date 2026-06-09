from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = REPO_ROOT / "scripts"

IDENTITY_STEM = "ns_sprint151_localized_enstrophy_identity"
CUTOFF_STEM = "ns_sprint151_cutoff_error_budget"

CONTROL_CARD_KEYS = {"O", "R", "C", "S", "L", "P", "G", "F"}
IDENTITY_REQUIRED_ROW_IDS = {
    "localized_enstrophy_definition",
    "omega1_equation_input",
    "cutoff_derivative",
    "transport_flux",
    "diffusion_coercive_term",
    "boundary_annular_leakage",
    "vortex_stretching_source",
    "biot_savart_nonlocal_closure",
    "constants_compatibility",
    "model_width_ode_extraction",
    "clay_guard",
}
CUTOFF_REQUIRED_ROW_IDS = {
    "cutoff_gradient_scale_delta_inverse",
    "cutoff_laplacian_scale_delta_inverse_square",
    "transport_flux_cutoff_boundary",
    "diffusion_leakage_cutoff_laplacian",
    "source_localization_core_window",
    "annular_leakage_outer_shell",
    "absorption_margin_transport_diffusion",
    "absorption_margin_annular_source",
}
FALSE_FLAG_NAMES = {
    "localized_enstrophy_identity_proved",
    "model_validity_for_width_ode",
    "scaling_coupling_consistency",
    "symmetric_hou_luo_bkm_finite",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
    "promotion_allowed",
    "claim_closed",
    "claim_proved",
    "claim_proven",
}
TRUE_COMPLETION_PATTERNS = (
    re.compile(
        r'"(?:localized_enstrophy_identity_proved|model_validity_for_width_ode|'
        r'scaling_coupling_consistency|symmetric_hou_luo_bkm_finite|'
        r'full_clay_ns_solved|clay_navier_stokes_promoted|promotion_allowed|'
        r'claim_closed|claim_proved|claim_proven)"\s*:\s*true\b',
        re.IGNORECASE,
    ),
)


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def normalize(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(value).lower()).strip("_")


def as_bool(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str) and value.lower() in {"true", "false"}:
        return value.lower() == "true"
    return None


def run_script(stem: str, tmp_path: Path) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
    script = SCRIPT_DIR / f"{stem}.py"
    assert script.is_file(), f"missing script: {script.relative_to(REPO_ROOT)}"

    out_dir = tmp_path / stem
    result = subprocess.run(
        [
            sys.executable,
            str(script),
            "--repo-root",
            str(REPO_ROOT),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    artifact_paths = sorted(out_dir.glob("*")) if out_dir.exists() else []
    json_paths = [path for path in artifact_paths if path.suffix.lower() == ".json"]
    csv_paths = [path for path in artifact_paths if path.suffix.lower() == ".csv"]
    md_paths = [path for path in artifact_paths if path.suffix.lower() == ".md"]
    text = "\n".join(
        [result.stdout, result.stderr]
        + [
            path.read_text(encoding="utf-8", errors="replace")
            for path in [*json_paths, *csv_paths, *md_paths]
        ]
    )

    assert result.returncode == 0, text
    assert out_dir.is_dir(), text
    assert json_paths, text
    assert csv_paths, text
    assert md_paths, text

    payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    rows: list[dict[str, Any]] = []
    for item in walk(payloads):
        if isinstance(item, dict) and any(
            normalize(key) in {"row_id", "status", "classification"} for key in item
        ):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))

    assert rows, text
    return payloads, rows, text, out_dir


def row_ids(rows: list[dict[str, Any]]) -> set[str]:
    return {
        normalize(row["row_id"])
        for row in rows
        if isinstance(row.get("row_id"), str) and row["row_id"].strip()
    }


def bool_values_for_keys(values: list[Any], *names: str) -> list[bool]:
    wanted = {normalize(name) for name in names}
    found: list[bool] = []
    for item in walk(values):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize(key) in wanted:
                parsed = as_bool(value)
                if parsed is not None:
                    found.append(parsed)
    return found


def assert_control_card(payloads: list[Any], text: str) -> None:
    for item in walk(payloads):
        if not isinstance(item, dict):
            continue
        card = item.get("control_card") or item.get("control-card")
        if isinstance(card, dict) and CONTROL_CARD_KEYS.issubset({str(key) for key in card}):
            return
    normalized_text = normalize(text)
    assert all(normalize(key) in normalized_text for key in CONTROL_CARD_KEYS), text


def assert_fail_closed_flags(payloads: list[Any], rows: list[dict[str, Any]], text: str) -> None:
    for name in FALSE_FLAG_NAMES:
        values = bool_values_for_keys([payloads, rows], name)
        if values:
            assert all(value is False for value in values), (name, values)
    for pattern in TRUE_COMPLETION_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_localized_enstrophy_identity_emitter_records_required_fail_closed_rows(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_script(IDENTITY_STEM, tmp_path)
    ids = row_ids(rows)

    assert out_dir.name == IDENTITY_STEM
    assert {normalize(row_id) for row_id in IDENTITY_REQUIRED_ROW_IDS} <= ids
    assert_control_card(payloads, text)
    assert_fail_closed_flags(payloads, rows, text)

    summary = next(
        item
        for item in walk(payloads)
        if isinstance(item, dict)
        and item.get("contract") == IDENTITY_STEM
        and item.get("decision") == "localized_enstrophy_identity_not_proved_fail_closed"
    )
    assert summary["invariant_valid"] is True
    assert summary["artifact_complete"] is True
    assert summary["row_count"] == 11
    assert summary["decision"] == "localized_enstrophy_identity_not_proved_fail_closed"
    assert summary["localized_enstrophy_identity_proved"] is False
    assert summary["model_validity_for_width_ode"] is False
    assert summary["scaling_coupling_consistency"] is False
    assert summary["symmetric_hou_luo_bkm_finite"] is False
    assert summary["full_clay_ns_solved"] is False

    by_id = {normalize(row["row_id"]): row for row in rows if "row_id" in row}
    assert by_id["clay_guard"]["status"] == "FAIL_CLOSED_NOT_PROMOTED"
    assert by_id["model_width_ode_extraction"]["width_ode_ready"] in {False, "False"}


def test_cutoff_error_budget_emitter_records_absorbed_support_open_and_blocker_rows(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_script(CUTOFF_STEM, tmp_path)
    ids = row_ids(rows)

    assert out_dir.name == CUTOFF_STEM
    assert {normalize(row_id) for row_id in CUTOFF_REQUIRED_ROW_IDS} <= ids
    assert_fail_closed_flags(payloads, rows, text)

    summary = next(
        item
        for item in walk(payloads)
        if isinstance(item, dict)
        and item.get("contract") == CUTOFF_STEM
        and item.get("decision") == "fail_closed_cutoff_budget_has_open_and_blocker_rows"
    )
    assert summary["validation_passed"] is True
    assert summary["decision"] == "fail_closed_cutoff_budget_has_open_and_blocker_rows"
    assert summary["classification_counts"] == {
        "absorbed": 3,
        "blocker": 1,
        "open": 2,
        "support": 2,
    }
    assert summary["source_localization_closed"] is False
    assert summary["annular_leakage_closed"] is False
    assert summary["absorption_margins_close_all_errors"] is False

    by_id = {normalize(row["row_id"]): row for row in rows if "row_id" in row}
    assert by_id["transport_flux_cutoff_boundary"]["classification"] == "absorbed"
    assert by_id["diffusion_leakage_cutoff_laplacian"]["classification"] == "absorbed"
    assert by_id["source_localization_core_window"]["classification"] == "open"
    assert by_id["annular_leakage_outer_shell"]["classification"] == "blocker"
