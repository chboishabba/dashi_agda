from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint134_axisymmetric_equation_correction"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"

CLAY_TRUE_PATTERNS = (
    re.compile(r'"clay[^"]*"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bclay[A-Za-z0-9_]*\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_correction_script(tmp_path: Path) -> tuple[dict[str, Any], list[dict[str, Any]], str, Path]:
    assert SCRIPT.is_file(), f"missing Worker 1 Sprint 134 script: {SCRIPT.relative_to(REPO_ROOT)}"

    out_dir = tmp_path / STEM
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
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

    artifact_paths = sorted(
        path for path in out_dir.glob("*") if path.suffix.lower() in {".json", ".csv", ".md"}
    ) if out_dir.exists() else []
    artifact_text = "\n".join(
        [result.stdout, result.stderr]
        + [path.read_text(encoding="utf-8", errors="replace") for path in artifact_paths]
    )

    assert result.returncode == 0, artifact_text
    assert out_dir.is_dir(), artifact_text
    assert any(path.suffix == ".json" for path in artifact_paths), artifact_text
    assert any(path.suffix == ".csv" for path in artifact_paths), artifact_text
    assert any(path.suffix == ".md" for path in artifact_paths), artifact_text
    assert all(path.stat().st_size > 0 for path in artifact_paths), artifact_text

    json_payloads = [
        json.loads(path.read_text(encoding="utf-8"))
        for path in artifact_paths
        if path.suffix == ".json"
    ]
    csv_rows: list[dict[str, Any]] = []
    for path in artifact_paths:
        if path.suffix != ".csv":
            continue
        with path.open(newline="", encoding="utf-8") as handle:
            csv_rows.extend(dict(row) for row in csv.DictReader(handle))

    summary: dict[str, Any] = {}
    for payload in json_payloads:
        if isinstance(payload, dict):
            summary.update(payload)
    rows = flatten_rows(json_payloads) + csv_rows
    assert summary or rows, "expected nonempty JSON/CSV content"
    return summary, rows, artifact_text, out_dir


def flatten_rows(value: Any) -> list[dict[str, Any]]:
    if isinstance(value, dict):
        rows: list[dict[str, Any]] = []
        for key in (
            "rows",
            "claims",
            "lemmas",
            "equations",
            "corrections",
            "gates",
            "artifacts",
        ):
            child = value.get(key)
            if isinstance(child, list):
                rows.extend(item for item in child if isinstance(item, dict))
        if looks_like_row(value):
            rows.append(value)
        for child in value.values():
            rows.extend(flatten_rows(child))
        return rows
    if isinstance(value, list):
        return [row for child in value for row in flatten_rows(child)]
    return []


def looks_like_row(value: dict[str, Any]) -> bool:
    if set(value) == {"key", "value"}:
        return False
    row_keys = {
        "lemma",
        "lemma_id",
        "claim",
        "claim_id",
        "equation",
        "equation_id",
        "status",
        "correction",
        "old_claim",
        "new_claim",
    }
    return bool(row_keys.intersection(value))


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def joined_text(*values: Any) -> str:
    return "\n".join(
        value if isinstance(value, str) else json.dumps(value, sort_keys=True, default=str)
        for value in values
    )


def compact(value: str) -> str:
    replacements = {
        "Γ": "gamma",
        "γ": "gamma",
        "θ": "theta",
        "ω": "omega",
        "ψ": "psi",
        "∂": "partial",
        "²": "^2",
        "∞": "inf",
        "≤": "<=",
        "‖": "||",
        "̃": "",
    }
    for old, new in replacements.items():
        value = value.replace(old, new)
    return re.sub(r"[^a-z0-9_<>/=+*^.-]+", "", value.lower())


def bool_values_for_keys(payload: Any, *keys: str) -> list[bool]:
    wanted = {key.lower() for key in keys}
    values: list[bool] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if str(key).lower() in wanted and isinstance(value, bool):
                values.append(value)
    return values


def test_sprint134_writes_json_csv_and_markdown_outputs(tmp_path: Path) -> None:
    summary, rows, artifact_text, out_dir = run_correction_script(tmp_path)

    assert out_dir.name == STEM
    assert summary.get("contract", STEM) == STEM
    assert rows, artifact_text
    assert "axisymmetric" in artifact_text.lower()
    assert "swirl" in artifact_text.lower()


def test_sprint134_corrects_u1_equation_with_stretching_source(tmp_path: Path) -> None:
    summary, rows, artifact_text, _out_dir = run_correction_script(tmp_path)
    text = compact(joined_text(summary, rows, artifact_text))

    assert "u1" in text
    assert "stretching" in text or "source" in text
    assert (
        "2u1partial_zpsi1" in text
        or "2*u1*partial_zpsi1" in text
        or "2u1partialzpsi1" in text
        or "2*u1*partialzpsi1" in text
    ), artifact_text
    assert "nu" in text and ("ltildeu1" in text or "lu1" in text or "l_u1" in text)


def test_sprint134_omega1_equation_has_quadratic_source(tmp_path: Path) -> None:
    summary, rows, artifact_text, _out_dir = run_correction_script(tmp_path)
    text = compact(joined_text(summary, rows, artifact_text))

    assert "omega1" in text
    assert (
        "partial_z(u1^2)" in text
        or "partial_zu1^2" in text
        or "partialzu1^2" in text
        or "partial_zofu1^2" in text
        or "partial_z(u1*u1)" in text
    ), artifact_text
    assert "quadratic" in text or "u1^2" in text
    assert "nu" in text and ("ltildeomega1" in text or "lomega1" in text or "l_omega1" in text)


def test_sprint134_retracts_old_pure_u1_diffusion_claim(tmp_path: Path) -> None:
    summary, rows, artifact_text, _out_dir = run_correction_script(tmp_path)
    text = compact(joined_text(summary, rows, artifact_text))

    retraction_flags = bool_values_for_keys(
        [summary, rows],
        "old_u1_pure_diffusion_retracted",
        "old_pure_u1_diffusion_retracted",
        "pure_u1_diffusion_retracted",
        "u1_pure_diffusion_retracted",
    )
    false_pure_flags = bool_values_for_keys(
        [summary, rows],
        "u1_pure_diffusion",
        "pure_diffusion_u1",
        "u1_equation_pure_diffusion",
    )
    superseded_flags = bool_values_for_keys(
        [summary, rows],
        "pure_diffusion_u1_maximum_principle_superseded",
    )
    assert retraction_flags and all(retraction_flags), artifact_text
    assert (false_pure_flags and not any(false_pure_flags)) or (
        superseded_flags and all(superseded_flags)
    ), artifact_text
    assert "purediffusionu1maximumprinciple" in text or "pureu1diffusion" in text
    assert "retracted" in text or "false" in text


def test_sprint134_gamma_maximum_principle_and_boundary_annulus_bound(tmp_path: Path) -> None:
    summary, rows, artifact_text, _out_dir = run_correction_script(tmp_path)
    text = compact(joined_text(summary, rows, artifact_text))

    assert "gamma" in text
    assert "maximumprinciple" in text or "linf" in text
    assert "r*u" in text or "rutheta" in text or "r^2u1" in text or "r2u1" in text
    assert "boundaryannulus" in text or "r0" in text
    assert "r0^2" in text or "r02" in text
    assert "m0/r0^2" in text or "m0r0^2" in text or "m0/r02" in text


def test_sprint134_clay_flags_remain_false(tmp_path: Path) -> None:
    summary, rows, artifact_text, _out_dir = run_correction_script(tmp_path)

    full_clay_flags = bool_values_for_keys([summary, rows], "full_clay_ns_solved", "full_clay_solved")
    promotion_flags = bool_values_for_keys(
        [summary, rows],
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay_promoted",
    )
    assert full_clay_flags and all(value is False for value in full_clay_flags), artifact_text
    assert promotion_flags and all(value is False for value in promotion_flags), artifact_text
    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(artifact_text), pattern.pattern
