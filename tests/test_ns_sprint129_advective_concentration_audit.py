from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS_DIR = REPO_ROOT / "scripts"

PDE_FACTS = (
    "pure_diffusion_u1",
    "omega1_source_term",
    "no_log_axisymmetric_biot_savart",
)
PRIMARY_OPEN_GATE = "AdvectiveConcentrationVsDiffusionBound"


def sprint129_audit_script() -> Path:
    candidates = sorted(SCRIPTS_DIR.glob("ns_sprint129*advective*concentration*audit*.py"))
    if not candidates:
        candidates = sorted(SCRIPTS_DIR.glob("*sprint129*advective*concentration*audit*.py"))
    assert candidates, (
        "missing Sprint 129 advective concentration audit script among "
        f"{[path.name for path in sorted(SCRIPTS_DIR.glob('*sprint129*.py'))]}"
    )
    assert len(candidates) == 1, (
        "ambiguous Sprint 129 advective concentration audit scripts: "
        f"{[path.name for path in candidates]}"
    )
    return candidates[0]


def run_script(script: Path, out_dir: Path, tmp_path: Path) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["TMPDIR"] = str(tmp_path)
    return subprocess.run(
        [sys.executable, str(script), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
        env=env,
    )


def artifact_paths(out_dir: Path) -> tuple[list[Path], list[Path]]:
    return (
        sorted(out_dir.glob("*.json")),
        sorted(path for path in out_dir.glob("*") if path.suffix.lower() in {".md", ".markdown"}),
    )


def load_json(paths: list[Path]) -> list[Any]:
    return [json.loads(path.read_text(encoding="utf-8")) for path in paths]


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for nested in value.values() for item in flatten(nested)]
    if isinstance(value, list):
        return [value] + [item for nested in value for item in flatten(nested)]
    return [value]


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def output_text(out_dir: Path, payloads: list[Any]) -> str:
    parts = [json_text(payloads)]
    for path in sorted(out_dir.glob("*")):
        if path.suffix.lower() in {".json", ".md", ".markdown", ".txt"}:
            parts.append(path.read_text(encoding="utf-8"))
    return "\n".join(parts)


def normalize_key(key: str) -> str:
    return "".join(ch for ch in key.lower() if ch.isalnum())


def boolish(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return value != 0
    if isinstance(value, str):
        lowered = value.strip().replace("_", "-").lower()
        if lowered in {"true", "1", "yes", "pass", "passed", "closed", "promoted"}:
            return True
        if lowered in {"false", "0", "no", "fail", "failed", "open", "blocked", "hold"}:
            return False
    return None


def scalar_values(payloads: list[Any], *names: str) -> list[Any]:
    wanted = {normalize_key(name) for name in names}
    values: list[Any] = []
    for item in flatten(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize_key(str(key)) in wanted and not isinstance(value, (dict, list)):
                values.append(value)
    return values


def entries_containing(payloads: list[Any], *terms: str) -> list[dict[str, Any]]:
    lowered_terms = tuple(term.lower() for term in terms)
    return [
        item
        for item in flatten(payloads)
        if isinstance(item, dict)
        and all(term in json_text(item).lower() for term in lowered_terms)
    ]


def assert_terms_present(text: str, terms: tuple[str, ...], label: str) -> None:
    missing = [term for term in terms if term not in text]
    assert not missing, f"missing {label}: {missing}"


def assert_feasibility_window_records_alpha_beta(payloads: list[Any], text: str) -> None:
    rows = entries_containing(payloads, "feasibility", "alpha", "beta")
    rows += entries_containing(payloads, "window", "alpha", "beta")
    assert rows or (
        re.search(r"\bfeasibility[-_ ]?window\b", text, re.IGNORECASE)
        and re.search(r"\balpha\b", text, re.IGNORECASE)
        and re.search(r"\bbeta\b", text, re.IGNORECASE)
    ), "missing feasibility window with alpha/beta"


def assert_primary_gate_is_open(payloads: list[Any], text: str) -> None:
    assert PRIMARY_OPEN_GATE in text, f"missing primary gate {PRIMARY_OPEN_GATE}"
    entries = entries_containing(payloads, PRIMARY_OPEN_GATE)
    assert entries, f"missing JSON entry for primary gate {PRIMARY_OPEN_GATE}"
    assert any(
        item.get("open") is True
        or item.get("blocked") is True
        or item.get("closed") is False
        or item.get("passed") is False
        or item.get("value") is False
        or re.search(r"\b(open|blocked|fail[-_ ]?closed|false)\b", json_text(item), re.IGNORECASE)
        for item in entries
    ), f"{PRIMARY_OPEN_GATE} is not recorded as open"


def assert_clay_promotion_false(payloads: list[Any], text: str) -> None:
    values = [
        boolish(value)
        for value in scalar_values(
            payloads,
            "clay_navier_stokes_promoted",
            "clayNavierStokesPromoted",
            "clay_promoted",
            "clayPromoted",
        )
        if boolish(value) is not None
    ]
    assert values, "missing clay_navier_stokes_promoted false record"
    assert values[-1] is False, values
    forbidden = (
        r'"clay_navier_stokes_promoted"\s*:\s*true',
        r'"clayNavierStokesPromoted"\s*:\s*true',
        r"\bclay_navier_stokes_promoted\b\s*[:=]\s*true\b",
    )
    for pattern in forbidden:
        assert not re.search(pattern, text, re.IGNORECASE), pattern


def test_sprint129_advective_concentration_audit_script_exists() -> None:
    assert sprint129_audit_script().exists()


def test_sprint129_advective_concentration_audit_cli_writes_outputs_and_exits_one(
    tmp_path: Path,
) -> None:
    script = sprint129_audit_script()
    out_dir = tmp_path / script.stem
    result = run_script(script, out_dir, tmp_path)

    json_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "audit did not write JSON output"
    assert md_paths, "audit did not write Markdown output"
    assert result.returncode == 1, result.stdout + result.stderr


def test_sprint129_advective_concentration_audit_records_pde_facts_and_window(
    tmp_path: Path,
) -> None:
    script = sprint129_audit_script()
    out_dir = tmp_path / script.stem
    result = run_script(script, out_dir, tmp_path)
    assert result.returncode == 1, result.stdout + result.stderr

    json_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "audit did not write JSON output"
    assert md_paths, "audit did not write Markdown output"
    payloads = load_json(json_paths)
    text = output_text(out_dir, payloads)

    assert_terms_present(text, PDE_FACTS, "PDE facts")
    assert_feasibility_window_records_alpha_beta(payloads, text)


def test_sprint129_advective_concentration_audit_records_open_gate_and_no_clay_promotion(
    tmp_path: Path,
) -> None:
    script = sprint129_audit_script()
    out_dir = tmp_path / script.stem
    result = run_script(script, out_dir, tmp_path)
    assert result.returncode == 1, result.stdout + result.stderr

    json_paths, md_paths = artifact_paths(out_dir)
    assert json_paths, "audit did not write JSON output"
    assert md_paths, "audit did not write Markdown output"
    payloads = load_json(json_paths)
    text = output_text(out_dir, payloads)

    assert_primary_gate_is_open(payloads, text)
    assert_clay_promotion_false(payloads, text)
