from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS_DIR = REPO_ROOT / "scripts"
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"

SPRINT = "124"

FORBIDDEN_SOURCE_PATTERNS = {
    "postulate": re.compile(r"(?<![A-Za-z0-9_])postulate(?![A-Za-z0-9_])"),
    "TODO": re.compile(r"(?<![A-Za-z0-9_])TODO(?![A-Za-z0-9_])"),
    "stub": re.compile(r"(?<![A-Za-z0-9_])stub(?![A-Za-z0-9_])", re.IGNORECASE),
    "skeleton": re.compile(r"(?<![A-Za-z0-9_])skeletons?(?![A-Za-z0-9_])", re.IGNORECASE),
    "admit": re.compile(r"(?<![A-Za-z0-9_])admits?|admitted(?![A-Za-z0-9_])", re.IGNORECASE),
    "dummy": re.compile(r"(?<![A-Za-z0-9_])dummy(?![A-Za-z0-9_])", re.IGNORECASE),
    "future-proof": re.compile(r"(?<![A-Za-z0-9_])future-proof(?:ed|ing)?(?![A-Za-z0-9_])", re.IGNORECASE),
    "hole": re.compile(r"(?<![A-Za-z0-9_])holes?(?![A-Za-z0-9_])", re.IGNORECASE),
    "agda-hole-open": re.compile(r"\{!"),
    "agda-hole-close": re.compile(r"!\}"),
    "agda-query-hole": re.compile(r"=\s*\?(?![A-Za-z0-9_])"),
}


def sprint124_scripts() -> list[Path]:
    return sorted(SCRIPTS_DIR.glob("ns_sprint124*.py"))


def sprint124_agda_files() -> list[Path]:
    return sorted(AGDA_DIR.glob("NSSprint124*.agda"))


def run_script(script: Path, out_dir: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(script), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )


def artifact_paths(out_dir: Path) -> tuple[list[Path], list[Path], list[Path]]:
    return (
        sorted(out_dir.glob("*.json")),
        sorted(out_dir.glob("*.csv")),
        sorted(out_dir.glob("*.md")),
    )


def load_json(paths: list[Path]) -> list[Any]:
    return [json.loads(path.read_text(encoding="utf-8")) for path in paths]


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for nested in value.values() for item in flatten(nested)]
    if isinstance(value, list):
        return [value] + [item for nested in value for item in flatten(nested)]
    return [value]


def normalize_key(key: str) -> str:
    return "".join(ch for ch in key.lower() if ch.isalnum())


def boolish(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return value != 0
    if isinstance(value, str):
        lowered = value.strip().replace("_", "-").lower()
        if lowered in {"true", "1", "yes", "closed", "met", "established", "pass", "passed"}:
            return True
        if lowered in {"false", "0", "no", "open", "blocked", "unmet", "hold", "fail", "failed"}:
            return False
    return None


def boolean_values_for_keys(payloads: list[Any], *names: str) -> list[bool]:
    normalized_names = {normalize_key(name) for name in names}
    matches: list[bool] = []
    for item in flatten(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize_key(str(key)) not in normalized_names or isinstance(value, (dict, list)):
                continue
            parsed = boolish(value)
            if parsed is not None:
                matches.append(parsed)
    return matches


def assert_any_true(payloads: list[Any], *names: str) -> None:
    values = boolean_values_for_keys(payloads, *names)
    assert values, f"missing boolean-like field for {names}"
    assert any(value is True for value in values), values


def assert_all_false(payloads: list[Any], *names: str) -> None:
    values = boolean_values_for_keys(payloads, *names)
    assert values, f"missing boolean-like field for {names}"
    assert not any(values), values


def assert_route_closed(payloads: list[Any], *terms: str) -> None:
    normalized_terms = [normalize_key(term) for term in terms]
    for item in flatten(payloads):
        if not isinstance(item, dict):
            continue
        row_text = normalize_key(json.dumps(item, sort_keys=True))
        if not all(term in row_text for term in normalized_terms):
            continue
        classification = str(item.get("classification", "")).lower()
        complete = boolish(item.get("complete"))
        closed = boolish(
            item.get("closed", item.get("route_closed", item.get("routeClosed")))
        )
        if "closed" in classification or complete is True or closed is True:
            return
    assert False, f"missing closed route record containing {terms}"


def combined_output_text(json_paths: list[Path], md_paths: list[Path]) -> str:
    parts = [path.read_text(encoding="utf-8") for path in json_paths + md_paths]
    return "\n".join(parts)


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def forbidden_source_hits(paths: list[Path]) -> list[str]:
    hits: list[str] = []
    for path in paths:
        text = path.read_text(encoding="utf-8", errors="replace")
        for label, pattern in FORBIDDEN_SOURCE_PATTERNS.items():
            for match in pattern.finditer(text):
                hits.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")
    return hits


def test_sprint124_worker2_worker3_scripts_run_and_emit_json_markdown(
    tmp_path: Path,
) -> None:
    scripts = sprint124_scripts()
    assert len(scripts) >= 2, "Worker 2/3 Sprint 124 scripts are missing"

    all_payloads: list[Any] = []
    all_json_paths: list[Path] = []
    all_md_paths: list[Path] = []
    csv_seen = False
    for script in scripts:
        out_dir = tmp_path / script.stem
        result = run_script(script, out_dir)
        assert result.returncode in {0, 1}, result.stdout + result.stderr

        json_paths, csv_paths, md_paths = artifact_paths(out_dir)
        assert json_paths, f"{script.name} did not write JSON output"
        assert md_paths, f"{script.name} did not write Markdown output"
        csv_seen = csv_seen or bool(csv_paths)
        all_payloads.extend(load_json(json_paths))
        all_json_paths.extend(json_paths)
        all_md_paths.extend(md_paths)

    assert csv_seen, "at least one Worker 2/3 sampler script should emit CSV rows"
    text = combined_output_text(all_json_paths, all_md_paths)
    assert re.search(r"favorable[ _-]?dwell", text, re.IGNORECASE), text
    assert re.search(r"zero[ _-]?mean[ _-]?flux", text, re.IGNORECASE), text
    assert re.search(r"rotating[\s\S]{0,120}route", text, re.IGNORECASE), text

    assert re.search(r"favorable[\s\S]{0,200}closed", text, re.IGNORECASE), text
    assert_route_closed(all_payloads, "favorable")
    assert_any_true(
        all_payloads,
        "zero_mean_flux_established",
        "zeroMeanFluxEstablished",
        "mean_flux_zero_established",
        "meanFluxZeroEstablished",
        "zero_mean_flux",
        "zeroMeanFlux",
    )
    assert_any_true(
        all_payloads,
        "rotating_route_closed",
        "rotatingRouteClosed",
        "route_closed",
        "routeClosed",
        "rotating_strain_blowup_route_closed",
        "rotatingStrainBlowupRouteClosed",
    )
    assert_all_false(
        all_payloads,
        "clay",
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay_promoted",
        "clayPromoted",
    )


def test_sprint124_agda_and_scripts_have_no_forbidden_markers() -> None:
    scripts = sprint124_scripts()
    agda_files = sprint124_agda_files()
    assert scripts, "Sprint 124 scripts are missing"
    assert agda_files, "Sprint 124 Agda receipt is missing"

    hits = forbidden_source_hits([*scripts, *agda_files])
    assert hits == []
