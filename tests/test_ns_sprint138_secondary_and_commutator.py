from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
SECONDARY_STEM = "ns_sprint138_secondary_peak_exclusion"
COMMUTATOR_STEM = "ns_sprint138_transport_commutator_budget"

CLAY_TRUE_PATTERNS = (
    re.compile(r'"clay[^"]*"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bclay[A-Za-z0-9_]*\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_sprint_script(tmp_path: Path, stem: str) -> tuple[list[Any], str, Path]:
    script = REPO_ROOT / "scripts" / f"{stem}.py"
    assert script.is_file(), "missing " + str(script.relative_to(REPO_ROOT))

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

    artifact_paths = sorted(
        path
        for path in out_dir.glob("*")
        if path.suffix.lower() in {".json", ".csv", ".md", ".txt"}
    ) if out_dir.exists() else []
    artifact_text = "\n".join(
        [result.stdout, result.stderr]
        + [path.read_text(encoding="utf-8", errors="replace") for path in artifact_paths]
    )

    assert result.returncode == 0, artifact_text
    assert out_dir.is_dir(), artifact_text
    assert any(path.suffix.lower() == ".json" for path in artifact_paths), artifact_text
    assert any(path.suffix.lower() == ".md" for path in artifact_paths), artifact_text
    assert all(path.stat().st_size > 0 for path in artifact_paths), artifact_text

    payloads = [
        json.loads(path.read_text(encoding="utf-8"))
        for path in artifact_paths
        if path.suffix.lower() == ".json"
    ]
    assert payloads, artifact_text
    return payloads, artifact_text, out_dir


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def normalize(value: Any) -> str:
    text = str(value)
    replacements = {
        "Γ": "gamma",
        "γ": "gamma",
        "∂": "partial",
        "ᵣ": "r",
        "ᶻ": "z",
        "¹": "1",
        "²": "2",
        "^": " ",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    return re.sub(r"[^a-z0-9]+", " ", text.lower()).strip()


def compact(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "_", normalize(value)).strip("_")


def joined_text(*payloads: Any) -> str:
    return "\n".join(
        payload if isinstance(payload, str) else json.dumps(payload, sort_keys=True, default=str)
        for payload in payloads
    )


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


def rows_mentioning(payload: Any, *terms: str) -> list[dict[str, Any]]:
    wanted = tuple(normalize(term) for term in terms)
    rows: list[dict[str, Any]] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        text = normalize(json.dumps(item, sort_keys=True, default=str))
        if all(term in text for term in wanted):
            rows.append(item)
    return rows


def assert_text_has_all(text: str, *terms: str) -> None:
    haystack = normalize(text)
    missing = [term for term in terms if normalize(term) not in haystack]
    assert not missing, f"missing terms {missing} in:\n{text}"


def assert_claim_closed_and_proved_false(payloads: list[Any], text: str, claim: str) -> None:
    rows = rows_mentioning(payloads, claim)
    rows_text = joined_text(rows)
    assert rows, f"missing rows for {claim}\n{text}"

    assert rows_mentioning(rows, claim, "closed", "false") or bool_values_for_keys(
        rows,
        f"{compact(claim)}_closed",
        "closed",
        "is_closed",
        "claim_closed",
    ) == [False], rows_text
    assert rows_mentioning(rows, claim, "proved", "false") or rows_mentioning(
        rows, claim, "proven", "false"
    ) or bool_values_for_keys(
        rows,
        f"{compact(claim)}_proved",
        f"{compact(claim)}_proven",
        "proved",
        "proven",
        "is_proved",
        "is_proven",
    ) == [False], rows_text


def assert_blocker_open(payloads: list[Any], text: str, *terms: str) -> None:
    blocker_rows = rows_mentioning(payloads, "blocker", *terms)
    blocker_text = normalize(joined_text(blocker_rows, text))
    assert blocker_rows, f"missing blocker rows for {terms}\n{text}"
    assert any(term in blocker_text for term in ("open", "blocked", "gap", "unresolved")), blocker_text


def assert_clay_not_solved_or_promoted(payloads: list[Any], text: str) -> None:
    full_clay_flags = bool_values_for_keys(payloads, "full_clay_ns_solved", "full_clay_solved")
    promotion_flags = bool_values_for_keys(
        payloads,
        "clayNavierStokesPromoted",
        "clay_navier_stokes_promoted",
        "clay_promoted",
    )
    assert full_clay_flags and all(value is False for value in full_clay_flags), joined_text(payloads)
    assert promotion_flags and all(value is False for value in promotion_flags), joined_text(payloads)
    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_sprint138_secondary_peak_exclusion_records_open_blocked_claim(
    tmp_path: Path,
) -> None:
    payloads, text, out_dir = run_sprint_script(tmp_path, SECONDARY_STEM)
    combined = joined_text(payloads, text)

    assert out_dir.name == SECONDARY_STEM
    assert_text_has_all(
        combined,
        "secondary peak exclusion",
        "single peak",
        "parabolic",
        "nonlinear shoulder",
        "gamma",
        "Sturmian",
    )
    assert_claim_closed_and_proved_false(payloads, text, "secondary peak exclusion")
    assert_blocker_open(payloads, text, "secondary peak")
    assert_clay_not_solved_or_promoted(payloads, text)


def test_sprint138_transport_commutator_records_open_blocked_claim(
    tmp_path: Path,
) -> None:
    payloads, text, out_dir = run_sprint_script(tmp_path, COMMUTATOR_STEM)
    combined = joined_text(payloads, text)

    assert out_dir.name == COMMUTATOR_STEM
    assert_text_has_all(
        combined,
        "commutator domination",
        "transport commutator equation",
        "partial z u r",
        "partial r u1",
        "log Biot Savart",
        "domination",
    )
    assert_claim_closed_and_proved_false(payloads, text, "commutator domination")
    assert_blocker_open(payloads, text, "commutator")
    assert_clay_not_solved_or_promoted(payloads, text)
