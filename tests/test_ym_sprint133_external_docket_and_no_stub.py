from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint133_external_review_docket.py"
SUMMARY_NAME = "ym_sprint133_external_review_docket_summary.json"
REPORT_NAME = "ym_sprint133_external_review_docket.md"

AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"
SPRINT = "133"
AGDA_PREFIX = "YMSprint" + SPRINT

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_TODO = "TO" + "DO"
TOKEN_STUB = "st" + "ub"
TOKEN_SKELETON = "skele" + "ton"
TOKEN_DUMMY = "dum" + "my"
TOKEN_FUTURE_PROOF = "future" + r"[\s-]*" + "proof"
TOKEN_HOLE = "ho" + "le"
CLAY_PROMOTED_NAME = "clay" + "Yang" + "Mills" + "Promoted"

FORBIDDEN_PATTERNS = {
    "unproved axiom marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_POSTULATE + r"(?![A-Za-z0-9_])"
    ),
    "open work marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_TODO + r"(?![A-Za-z0-9_])"
    ),
    "placeholder wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_STUB + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "bare scaffold wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_SKELETON + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "dummy wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_DUMMY + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "deferred proof wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_FUTURE_PROOF + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "hole wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_HOLE + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "Agda hole braces": re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}")),
}

DATA_DECL = re.compile(r"^\s*data\s+([A-Za-z][A-Za-z0-9_'-]*)\b")
EVERYTHING_IMPORT = re.compile(
    r"(?m)^\s*import\s+(DASHI\.Physics\.Closure\.YMSprint133[A-Za-z0-9_.]*)\s*$"
)


def run_script(out_dir: Path) -> dict[str, Any]:
    assert SCRIPT.is_file(), f"missing docket script: {SCRIPT.relative_to(REPO_ROOT)}"
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
    assert result.returncode in (0, 1), result.stdout + result.stderr

    summary_path = out_dir / SUMMARY_NAME
    if not summary_path.exists():
        candidates = sorted(out_dir.glob("*sprint133*external*review*docket*.json"))
        assert candidates, result.stdout + result.stderr
        summary_path = candidates[0]
    return json.loads(summary_path.read_text(encoding="utf-8"))


def flatten_values(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [
            nested for item in value.values() for nested in flatten_values(item)
        ]
    if isinstance(value, list):
        return [value] + [nested for item in value for nested in flatten_values(item)]
    return [value]


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def output_text(out_dir: Path, summary: dict[str, Any]) -> str:
    parts = [json_text(summary)]
    for path in sorted(out_dir.glob("*")):
        if path.suffix.lower() in {".json", ".md", ".markdown", ".txt"}:
            parts.append(path.read_text(encoding="utf-8"))
    return "\n".join(parts)


def dict_rows(summary: dict[str, Any], *terms: str) -> list[dict[str, Any]]:
    pattern = re.compile("|".join(re.escape(term) for term in terms), re.IGNORECASE)
    return [
        item
        for item in flatten_values(summary)
        if isinstance(item, dict) and pattern.search(json_text(item))
    ]


def bool_rows(summary: dict[str, Any], *terms: str) -> list[dict[str, Any]]:
    return [
        item
        for item in dict_rows(summary, *terms)
        if any(isinstance(value, bool) for value in item.values())
    ]


def looks_resolved(row: dict[str, Any]) -> bool:
    lowered = {str(key).lower(): value for key, value in row.items()}
    for key in ("resolved", "closed", "discharged", "passed", "satisfied"):
        if lowered.get(key) is True:
            return True
    status = str(lowered.get("status", "")).lower()
    return status in {"resolved", "closed", "discharged", "pass", "passed", "satisfied"}


def assert_external_rows_are_concrete_present_false(summary: dict[str, Any]) -> None:
    rows = [
        row
        for row in dict_rows(summary, "external")
        if "present" in {str(key).lower() for key in row}
    ]
    assert rows, "docket summary should expose concrete external rows"

    failures: list[dict[str, Any]] = []
    for row in rows:
        lowered = {str(key).lower(): value for key, value in row.items()}
        if lowered.get("present") is not False or "state" in lowered:
            failures.append(row)
    assert not failures, "external rows must use present=false and omit state:\n" + json_text(failures)


def assert_required_resolutions_are_closed(summary: dict[str, Any]) -> None:
    rows = [
        row
        for row in dict_rows(summary, "required", "resolution")
        if re.search(r"required|must|resolution|resolved", json_text(row), re.IGNORECASE)
    ]
    assert rows, "docket summary should expose required resolution rows"
    unresolved = [row for row in rows if not looks_resolved(row)]
    assert not unresolved, "required resolutions should be closed:\n" + json_text(unresolved)


def assert_no_promotion_true(text: str, summary: dict[str, Any]) -> None:
    rows = bool_rows(summary, "promotion", "promoted", "clay")
    assert rows, "summary should expose the promotion gate"
    true_rows = [
        row
        for row in rows
        if any(isinstance(value, bool) and value is True for value in row.values())
    ]
    assert not true_rows, "promotion booleans must not be true:\n" + json_text(true_rows)

    forbidden_patterns = (
        CLAY_PROMOTED_NAME + " = " + "tr" + "ue",
        CLAY_PROMOTED_NAME + '": ' + "tr" + "ue",
        CLAY_PROMOTED_NAME + ": " + "tr" + "ue",
        '"promotion": ' + "tr" + "ue",
        '"promoted": ' + "tr" + "ue",
    )
    for pattern in forbidden_patterns:
        assert pattern not in text


def sprint133_agda_files() -> list[Path]:
    return sorted(path for path in AGDA_DIR.glob(AGDA_PREFIX + "*.agda") if path.is_file())


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def empty_datatypes(text: str) -> Iterable[tuple[int, str]]:
    lines = text.splitlines()
    index = 0
    while index < len(lines):
        match = DATA_DECL.match(lines[index])
        if not match:
            index += 1
            continue

        start = index
        name = match.group(1)
        saw_where = " where" in lines[index] or lines[index].rstrip().endswith("where")
        index += 1
        has_constructor = False
        while index < len(lines):
            stripped = lines[index].strip()
            indented = lines[index].startswith((" ", "\t"))
            if not stripped:
                index += 1
                continue
            if not indented:
                break
            if stripped == "where":
                saw_where = True
            elif saw_where and not stripped.startswith("--"):
                has_constructor = True
                break
            index += 1

        if saw_where and not has_constructor:
            yield start + 1, name


def everything_sprint133_imports() -> set[str]:
    assert EVERYTHING.is_file(), "missing DASHI/Everything.agda"
    return set(EVERYTHING_IMPORT.findall(read_text(EVERYTHING)))


def test_sprint133_external_review_docket_outputs_and_gates(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    assert (out_dir / SUMMARY_NAME).exists() or sorted(
        out_dir.glob("*sprint133*external*review*docket*.json")
    )
    assert (out_dir / REPORT_NAME).exists() or sorted(
        out_dir.glob("*sprint133*external*review*docket*.md")
    )
    assert "Sprint 133" in text or "Sprint133" in text
    assert "docket" in text.lower()
    assert_external_rows_are_concrete_present_false(summary)
    assert_required_resolutions_are_closed(summary)
    assert_no_promotion_true(text, summary)


def test_sprint133_agda_modules_have_no_stub_or_incomplete_surfaces() -> None:
    agda_files = sprint133_agda_files()
    assert agda_files, "no Sprint133 Agda modules found under DASHI/Physics/Closure"

    failures: list[str] = []
    for path in agda_files:
        text = read_text(path)
        for label, pattern in FORBIDDEN_PATTERNS.items():
            for match in pattern.finditer(text):
                failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")
        for line, datatype in empty_datatypes(text):
            failures.append(f"{relative(path)}:{line}: empty datatype {datatype!r}")

    assert not failures, "Forbidden Sprint133 Agda surface markers found:\n" + "\n".join(failures)


def test_everything_imports_all_present_sprint133_modules() -> None:
    agda_files = sprint133_agda_files()
    assert agda_files, "no Sprint133 Agda modules found under DASHI/Physics/Closure"

    imports = everything_sprint133_imports()
    expected = {"DASHI.Physics.Closure." + path.stem for path in agda_files}

    extra = sorted(imports - expected)
    assert not extra, "DASHI/Everything.agda imports unknown Sprint133 modules: " + ", ".join(extra)

    missing = sorted(expected - imports)
    assert not missing, "DASHI/Everything.agda is missing Sprint133 imports: " + ", ".join(missing)
