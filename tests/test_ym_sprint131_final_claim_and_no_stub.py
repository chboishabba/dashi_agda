from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint131_final_claim_audit.py"
SUMMARY_NAME = "ym_sprint131_final_claim_audit_summary.json"
REPORT_NAME = "ym_sprint131_final_claim_audit.md"

AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"
SPRINT = "131"
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
    r"(?m)^\s*import\s+(DASHI\.Physics\.Closure\.YMSprint131[A-Za-z0-9_.]*)\s*$"
)


def run_script(out_dir: Path) -> dict[str, Any]:
    assert SCRIPT.is_file(), f"missing audit script: {SCRIPT.relative_to(REPO_ROOT)}"
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
        candidates = sorted(out_dir.glob("*sprint131*final*claim*audit*.json"))
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


def bool_rows(summary: dict[str, Any], *terms: str) -> list[dict[str, Any]]:
    pattern = re.compile("|".join(re.escape(term) for term in terms), re.IGNORECASE)
    return [
        item
        for item in flatten_values(summary)
        if isinstance(item, dict)
        and any(isinstance(value, bool) for value in item.values())
        and pattern.search(json_text(item))
    ]


def internal_gate_rows(summary: dict[str, Any]) -> list[dict[str, Any]]:
    candidates = bool_rows(summary, "internal", "gate")
    return [
        row
        for row in candidates
        if not re.search(r"external|governance|acceptance|promotion|promoted", json_text(row), re.IGNORECASE)
    ]


def assert_all_internal_gates_true(summary: dict[str, Any]) -> None:
    rows = internal_gate_rows(summary)
    assert rows, "summary should expose internal gates"
    false_rows = [
        row
        for row in rows
        if any(isinstance(value, bool) and value is False for value in row.values())
    ]
    assert not false_rows, "internal gates should all be true:\n" + json_text(false_rows)
    assert any(
        any(value is True for value in row.values()) for row in rows
    ), "internal gate rows did not contain true booleans"


def assert_external_governance_absent(summary: dict[str, Any]) -> None:
    rows = bool_rows(summary, "external", "governance", "acceptance")
    assert rows, "summary should expose external governance/acceptance absence"
    assert all(
        not any(isinstance(value, bool) and value is True for value in row.values())
        for row in rows
    ), "external governance gates must be absent/false:\n" + json_text(rows)


def assert_promotion_false(text: str, summary: dict[str, Any]) -> None:
    rows = bool_rows(summary, "promotion", "promoted", "clay")
    assert rows, "summary should expose the promotion gate"
    assert all(
        not any(isinstance(value, bool) and value is True for value in row.values())
        for row in rows
    ), "promotion gate must remain false:\n" + json_text(rows)

    forbidden_patterns = (
        CLAY_PROMOTED_NAME + " = " + "tr" + "ue",
        CLAY_PROMOTED_NAME + '": ' + "tr" + "ue",
        CLAY_PROMOTED_NAME + ": " + "tr" + "ue",
    )
    for pattern in forbidden_patterns:
        assert pattern not in text


def sprint131_agda_files() -> list[Path]:
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


def everything_sprint131_imports() -> set[str]:
    assert EVERYTHING.is_file(), "missing DASHI/Everything.agda"
    return set(EVERYTHING_IMPORT.findall(read_text(EVERYTHING)))


def test_sprint131_final_claim_audit_internal_gates_pass_without_promotion(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    assert (out_dir / SUMMARY_NAME).exists() or sorted(
        out_dir.glob("*sprint131*final*claim*audit*.json")
    )
    assert (out_dir / REPORT_NAME).exists() or sorted(
        out_dir.glob("*sprint131*final*claim*audit*.md")
    )
    assert "Sprint 131" in text or "Sprint131" in text
    assert_all_internal_gates_true(summary)
    assert_external_governance_absent(summary)
    assert_promotion_false(text, summary)


def test_sprint131_agda_modules_have_no_stub_or_incomplete_surfaces() -> None:
    agda_files = sprint131_agda_files()
    assert agda_files, "no Sprint131 Agda modules found under DASHI/Physics/Closure"

    failures: list[str] = []
    for path in agda_files:
        text = read_text(path)
        for label, pattern in FORBIDDEN_PATTERNS.items():
            for match in pattern.finditer(text):
                failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")
        for line, datatype in empty_datatypes(text):
            failures.append(f"{relative(path)}:{line}: empty datatype {datatype!r}")

    assert not failures, "Forbidden Sprint131 Agda surface markers found:\n" + "\n".join(failures)


def test_everything_imports_all_sprint131_modules() -> None:
    agda_files = sprint131_agda_files()
    assert agda_files, "no Sprint131 Agda modules found under DASHI/Physics/Closure"

    imports = everything_sprint131_imports()
    expected = {"DASHI.Physics.Closure." + path.stem for path in agda_files}

    extra = sorted(imports - expected)
    assert not extra, "DASHI/Everything.agda imports unknown Sprint131 modules: " + ", ".join(extra)

    missing = sorted(expected - imports)
    assert not missing, "DASHI/Everything.agda is missing Sprint131 imports: " + ", ".join(missing)
