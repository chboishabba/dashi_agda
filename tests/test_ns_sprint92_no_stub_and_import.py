from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "92"

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_TODO = "TO" + "DO"
TOKEN_STUB = "st" + "ub"
TOKEN_PLACEHOLDER = "place" + "holder"
TOKEN_FUTURE_PROOF = "future" + r"\s+" + "proof"

FORBIDDEN_PATTERNS = {
    "unproved axiom marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_POSTULATE + r"(?![A-Za-z0-9_])"
    ),
    "open work marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_TODO + r"(?![A-Za-z0-9_])"
    ),
    "stub wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_STUB + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "placeholder wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_PLACEHOLDER + r"s?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "future proof phrasing": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_FUTURE_PROOF + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "Agda hole start": re.compile(r"\{!"),
    "Agda hole end": re.compile(r"!\}"),
}

CANONICAL_BOUNDARY = "canonicalNSSprint92MovingKStarLocalizationBoundary"

EXPECTED_FALSE_EXPORTS = {
    "Clay promotion": "clayNavierStokesPromoted",
    "moving boundary theorem": "movingInTimeKStarLocalizationBoundaryClosed",
    "dominance": "dangerShellDissipationDominatesInfluxClosed",
    "pointwise": "pointwiseTailFromLocalDissipationClosed",
    "high-high": "highHighDominanceClosed",
    "independent coefficient": "independentCoefficientBudgetClosed",
}


def sprint92_ns_agda_files() -> list[Path]:
    return sorted(AGDA_DIR.glob("NSSprint" + SPRINT + "*.agda"))


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def relative(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def agda_module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO_ROOT).with_suffix("").parts)


def require_single_sprint92_ns_agda_module() -> Path:
    modules = sprint92_ns_agda_files()
    assert modules, (
        "missing Sprint 92 NS Agda module under "
        "DASHI/Physics/Closure/NSSprint92*.agda"
    )
    assert len(modules) == 1, (
        "expected exactly one Sprint 92 NS Agda module, found: "
        + ", ".join(relative(path) for path in modules)
    )
    return modules[0]


def bool_export_pattern(export: str, value: bool) -> re.Pattern[str]:
    agda_bool = "true" if value else "false"
    return re.compile(
        r"(?<![A-Za-z0-9_])"
        + re.escape(export)
        + r"(?![A-Za-z0-9_])"
        + r"(?:\s*:\s*[^\n=]+)?\s*=\s*"
        + agda_bool
        + r"(?![A-Za-z0-9_])",
        re.MULTILINE,
    )


def test_sprint92_ns_agda_module_exists_exactly_once_and_has_no_incomplete_markers() -> None:
    path = require_single_sprint92_ns_agda_module()
    text = read_text(path)

    failures: list[str] = []
    for label, pattern in FORBIDDEN_PATTERNS.items():
        for match in pattern.finditer(text):
            failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")

    assert not failures, "Forbidden Sprint 92 NS Agda surface:\n" + "\n".join(failures)


def test_sprint92_ns_agda_module_contains_canonical_boundary_export() -> None:
    path = require_single_sprint92_ns_agda_module()
    text = read_text(path)

    assert re.search(
        r"(?<![A-Za-z0-9_])" + re.escape(CANONICAL_BOUNDARY) + r"(?![A-Za-z0-9_])",
        text,
    ), relative(path) + " is missing " + CANONICAL_BOUNDARY


def test_sprint92_ns_agda_module_exports_fail_closed_gates() -> None:
    path = require_single_sprint92_ns_agda_module()
    text = read_text(path)

    missing: list[str] = []
    for label, export in EXPECTED_FALSE_EXPORTS.items():
        if not bool_export_pattern(export, False).search(text):
            missing.append(label + " gate: " + export + " = false")

    assert not missing, relative(path) + " is missing fail-closed gates:\n" + "\n".join(missing)


def test_everything_imports_sprint92_ns_agda_module() -> None:
    path = require_single_sprint92_ns_agda_module()
    module = agda_module_name(path)
    everything = read_text(EVERYTHING)

    assert re.search(
        r"^\s*import\s+" + re.escape(module) + r"\s*$",
        everything,
        re.MULTILINE,
    ), "DASHI/Everything.agda is missing import: " + module
