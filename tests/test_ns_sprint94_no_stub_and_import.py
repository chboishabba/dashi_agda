from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "94"

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_TODO = "TO" + "DO"
TOKEN_STUB = "st" + "ub"
TOKEN_ADMIT = "ad" + "mit"
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
    "admit wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_ADMIT + r"(?:ted|s)?(?![A-Za-z0-9_])",
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

REQUIRED_ANCHORS = (
    "KStarLowerBoundHypothesis",
    "GlobalRegularityUnderKStarLowerBound",
    "GeneralDataKStarLowerBoundObstruction",
    "OptionABlocked",
    "OptionBOpen",
    "OptionCConditional",
)

CANONICAL_RECEIPT_PATTERN = re.compile(
    r"(?<![A-Za-z0-9_])canonical[A-Za-z0-9_]*Receipt(?![A-Za-z0-9_])"
)

CLAY_PROMOTED_TRUE_PATTERN = re.compile(
    r"(?<![A-Za-z0-9_])"
    r"clayNavierStokesPromoted"
    r"(?![A-Za-z0-9_])"
    r"(?:\s*:\s*[^\n=]+)?\s*=\s*true(?![A-Za-z0-9_])",
    re.MULTILINE,
)


def sprint94_ns_agda_files() -> list[Path]:
    return sorted(AGDA_DIR.glob("NSSprint" + SPRINT + "*.agda"))


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def relative(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def agda_module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO_ROOT).with_suffix("").parts)


def require_single_sprint94_ns_agda_module() -> Path:
    modules = sprint94_ns_agda_files()
    assert modules, (
        "missing Sprint 94 NS Agda module under "
        "DASHI/Physics/Closure/NSSprint94*.agda"
    )
    assert len(modules) == 1, (
        "expected exactly one Sprint 94 NS Agda module, found: "
        + ", ".join(relative(path) for path in modules)
    )
    return modules[0]


def identifier_pattern(identifier: str) -> re.Pattern[str]:
    return re.compile(
        r"(?<![A-Za-z0-9_])" + re.escape(identifier) + r"(?![A-Za-z0-9_])"
    )


def test_sprint94_ns_agda_module_exists_exactly_once_and_has_no_incomplete_markers() -> None:
    path = require_single_sprint94_ns_agda_module()
    text = read_text(path)

    failures: list[str] = []
    for label, pattern in FORBIDDEN_PATTERNS.items():
        for match in pattern.finditer(text):
            failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")

    assert not failures, "Forbidden Sprint 94 NS Agda surface:\n" + "\n".join(failures)


def test_sprint94_ns_agda_module_contains_required_kstar_anchors() -> None:
    path = require_single_sprint94_ns_agda_module()
    text = read_text(path)

    missing = [
        anchor for anchor in REQUIRED_ANCHORS if not identifier_pattern(anchor).search(text)
    ]
    if not CANONICAL_RECEIPT_PATTERN.search(text):
        missing.append("canonical*Receipt")

    assert not missing, relative(path) + " is missing Sprint 94 anchors:\n" + "\n".join(missing)


def test_sprint94_ns_agda_module_does_not_promote_clay_navier_stokes() -> None:
    path = require_single_sprint94_ns_agda_module()
    text = read_text(path)

    match = CLAY_PROMOTED_TRUE_PATTERN.search(text)
    assert match is None, (
        f"{relative(path)}:{line_for_offset(text, match.start())}: "
        "clayNavierStokesPromoted must not be true"
    )


def test_everything_imports_sprint94_ns_agda_module() -> None:
    path = require_single_sprint94_ns_agda_module()
    module = agda_module_name(path)
    everything = read_text(EVERYTHING)

    assert re.search(
        r"^\s*import\s+" + re.escape(module) + r"\s*$",
        everything,
        re.MULTILINE,
    ), "DASHI/Everything.agda is missing import: " + module
