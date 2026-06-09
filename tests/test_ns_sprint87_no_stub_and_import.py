from __future__ import annotations

import re
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
SCRIPTS_DIR = REPO_ROOT / "scripts"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "87"
AGDA_PREFIXES = ("NSSprint" + SPRINT, "YMSprint" + SPRINT)
SCRIPT_GLOBS = (
    "ns_sprint" + SPRINT + "_*.py",
    "ym_sprint" + SPRINT + "_*.py",
    "clay_sprint" + SPRINT + "_*.py",
)

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_TODO = "TO" + "DO"
TOKEN_STUB = "st" + "ub"
TOKEN_SKELETON = "skele" + "ton"
TOKEN_PLACEHOLDER = "place" + "holder"
TOKEN_INCOMPLETE = "incom" + "plete"
TOKEN_DUMMY = "dum" + "my"

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
    "skeleton wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_SKELETON + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "placeholder wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_PLACEHOLDER + r"s?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "incomplete wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_INCOMPLETE + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "dummy wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_DUMMY + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "Agda hole start": re.compile(r"\{!"),
    "Agda hole end": re.compile(r"!\}"),
    "Python ellipsis body": re.compile(r"^\s*\.\.\.\s*(?:#.*)?$", re.MULTILINE),
    "Python pass body": re.compile(r"^\s*pass\s*(?:#.*)?$", re.MULTILINE),
}

CLAY_NS_PROMOTED_TRUE = re.compile(
    r"(?<![A-Za-z0-9_])clayNavierStokesPromoted(?![A-Za-z0-9_])"
    r"(?:\s*:\s*[^\n=]+)?\s*=\s*true(?![A-Za-z0-9_])",
    re.MULTILINE,
)


def sprint87_agda_files() -> list[Path]:
    files: list[Path] = []
    for prefix in AGDA_PREFIXES:
        files.extend(AGDA_DIR.glob(prefix + "*.agda"))
    return sorted(set(files))


def sprint87_script_files() -> list[Path]:
    files: list[Path] = []
    for pattern in SCRIPT_GLOBS:
        files.extend(SCRIPTS_DIR.glob(pattern))
    return sorted(set(files))


def sprint87_surfaces() -> list[Path]:
    return sprint87_agda_files() + sprint87_script_files()


def require_sprint87_surfaces() -> list[Path]:
    surfaces = sprint87_surfaces()
    if not surfaces:
        pytest.skip(
            "No Sprint 87 Agda or script surfaces found under "
            "DASHI/Physics/Closure/YMSprint87*.agda or scripts/*_sprint87_*.py"
        )
    return surfaces


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def relative(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def agda_module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO_ROOT).with_suffix("").parts)


def test_sprint87_surfaces_have_no_forbidden_placeholders_or_postulates() -> None:
    failures: list[str] = []
    for path in require_sprint87_surfaces():
        text = read_text(path)
        for label, pattern in FORBIDDEN_PATTERNS.items():
            for match in pattern.finditer(text):
                failures.append(
                    f"{relative(path)}:{line_for_offset(text, match.start())}: {label}"
                )

    assert not failures, "Forbidden Sprint 87 surfaces:\n" + "\n".join(failures)


def test_sprint87_does_not_promote_clay_navier_stokes() -> None:
    failures: list[str] = []
    for path in require_sprint87_surfaces():
        text = read_text(path)
        for match in CLAY_NS_PROMOTED_TRUE.finditer(text):
            failures.append(
                f"{relative(path)}:{line_for_offset(text, match.start())}: "
                "clayNavierStokesPromoted is true"
            )

    assert not failures, "Forbidden Clay Navier-Stokes promotion:\n" + "\n".join(failures)


def test_everything_imports_sprint87_agda_modules_if_present() -> None:
    modules = [agda_module_name(path) for path in sprint87_agda_files()]
    if not modules:
        pytest.skip("No Sprint 87 Agda modules found")

    everything = read_text(EVERYTHING)
    missing = [
        module
        for module in modules
        if not re.search(r"^\s*import\s+" + re.escape(module) + r"\s*$", everything, re.MULTILINE)
    ]

    assert not missing, "DASHI/Everything.agda is missing imports:\n" + "\n".join(missing)
