from __future__ import annotations

import re
from pathlib import Path
from typing import Iterable

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
SCRIPTS_DIR = REPO_ROOT / "scripts"
OUTPUTS_DIR = REPO_ROOT / "outputs"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "130"
AGDA_PREFIX = "YMSprint" + SPRINT
SCRIPT_PREFIX = "ym_sprint" + SPRINT + "_"
OUTPUT_PREFIX = "ym_sprint" + SPRINT + "_"

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_TODO = "TO" + "DO"
TOKEN_STUB = "st" + "ub"
TOKEN_SKELETON = "skele" + "ton"
TOKEN_DUMMY = "dum" + "my"
TOKEN_FUTURE_PROOF = "future" + r"[\s-]*" + "proof"
PROMOTED_TRUE = "clay" + "Yang" + "Mills" + r"Promoted\s*=\s*true"

FORBIDDEN_PATTERNS = {
    "unproved axiom marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_POSTULATE + r"(?![A-Za-z0-9_])"
    ),
    "open work marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_TODO + r"(?![A-Za-z0-9_])"
    ),
    "placeholder wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_STUB + r"(?![A-Za-z0-9_])", re.IGNORECASE
    ),
    "bare scaffold wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_SKELETON + r"(?![A-Za-z0-9_])", re.IGNORECASE
    ),
    "dummy wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_DUMMY + r"(?![A-Za-z0-9_])", re.IGNORECASE
    ),
    "deferred datatype wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_FUTURE_PROOF + r"(?![A-Za-z0-9_])", re.IGNORECASE
    ),
    "Clay promotion": re.compile(PROMOTED_TRUE),
}

DATA_DECL = re.compile(r"^\s*data\s+([A-Za-z][A-Za-z0-9_'-]*)\b")
SPRINT_IMPORT = re.compile(
    r"(?m)^\s*import\s+(DASHI\.Physics\.Closure\.YMSprint130[A-Za-z0-9_.]*)\s*$"
)


def sprint130_agda_files() -> list[Path]:
    return sorted(AGDA_DIR.glob(AGDA_PREFIX + "*.agda"))


def sprint130_script_files() -> list[Path]:
    return sorted(SCRIPTS_DIR.glob(SCRIPT_PREFIX + "*.py"))


def sprint130_output_roots() -> list[Path]:
    return sorted(path for path in OUTPUTS_DIR.glob(OUTPUT_PREFIX + "*") if path.exists())


def sprint130_output_files() -> list[Path]:
    files: list[Path] = []
    for root in sprint130_output_roots():
        if root.is_file():
            files.append(root)
        else:
            files.extend(path for path in root.rglob("*") if path.is_file())
    return sorted(files)


def sprint130_surfaces() -> list[Path]:
    return sprint130_agda_files() + sprint130_script_files() + sprint130_output_files()


def require_sprint130_surfaces() -> list[Path]:
    surfaces = sprint130_surfaces()
    if not surfaces:
        pytest.skip(
            "No Sprint130 production surfaces found under "
            "DASHI/Physics/Closure/YMSprint130*.agda, "
            "scripts/ym_sprint130_*.py, or outputs/ym_sprint130_*"
        )
    return surfaces


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def relative(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


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
            indented = lines[index].startswith(" ") or lines[index].startswith("\t")
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


def everything_sprint130_imports() -> set[str]:
    if not EVERYTHING.exists():
        return set()
    return set(SPRINT_IMPORT.findall(read_text(EVERYTHING)))


def test_sprint130_surfaces_have_no_incomplete_or_promoted_markers() -> None:
    failures: list[str] = []
    for path in require_sprint130_surfaces():
        text = read_text(path)
        for label, pattern in FORBIDDEN_PATTERNS.items():
            for match in pattern.finditer(text):
                failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")

        if path.suffix == ".agda":
            for line, datatype in empty_datatypes(text):
                failures.append(f"{relative(path)}:{line}: empty datatype {datatype!r}")

    assert not failures, "Forbidden Sprint130 production surface markers found:\n" + "\n".join(failures)


def test_sprint130_everything_imports_all_modules_after_integration() -> None:
    agda_files = sprint130_agda_files()
    imports = everything_sprint130_imports()

    if not agda_files and not imports:
        pytest.skip("No Sprint130 Agda modules or DASHI/Everything.agda Sprint130 imports yet")

    assert agda_files, "DASHI/Everything.agda imports Sprint130 modules, but no Sprint130 Agda files exist"
    expected = {"DASHI.Physics.Closure." + path.stem for path in agda_files}

    extra = sorted(imports - expected)
    assert not extra, "DASHI/Everything.agda imports unknown Sprint130 modules: " + ", ".join(extra)

    missing = sorted(expected - imports)
    assert not missing, "DASHI/Everything.agda is missing Sprint130 imports: " + ", ".join(missing)
