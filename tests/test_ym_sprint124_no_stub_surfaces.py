from __future__ import annotations

import re
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
SCRIPTS_DIR = REPO_ROOT / "scripts"
OUTPUTS_DIR = REPO_ROOT / "outputs"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "124"
AGDA_PREFIX = "YMSprint" + SPRINT
SCRIPT_PREFIX = "ym_sprint" + SPRINT + "_"
OUTPUT_PREFIX = "ym_sprint" + SPRINT + "_"
CLAY_PROMOTION_PATTERN = "clay" + "Yang" + "Mills" + r"Promoted\s*=\s*true"
FUTURE_PROOF = "future" + r"[\s-]*" + "proof"

FORBIDDEN_PATTERNS = {
    "postulate": re.compile(r"(?<![A-Za-z0-9_])postulate(?![A-Za-z0-9_])"),
    "TODO": re.compile(r"(?<![A-Za-z0-9_])TODO(?![A-Za-z0-9_])"),
    "stub": re.compile(r"(?<![A-Za-z0-9_])stub(?![A-Za-z0-9_])", re.IGNORECASE),
    "Agda hole start": re.compile(r"\{!"),
    "Agda hole end": re.compile(r"!\}"),
    "hole marker": re.compile(r"(?<![A-Za-z0-9_])hole[s]?(?![A-Za-z0-9_])", re.IGNORECASE),
    "dummy": re.compile(r"(?<![A-Za-z0-9_])dummy(?![A-Za-z0-9_])", re.IGNORECASE),
    "future proof": re.compile(r"(?<![A-Za-z0-9_])" + FUTURE_PROOF + r"(?![A-Za-z0-9_])", re.IGNORECASE),
    "Clay promotion": re.compile(CLAY_PROMOTION_PATTERN),
}

DATA_DECL = re.compile(r"^\s*data\s+([A-Za-z][A-Za-z0-9_'-]*)\b")


def sprint124_agda_files() -> list[Path]:
    return sorted(AGDA_DIR.glob(AGDA_PREFIX + "*.agda"))


def sprint124_script_files() -> list[Path]:
    return sorted(SCRIPTS_DIR.glob(SCRIPT_PREFIX + "*.py"))


def sprint124_output_roots() -> list[Path]:
    return sorted(path for path in OUTPUTS_DIR.glob(OUTPUT_PREFIX + "*") if path.exists())


def sprint124_output_files() -> list[Path]:
    files: list[Path] = []
    for root in sprint124_output_roots():
        if root.is_file():
            files.append(root)
        else:
            files.extend(path for path in root.rglob("*") if path.is_file())
    return sorted(files)


def sprint124_surfaces() -> list[Path]:
    return sprint124_agda_files() + sprint124_script_files() + sprint124_output_files()


def require_sprint124_surfaces() -> list[Path]:
    surfaces = sprint124_surfaces()
    if not surfaces:
        pytest.skip(
            "No Sprint124 surfaces found under "
            "DASHI/Physics/Closure/YMSprint124*.agda, "
            "scripts/ym_sprint124_*.py, or outputs/ym_sprint124_*"
        )
    return surfaces


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def relative(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def empty_datatypes(text: str) -> list[tuple[int, str]]:
    failures: list[tuple[int, str]] = []
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
            failures.append((start + 1, name))

    return failures


def sprint124_imports() -> set[str]:
    if not EVERYTHING.exists():
        return set()
    everything_text = read_text(EVERYTHING)
    return set(
        re.findall(
            r"(?m)^\s*import\s+(DASHI\.Physics\.Closure\.YMSprint124[A-Za-z0-9_.]*)\s*$",
            everything_text,
        )
    )


def test_sprint124_production_surfaces_have_no_promotion_stubs_or_skeleton_markers() -> None:
    failures: list[str] = []
    for path in require_sprint124_surfaces():
        text = read_text(path)
        for label, pattern in FORBIDDEN_PATTERNS.items():
            for match in pattern.finditer(text):
                failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")

        if path.suffix == ".agda":
            for line, datatype in empty_datatypes(text):
                failures.append(f"{relative(path)}:{line}: empty skeleton datatype {datatype!r}")

    assert not failures, "Forbidden Sprint124 production surface markers found:\n" + "\n".join(failures)


def test_sprint124_everything_imports_all_modules_once_orchestrator_integrates() -> None:
    agda_files = sprint124_agda_files()
    if not agda_files and not EVERYTHING.exists():
        pytest.skip("No Sprint124 Agda modules and no DASHI/Everything.agda found")

    imports = sprint124_imports()
    if not imports:
        pytest.skip("No Sprint124 imports in DASHI/Everything.agda yet")

    assert agda_files, "DASHI/Everything.agda imports Sprint124 modules, but no Sprint124 Agda files exist"
    expected = {"DASHI.Physics.Closure." + path.stem for path in agda_files}
    extra = sorted(imports - expected)
    assert not extra, "DASHI/Everything.agda imports missing Sprint124 modules: " + ", ".join(extra)

    missing = sorted(expected - imports)
    assert not missing, "DASHI/Everything.agda is missing Sprint124 imports: " + ", ".join(missing)
