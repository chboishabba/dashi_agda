from __future__ import annotations

import re
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
SCRIPTS_DIR = REPO_ROOT / "scripts"
TESTS_DIR = REPO_ROOT / "tests"
OUTPUTS_DIR = REPO_ROOT / "outputs"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "125"
AGDA_PREFIX = "YMSprint" + SPRINT
SCRIPT_PREFIX = "ym_sprint" + SPRINT + "_"
TEST_PREFIX = "test_ym_sprint" + SPRINT + "_"
OUTPUT_PREFIX = "ym_sprint" + SPRINT + "_"

TOKEN_A = "post" + "ulate"
TOKEN_B = "TO" + "DO"
TOKEN_C = "st" + "ub"
TOKEN_D = "future" + r"[\s-]*" + "proof"
PROMOTED_TRUE = "clay" + "Yang" + "Mills" + r"Promoted\s*=\s*true"
EVIDENCE_WORD = "evi" + "dence"
DEPENDENCY_WORD = "depend" + "ency"
DEPENDENCIES_WORD = "depend" + "encies"

FORBIDDEN_PATTERNS = {
    TOKEN_A: re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_A + r"(?![A-Za-z0-9_])"),
    TOKEN_B: re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_B + r"(?![A-Za-z0-9_])"),
    TOKEN_C: re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_C + r"(?![A-Za-z0-9_])", re.IGNORECASE),
    "deferred datatype": re.compile(r"(?<![A-Za-z0-9_])" + TOKEN_D + r"(?![A-Za-z0-9_])", re.IGNORECASE),
    "Clay promotion": re.compile(PROMOTED_TRUE),
}

DATA_DECL = re.compile(r"^\s*data\s+([A-Za-z][A-Za-z0-9_'-]*)\b")
SECTION_HEADING = re.compile(r"^(#{1,6})\s+(.+?)\s*$")
ENTRY_LINE = re.compile(r"^\s*(?:[-*]|\d+[.)])\s+\S+")


def sprint125_agda_files() -> list[Path]:
    return sorted(AGDA_DIR.glob(AGDA_PREFIX + "*.agda"))


def sprint125_script_files() -> list[Path]:
    return sorted(SCRIPTS_DIR.glob(SCRIPT_PREFIX + "*.py"))


def sprint125_test_files() -> list[Path]:
    return sorted(TESTS_DIR.glob(TEST_PREFIX + "*.py"))


def sprint125_output_roots() -> list[Path]:
    return sorted(path for path in OUTPUTS_DIR.glob(OUTPUT_PREFIX + "*") if path.exists())


def sprint125_output_files() -> list[Path]:
    files: list[Path] = []
    for root in sprint125_output_roots():
        if root.is_file():
            files.append(root)
        else:
            files.extend(path for path in root.rglob("*") if path.is_file())
    return sorted(files)


def sprint125_surfaces() -> list[Path]:
    return sprint125_agda_files() + sprint125_script_files() + sprint125_test_files() + sprint125_output_files()


def require_sprint125_surfaces() -> list[Path]:
    surfaces = sprint125_surfaces()
    if not surfaces:
        pytest.skip("No Sprint125 surfaces found under Closure Agda, scripts, tests, or outputs")
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


def sprint125_imports() -> set[str]:
    if not EVERYTHING.exists():
        return set()
    everything_text = read_text(EVERYTHING)
    return set(
        re.findall(
            r"(?m)^\s*import\s+(DASHI\.Physics\.Closure\.YMSprint125[A-Za-z0-9_.]*)\s*$",
            everything_text,
        )
    )


def section_blocks(text: str) -> list[tuple[int, str, list[str]]]:
    lines = text.splitlines()
    headings: list[tuple[int, int, str]] = []
    for index, line in enumerate(lines):
        match = SECTION_HEADING.match(line)
        if match:
            headings.append((index, len(match.group(1)), match.group(2).strip()))

    blocks: list[tuple[int, str, list[str]]] = []
    for position, (start, level, title) in enumerate(headings):
        end = len(lines)
        for next_start, next_level, _ in headings[position + 1 :]:
            if next_level <= level:
                end = next_start
                break
        blocks.append((start + 1, title, lines[start + 1 : end]))
    return blocks


def section_requires_entries(title: str) -> bool:
    lowered = title.lower()
    return EVIDENCE_WORD in lowered or DEPENDENCY_WORD in lowered or DEPENDENCIES_WORD in lowered


def section_has_entries(lines: list[str]) -> bool:
    for line in lines:
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if ENTRY_LINE.match(line) and len(stripped.split()) > 2:
            return True
        if ":" in stripped and len(stripped.split()) > 2:
            return True
    return False


def incomplete_markers(text: str) -> list[tuple[int, str]]:
    phrases = [
        "No matching " + EVIDENCE_WORD + " was extracted.",
        "missing " + EVIDENCE_WORD,
        "missing required " + EVIDENCE_WORD,
        "missing " + DEPENDENCY_WORD,
        "missing " + DEPENDENCIES_WORD,
    ]
    failures: list[tuple[int, str]] = []
    for phrase in phrases:
        for match in re.finditer(re.escape(phrase), text, re.IGNORECASE):
            failures.append((line_for_offset(text, match.start()), phrase))
    return failures


def audit_document_files() -> list[Path]:
    return [
        path
        for path in sprint125_output_files()
        if path.suffix.lower() in {".md", ".txt"}
        and ("audit" in path.name.lower() or "audit" in str(path.parent).lower() or "manuscript" in path.name.lower())
    ]


def test_sprint125_production_surfaces_are_complete() -> None:
    failures: list[str] = []
    for path in require_sprint125_surfaces():
        text = read_text(path)
        for label, pattern in FORBIDDEN_PATTERNS.items():
            for match in pattern.finditer(text):
                failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: forbidden marker {label}")

        if path.suffix == ".agda":
            for line, datatype in empty_datatypes(text):
                failures.append(f"{relative(path)}:{line}: empty data declaration {datatype!r}")

    assert not failures, "Forbidden Sprint125 production surface markers found:\n" + "\n".join(failures)


def test_sprint125_audit_documents_record_section_entries() -> None:
    docs = audit_document_files()
    if not docs:
        pytest.skip("No Sprint125 manuscript or audit documents found")

    failures: list[str] = []
    for path in docs:
        text = read_text(path)
        for line, phrase in incomplete_markers(text):
            failures.append(f"{relative(path)}:{line}: incomplete section marker {phrase!r}")
        for line, title, lines in section_blocks(text):
            if section_requires_entries(title) and not section_has_entries(lines):
                failures.append(f"{relative(path)}:{line}: section has no recorded entries {title!r}")

    assert not failures, "Sprint125 manuscript or audit document sections lack recorded entries:\n" + "\n".join(failures)


def test_sprint125_everything_imports_all_modules_once_orchestrator_integrates() -> None:
    agda_files = sprint125_agda_files()
    if not agda_files and not EVERYTHING.exists():
        pytest.skip("No Sprint125 Agda modules and no DASHI/Everything.agda found")

    imports = sprint125_imports()
    if not imports:
        pytest.skip("No Sprint125 imports in DASHI/Everything.agda yet")

    assert agda_files, "DASHI/Everything.agda imports Sprint125 modules, but no Sprint125 Agda files exist"
    expected = {"DASHI.Physics.Closure." + path.stem for path in agda_files}
    extra = sorted(imports - expected)
    assert not extra, "DASHI/Everything.agda imports missing Sprint125 modules: " + ", ".join(extra)

    missing = sorted(expected - imports)
    assert not missing, "DASHI/Everything.agda is missing Sprint125 imports: " + ", ".join(missing)
