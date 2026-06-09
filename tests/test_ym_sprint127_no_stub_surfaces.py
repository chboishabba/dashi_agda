from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Iterable

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
SCRIPTS_DIR = REPO_ROOT / "scripts"
OUTPUTS_DIR = REPO_ROOT / "outputs"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "127"
AGDA_PREFIX = "YMSprint" + SPRINT
SCRIPT_PREFIX = "ym_sprint" + SPRINT + "_"
OUTPUT_PREFIX = "ym_sprint" + SPRINT + "_"

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_TODO = "TO" + "DO"
TOKEN_STUB = "st" + "ub"
TOKEN_SKELETON = "skele" + "ton"
TOKEN_FUTURE_PROOF = "future" + r"[\s-]*" + "proof"
PROMOTED_TRUE = "clay" + "Yang" + "Mills" + r"Promoted\s*=\s*true"
EVIDENCE_WORD = "evi" + "dence"
DEPENDENCY_WORD = "depend" + "ency"
DEPENDENCIES_WORD = "depend" + "encies"
BLOCKER_WORD = "block" + "er"
BLOCKERS_WORD = "block" + "ers"
BLOCKED_BY_WORD = "blocked" + "_by"
DEPENDS_ON_WORD = "depends" + "_on"

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
    "Agda hole start": re.compile(r"\{!"),
    "Agda hole end": re.compile(r"!\}"),
    "hole wording": re.compile(r"(?<![A-Za-z0-9_])hole[s]?(?![A-Za-z0-9_])", re.IGNORECASE),
    "dummy wording": re.compile(r"(?<![A-Za-z0-9_])dummy(?![A-Za-z0-9_])", re.IGNORECASE),
    "deferred datatype wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_FUTURE_PROOF + r"(?![A-Za-z0-9_])", re.IGNORECASE
    ),
    "Clay promotion": re.compile(PROMOTED_TRUE),
}

DATA_DECL = re.compile(r"^\s*data\s+([A-Za-z][A-Za-z0-9_'-]*)\b")
SECTION_HEADING = re.compile(r"^(#{1,6})\s+(.+?)\s*$")
ENTRY_LINE = re.compile(r"^\s*(?:[-*]|\d+[.)])\s+\S+")

SECTION_KEYS = {
    "manuscript",
    "section",
    "sections",
    "chapter",
    "subsection",
}
SUPPORT_KEYS = {
    BLOCKER_WORD,
    BLOCKERS_WORD,
    BLOCKED_BY_WORD,
    "blocking",
    "blocking_reason",
    DEPENDENCIES_WORD,
    DEPENDENCY_WORD,
    DEPENDS_ON_WORD,
    EVIDENCE_WORD,
    EVIDENCE_WORD + "_path",
    EVIDENCE_WORD + "_paths",
    EVIDENCE_WORD + "_text",
    "source",
    "sources",
    "status",
}
SUPPORT_WORDS = re.compile(
    r"\b("
    + BLOCKER_WORD
    + r"|"
    + BLOCKERS_WORD
    + r"|blocked|blocking|source|status|"
    + DEPENDENCIES_WORD
    + r"|"
    + DEPENDENCY_WORD
    + r"|depends on|"
    + EVIDENCE_WORD
    + r")\b",
    re.IGNORECASE,
)


def sprint127_agda_files() -> list[Path]:
    return sorted(AGDA_DIR.glob(AGDA_PREFIX + "*.agda"))


def sprint127_script_files() -> list[Path]:
    return sorted(SCRIPTS_DIR.glob(SCRIPT_PREFIX + "*.py"))


def sprint127_output_roots() -> list[Path]:
    return sorted(path for path in OUTPUTS_DIR.glob(OUTPUT_PREFIX + "*") if path.exists())


def sprint127_output_files() -> list[Path]:
    files: list[Path] = []
    for root in sprint127_output_roots():
        if root.is_file():
            files.append(root)
        else:
            files.extend(path for path in root.rglob("*") if path.is_file())
    return sorted(files)


def sprint127_surfaces() -> list[Path]:
    return sprint127_agda_files() + sprint127_script_files() + sprint127_output_files()


def require_sprint127_surfaces() -> list[Path]:
    surfaces = sprint127_surfaces()
    if not surfaces:
        pytest.skip(
            "No Sprint127 production surfaces found under "
            "DASHI/Physics/Closure/YMSprint127*.agda, "
            "scripts/ym_sprint127_*.py, or outputs/ym_sprint127_*"
        )
    return surfaces


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def relative(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def nonempty(value: Any) -> bool:
    if value is None:
        return False
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, (list, tuple, set, dict)):
        return bool(value)
    return True


def iter_json_dicts(value: Any) -> Iterable[dict[str, Any]]:
    if isinstance(value, dict):
        yield value
        for nested in value.values():
            yield from iter_json_dicts(nested)
    elif isinstance(value, list):
        for nested in value:
            yield from iter_json_dicts(nested)


def looks_section_like(entry: dict[str, Any]) -> bool:
    keys = {str(key).lower() for key in entry}
    if keys & SECTION_KEYS:
        return True
    title = entry.get("title")
    return isinstance(title, str) and bool(
        re.search(r"\b(manuscript|section|chapter|subsection)\b", title, re.IGNORECASE)
    )


def has_support(entry: dict[str, Any]) -> bool:
    return any(str(key).lower() in SUPPORT_KEYS and nonempty(value) for key, value in entry.items())


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
    return (
        "manuscript" in lowered
        or "section" in lowered
        or EVIDENCE_WORD in lowered
        or DEPENDENCY_WORD in lowered
        or DEPENDENCIES_WORD in lowered
        or BLOCKER_WORD in lowered
    )


def section_has_entries(lines: list[str]) -> bool:
    for line in lines:
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if SUPPORT_WORDS.search(stripped):
            return True
        if ENTRY_LINE.match(line) and len(stripped.split()) > 2:
            return True
        if ":" in stripped and len(stripped.split()) > 2:
            return True
    return False


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


def test_sprint127_production_surfaces_are_complete() -> None:
    failures: list[str] = []
    for path in require_sprint127_surfaces():
        text = read_text(path)
        for label, pattern in FORBIDDEN_PATTERNS.items():
            for match in pattern.finditer(text):
                failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")

        if path.suffix == ".agda":
            for line, datatype in empty_datatypes(text):
                failures.append(f"{relative(path)}:{line}: empty deferred datatype {datatype!r}")

    assert not failures, "Forbidden Sprint127 production surface markers found:\n" + "\n".join(failures)


def test_sprint127_manuscript_or_audit_sections_record_support() -> None:
    require_sprint127_surfaces()
    candidate_files = [
        path
        for path in sprint127_output_files()
        if path.suffix.lower() in {".json", ".md", ".txt"}
        and (
            "audit" in path.name.lower()
            or "audit" in str(path.parent).lower()
            or "manuscript" in path.name.lower()
            or "section" in path.name.lower()
            or "submission" in path.name.lower()
            or "readiness" in path.name.lower()
        )
    ]
    if not candidate_files:
        pytest.skip("No Sprint127 manuscript, section, submission, readiness, or audit output files found")

    checked = 0
    failures: list[str] = []
    for path in candidate_files:
        text = read_text(path)
        if path.suffix.lower() == ".json":
            data = json.loads(text)
            for entry in iter_json_dicts(data):
                if not looks_section_like(entry):
                    continue
                checked += 1
                if not has_support(entry):
                    label = entry.get("id") or entry.get("title") or entry.get("section") or "<entry>"
                    failures.append(
                        f"{relative(path)}: JSON entry {label!r} lacks recorded support"
                    )
        else:
            for line, title, lines in section_blocks(text):
                if not section_requires_entries(title):
                    continue
                checked += 1
                if not section_has_entries(lines):
                    failures.append(f"{relative(path)}:{line}: section has no recorded support {title!r}")

    if checked == 0:
        pytest.skip("No Sprint127 manuscript, section, submission, readiness, or audit entries found")
    assert not failures, "Sprint127 manuscript or audit sections missing support:\n" + "\n".join(failures)


def test_sprint127_everything_imports_all_modules_after_integration() -> None:
    agda_files = sprint127_agda_files()
    if not agda_files and not EVERYTHING.exists():
        pytest.skip("No Sprint127 Agda modules and no DASHI/Everything.agda found")

    imports = set()
    if EVERYTHING.exists():
        imports = set(
            re.findall(
                r"(?m)^\s*import\s+(DASHI\.Physics\.Closure\.YMSprint127[A-Za-z0-9_.]*)\s*$",
                read_text(EVERYTHING),
            )
        )
    if not imports:
        pytest.skip("No Sprint127 imports in DASHI/Everything.agda yet")

    assert agda_files, "DASHI/Everything.agda imports Sprint127 modules, but no Sprint127 Agda files exist"
    expected = {"DASHI.Physics.Closure." + path.stem for path in agda_files}
    extra = sorted(imports - expected)
    assert not extra, "DASHI/Everything.agda imports unknown Sprint127 modules: " + ", ".join(extra)

    missing = sorted(expected - imports)
    assert not missing, "DASHI/Everything.agda is missing Sprint127 imports: " + ", ".join(missing)
