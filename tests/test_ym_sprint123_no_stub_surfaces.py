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

CLAY_PROMOTION = "clay" + "Yang" + "Mills" + "Promoted = true"
FORBIDDEN_PATTERNS = {
    "postulate": re.compile(r"(?<![A-Za-z0-9_])postulate(?![A-Za-z0-9_])"),
    "TODO": re.compile(r"(?<![A-Za-z0-9_])TODO(?![A-Za-z0-9_])"),
    "stub": re.compile(r"(?<![A-Za-z0-9_])stub(?![A-Za-z0-9_])", re.IGNORECASE),
    "Agda hole start": re.compile(r"\{!"),
    "Agda hole end": re.compile(r"!\}"),
    "hole marker": re.compile(r"(?<![A-Za-z0-9_])hole[s]?(?![A-Za-z0-9_])", re.IGNORECASE),
    "Clay promotion": re.compile(re.escape(CLAY_PROMOTION)),
}
DATA_DECL = re.compile(r"^\s*data\s+([A-Za-z][A-Za-z0-9_'-]*)\b")

SECTION_KEYS = {
    "manuscript",
    "section",
    "sections",
    "chapter",
    "subsection",
}
SUPPORT_KEYS = {
    "blocker",
    "blockers",
    "blocked_by",
    "blocking",
    "blocking_reason",
    "dependencies",
    "dependency",
    "depends_on",
    "evidence",
    "evidence_path",
    "evidence_paths",
    "evidence_text",
}
SUPPORT_WORDS = re.compile(
    r"\b(blocker|blockers|blocked|blocking|dependencies|dependency|depends on|evidence)\b",
    re.IGNORECASE,
)
HEADING = re.compile(
    r"(?m)^\s*(?:#{1,6}\s+|--+\s+)?(?:manuscript|section|chapter|subsection)\b.*$",
    re.IGNORECASE,
)


def sprint123_agda_files() -> list[Path]:
    return sorted(AGDA_DIR.glob("YMSprint123*.agda"))


def sprint123_script_files() -> list[Path]:
    return sorted(SCRIPTS_DIR.glob("ym_sprint123_*.py"))


def sprint123_output_roots() -> list[Path]:
    return sorted(path for path in OUTPUTS_DIR.glob("ym_sprint123_*") if path.exists())


def sprint123_output_files() -> list[Path]:
    files: list[Path] = []
    for root in sprint123_output_roots():
        if root.is_file():
            files.append(root)
        else:
            files.extend(path for path in root.rglob("*") if path.is_file())
    return sorted(files)


def sprint123_surfaces() -> list[Path]:
    return sprint123_agda_files() + sprint123_script_files() + sprint123_output_files()


def require_sprint123_surfaces() -> list[Path]:
    surfaces = sprint123_surfaces()
    if not surfaces:
        pytest.skip(
            "No Sprint123 surfaces found under "
            "DASHI/Physics/Closure/YMSprint123*.agda, "
            "scripts/ym_sprint123_*.py, or outputs/ym_sprint123_*"
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


def nearby_text(text: str, offset: int, radius: int = 360) -> str:
    return text[max(0, offset - radius) : min(len(text), offset + radius)]


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


def test_sprint123_surfaces_have_no_promotion_stubs_or_skeleton_markers() -> None:
    failures: list[str] = []
    for path in require_sprint123_surfaces():
        text = read_text(path)
        for label, pattern in FORBIDDEN_PATTERNS.items():
            for match in pattern.finditer(text):
                failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")

        if path.suffix == ".agda":
            for line, datatype in empty_datatypes(text):
                failures.append(
                    f"{relative(path)}:{line}: empty future-proof datatype {datatype!r}"
                )

    assert not failures, "Forbidden Sprint123 production surface markers found:\n" + "\n".join(failures)


def test_sprint123_manuscript_or_section_headings_have_nearby_support() -> None:
    require_sprint123_surfaces()
    candidate_files = [
        path
        for path in sprint123_output_files() + sprint123_script_files()
        if path.suffix.lower() in {".json", ".md", ".txt", ".py"}
    ]
    if not candidate_files:
        pytest.skip("No Sprint123 text, script, JSON, or Markdown section surfaces found")

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
                    failures.append(f"{relative(path)}: JSON entry {label!r} lacks evidence/dependency/blocker")
        else:
            for match in HEADING.finditer(text):
                checked += 1
                if not SUPPORT_WORDS.search(nearby_text(text, match.start())):
                    failures.append(
                        f"{relative(path)}:{line_for_offset(text, match.start())}: "
                        f"heading lacks nearby evidence/dependency/blocker text"
                    )

    if checked == 0:
        pytest.skip("No Sprint123 manuscript/section-like headings or entries found")
    assert not failures, "Sprint123 manuscript/section headings missing support:\n" + "\n".join(failures)


def test_sprint123_agda_modules_are_imported_once_they_exist() -> None:
    agda_files = sprint123_agda_files()
    if not agda_files:
        pytest.skip("No Sprint123 Agda modules found")
    assert EVERYTHING.exists(), "DASHI/Everything.agda is required once Sprint123 Agda modules exist"

    everything_text = read_text(EVERYTHING)
    imported = set(
        re.findall(
            r"(?m)^\s*import\s+(DASHI\.Physics\.Closure\.YMSprint123[A-Za-z0-9_.]*)\s*$",
            everything_text,
        )
    )
    expected = {"DASHI.Physics.Closure." + path.stem for path in agda_files}
    missing = sorted(expected - imported)
    assert not missing, "DASHI/Everything.agda is missing Sprint123 imports: " + ", ".join(missing)
