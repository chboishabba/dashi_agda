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

SECTION_KEYS = {
    "manuscript",
    "section",
    "sections",
    "chapter",
    "subsection",
}
SUPPORT_KEYS = {
    "evidence",
    "evidence_text",
    "evidence_path",
    "evidence_paths",
    "blocker",
    "blockers",
    "blocked_by",
    "blocking",
    "blocking_reason",
}
SUPPORT_WORDS = re.compile(r"\b(evidence|blocker|blockers|blocked|blocking)\b", re.IGNORECASE)


def sprint122_agda_files() -> list[Path]:
    return sorted(AGDA_DIR.glob("YMSprint122*.agda"))


def sprint122_script_files() -> list[Path]:
    return sorted(SCRIPTS_DIR.glob("ym_sprint122_*.py"))


def sprint122_output_roots() -> list[Path]:
    return sorted(path for path in OUTPUTS_DIR.glob("ym_sprint122_*") if path.exists())


def sprint122_output_files() -> list[Path]:
    files: list[Path] = []
    for root in sprint122_output_roots():
        if root.is_file():
            files.append(root)
        else:
            files.extend(path for path in root.rglob("*") if path.is_file())
    return sorted(files)


def sprint122_surfaces() -> list[Path]:
    return sprint122_agda_files() + sprint122_script_files() + sprint122_output_files()


def require_sprint122_surfaces() -> list[Path]:
    surfaces = sprint122_surfaces()
    if not surfaces:
        pytest.skip(
            "No Sprint122 surfaces found under "
            "DASHI/Physics/Closure/YMSprint122*.agda, "
            "scripts/ym_sprint122_*.py, or outputs/ym_sprint122_*/"
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
    if isinstance(title, str) and re.search(r"\b(manuscript|section|chapter|subsection)\b", title, re.IGNORECASE):
        return True
    return False


def has_support(entry: dict[str, Any]) -> bool:
    for key, value in entry.items():
        lowered = str(key).lower()
        if lowered in SUPPORT_KEYS and nonempty(value):
            return True
    return False


def markdown_sections(text: str) -> list[tuple[str, str]]:
    heading_matches = list(re.finditer(r"(?m)^(#{1,6})\s+(.+?)\s*$", text))
    sections: list[tuple[str, str]] = []
    for index, match in enumerate(heading_matches):
        end = heading_matches[index + 1].start() if index + 1 < len(heading_matches) else len(text)
        title = match.group(2)
        body = text[match.end() : end]
        if re.search(r"\b(manuscript|section)\b", title, re.IGNORECASE):
            sections.append((title, body))
    return sections


def test_sprint122_surfaces_have_no_promotion_stubs_or_skeleton_markers() -> None:
    failures: list[str] = []
    for path in require_sprint122_surfaces():
        text = read_text(path)
        for label, pattern in FORBIDDEN_PATTERNS.items():
            for match in pattern.finditer(text):
                failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")

    assert not failures, "Forbidden Sprint122 surface markers found:\n" + "\n".join(failures)


def test_sprint122_manuscript_or_section_entries_have_evidence_or_blockers() -> None:
    require_sprint122_surfaces()
    candidate_files = [
        path
        for path in sprint122_output_files() + sprint122_script_files()
        if path.suffix.lower() in {".json", ".md"}
    ]
    if not candidate_files:
        pytest.skip("No Sprint122 JSON or Markdown manuscript/section surfaces found")

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
                    failures.append(f"{relative(path)}: JSON entry {label!r} lacks evidence/blockers")
        elif path.suffix.lower() == ".md":
            for title, body in markdown_sections(text):
                checked += 1
                if not SUPPORT_WORDS.search(body):
                    failures.append(f"{relative(path)}: Markdown section {title!r} lacks evidence/blockers")

    if checked == 0:
        pytest.skip("No Sprint122 manuscript/section-like JSON or Markdown entries found")
    assert not failures, "Sprint122 manuscript/section entries missing support:\n" + "\n".join(failures)


def test_sprint122_everything_imports_only_existing_integrated_modules() -> None:
    agda_files = sprint122_agda_files()
    if not agda_files and not EVERYTHING.exists():
        pytest.skip("No Sprint122 Agda modules and no DASHI/Everything.agda found")
    if not agda_files:
        everything_text = read_text(EVERYTHING)
        if "DASHI.Physics.Closure.YMSprint122" not in everything_text:
            pytest.skip("No Sprint122 Agda modules or Everything imports found")

    module_by_import = {
        "DASHI.Physics.Closure." + path.stem: path
        for path in agda_files
    }
    everything_text = read_text(EVERYTHING)
    imported = re.findall(
        r"(?m)^\s*import\s+(DASHI\.Physics\.Closure\.YMSprint122[A-Za-z0-9_.]*)\s*$",
        everything_text,
    )

    missing = [module for module in imported if module not in module_by_import]
    assert not missing, "Everything imports missing Sprint122 modules: " + ", ".join(missing)

    if imported:
        unintegrated = [
            module
            for module in imported
            if any(
                pattern.search(read_text(module_by_import[module]))
                for pattern in FORBIDDEN_PATTERNS.values()
            )
        ]
        assert not unintegrated, (
            "Everything imports Sprint122 modules before no-promotion/no-skeleton integration: "
            + ", ".join(unintegrated)
        )
