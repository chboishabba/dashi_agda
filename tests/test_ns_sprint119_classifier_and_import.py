from __future__ import annotations

import json
import re
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
SCRIPT_DIR = REPO_ROOT / "scripts"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "119"
PREVIOUS_MODULE = "DASHI.Physics.Closure.NSSprint118NonCircularGeometricCorrelation"
EXPECTED_STEM = "NSSprint" + SPRINT + "PersistentAlignmentExistence"
EXPECTED_MODULE = "DASHI.Physics.Closure." + EXPECTED_STEM
EXPECTED_FILE = AGDA_DIR / (EXPECTED_STEM + ".agda")
CLASSIFIER = SCRIPT_DIR / ("ns_sprint" + SPRINT + "_persistence_source_classifier.py")

RECOMMENDED_SOURCE = "PersistentAlignmentExistenceLowerBound"
OPEN_GATE = "persistent_alignment_existence"
REJECTED_ASSUMPTION = "imposed_alignment_assumption"
PROMOTION_FLAG = "clay" + "Navier" + "Stokes" + "Promoted"

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_TODO = "TO" + "DO"
TOKEN_STUB = "st" + "ub"
TOKEN_SKELETON = "skele" + "ton"
TOKEN_ADMIT = "ad" + "mit"
TOKEN_DUMMY = "du" + "mmy"
TOKEN_FUTURE_PROOF = "future" + "-" + "proof"
TOKEN_HOLE = "ho" + "le"
TOKEN_TRUE = "tr" + "ue"
TOKEN_FALSE = "fa" + "lse"

FORBIDDEN_AGDA_PATTERNS = {
    "unproved axiom marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_POSTULATE + r"(?![A-Za-z0-9_])"
    ),
    "open work marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_TODO + r"(?![A-Za-z0-9_])"
    ),
    "incomplete implementation marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_STUB + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "empty framework marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_SKELETON + r"s?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "accepted-without-proof marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_ADMIT + r"(?:ted|s)?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "placeholder marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_DUMMY + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "deferred-proof marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_FUTURE_PROOF + r"(?:ed|ing)?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "gap marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_HOLE + r"s?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "Agda gap start": re.compile(r"\{!"),
    "Agda gap end": re.compile(r"!\}"),
    "Agda question-mark placeholder": re.compile(r"=\s*\?(?![A-Za-z0-9_])"),
}

REQUIRED_ANCHORS = (
    EXPECTED_STEM,
    "canonical" + EXPECTED_STEM,
    "canonical" + EXPECTED_STEM + "Receipt",
    "NSSprint118NonCircularGeometricCorrelation",
    "canonicalNSSprint118NonCircularGeometricCorrelation",
    RECOMMENDED_SOURCE,
    PROMOTION_FLAG,
)

REQUIRED_STRINGS = (
    "persistent alignment existence",
    "PersistentAlignmentExistenceLowerBound",
    "imposed alignment assumption",
    "rejected circular",
    "open primary gate",
    "non-circular geometric correlation",
    "Sprint118",
    "clayNavierStokesPromoted remains false",
)

DATA_DECL = re.compile(r"^\s*data\s+([A-Za-z][A-Za-z0-9_'-]*)\b")


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def agda_module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO_ROOT).with_suffix("").parts)


def sprint119_ns_agda_files() -> list[Path]:
    return sorted(path for path in AGDA_DIR.glob("NSSprint" + SPRINT + "*.agda") if path.is_file())


def require_sprint119_ns_agda_module() -> Path:
    modules = sprint119_ns_agda_files()
    assert modules == [EXPECTED_FILE], (
        "Sprint 119 NS must have exactly one Agda file, "
        + relative(EXPECTED_FILE)
        + "; found: "
        + ", ".join(relative(path) for path in modules)
    )
    assert agda_module_name(EXPECTED_FILE) == EXPECTED_MODULE
    return EXPECTED_FILE


def identifier_pattern(identifier: str) -> re.Pattern[str]:
    return re.compile(r"(?<![A-Za-z0-9_])" + re.escape(identifier) + r"(?![A-Za-z0-9_])")


def bool_assignment_pattern(identifier: str, value: bool) -> re.Pattern[str]:
    agda_value = TOKEN_TRUE if value else TOKEN_FALSE
    return re.compile(
        r"(?<![A-Za-z0-9_])"
        + re.escape(identifier)
        + r"(?![A-Za-z0-9_])"
        + r"(?:\s*:\s*[^\n=]+)?\s*=\s*"
        + agda_value
        + r"(?![A-Za-z0-9_])",
        re.MULTILINE,
    )


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


def incomplete_marker_failures(path: Path) -> list[str]:
    text = read_text(path)
    failures: list[str] = []
    for label, pattern in FORBIDDEN_AGDA_PATTERNS.items():
        for match in pattern.finditer(text):
            failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")

    for line, datatype in empty_datatypes(text):
        failures.append(f"{relative(path)}:{line}: empty datatype {datatype!r}")

    return failures


def json_values(payload: Any) -> Iterable[Any]:
    if isinstance(payload, dict):
        yield payload
        for value in payload.values():
            yield from json_values(value)
    elif isinstance(payload, list):
        for value in payload:
            yield from json_values(value)
    else:
        yield payload


def route_payloads(payloads: list[Any], route_id: str) -> list[dict[str, Any]]:
    matches: list[dict[str, Any]] = []
    for value in json_values(payloads):
        if isinstance(value, dict) and route_id in json.dumps(value, sort_keys=True):
            matches.append(value)
    return matches


def payload_has_status(payloads: list[Any], route_id: str, status: str) -> bool:
    return any(status in json.dumps(payload, sort_keys=True) for payload in route_payloads(payloads, route_id))


def no_clay_complete_route(payloads: list[Any]) -> bool:
    for value in json_values(payloads):
        if not isinstance(value, dict):
            continue
        complete = value.get("complete", value.get("clay_complete", value.get("clayComplete")))
        clay = value.get("clay", value.get("clay_promoted", value.get("clay_navier_stokes_promoted")))
        if complete is True and clay is True:
            return False
    return True


def run_classifier(tmp_path: Path) -> tuple[subprocess.CompletedProcess[str], list[Any], str]:
    assert CLASSIFIER.exists(), "Sprint119 NS persistence source classifier is missing"

    out_dir = tmp_path / "ns_sprint119_persistence_source_classifier"
    result = subprocess.run(
        [sys.executable, str(CLASSIFIER), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    json_files = sorted(out_dir.glob("*.json"))
    markdown_files = sorted(out_dir.glob("*.md"))
    payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_files]
    artifact_text = "\n".join(
        path.read_text(encoding="utf-8", errors="replace")
        for path in json_files + markdown_files
        if path.is_file()
    )
    output_text = "\n".join((result.stdout, result.stderr, artifact_text))

    assert json_files, "classifier must write at least one JSON artifact"
    assert markdown_files, "classifier must write at least one Markdown artifact"
    return result, payloads, output_text


def test_persistence_source_classifier_exits_1_and_writes_json_and_markdown(tmp_path: Path) -> None:
    result, _payloads, output_text = run_classifier(tmp_path)

    assert result.returncode == 1, output_text


def test_persistence_source_classifier_marks_gates_and_recommends_lower_bound(
    tmp_path: Path,
) -> None:
    result, payloads, output_text = run_classifier(tmp_path)

    assert result.returncode == 1, output_text
    assert RECOMMENDED_SOURCE in json.dumps(payloads, sort_keys=True), output_text
    assert payload_has_status(payloads, OPEN_GATE, "open_primary_gate"), output_text
    assert payload_has_status(payloads, REJECTED_ASSUMPTION, "rejected_circular"), output_text
    assert no_clay_complete_route(payloads), output_text


def test_everything_imports_sprint119_ns_after_sprint118_once() -> None:
    require_sprint119_ns_agda_module()
    everything = read_text(EVERYTHING)

    previous_import = "import " + PREVIOUS_MODULE
    sprint119_import = "import " + EXPECTED_MODULE
    imports = re.findall(
        r"^\s*" + re.escape(sprint119_import) + r"\s*$",
        everything,
        re.MULTILINE,
    )

    assert imports, "DASHI/Everything.agda is missing import: " + EXPECTED_MODULE
    assert len(imports) == 1, "DASHI/Everything.agda imports more than once: " + EXPECTED_MODULE
    assert previous_import in everything, "DASHI/Everything.agda is missing import: " + PREVIOUS_MODULE
    assert everything.index(previous_import) < everything.index(sprint119_import), (
        "DASHI/Everything.agda must import Sprint119 after Sprint118"
    )


def test_sprint119_ns_agda_contains_required_strings_and_no_placeholder_markers() -> None:
    path = require_sprint119_ns_agda_module()
    text = read_text(path)
    missing_anchors = [anchor for anchor in REQUIRED_ANCHORS if not identifier_pattern(anchor).search(text)]
    missing_strings = [required for required in REQUIRED_STRINGS if required not in text]
    failures = incomplete_marker_failures(path)

    assert re.search(r"^\s*module\s+" + re.escape(EXPECTED_MODULE) + r"\s+where\s*$", text, re.MULTILINE), (
        relative(path) + " must declare module " + EXPECTED_MODULE
    )
    assert not missing_anchors, relative(path) + " is missing Sprint 119 anchors:\n" + "\n".join(missing_anchors)
    assert not missing_strings, relative(path) + " is missing Sprint 119 strings:\n" + "\n".join(missing_strings)
    assert bool_assignment_pattern(PROMOTION_FLAG, False).search(text), (
        relative(path) + " must explicitly keep " + PROMOTION_FLAG + " = false"
    )
    assert not bool_assignment_pattern(PROMOTION_FLAG, True).search(text), (
        relative(path) + " unexpectedly promotes Clay completion"
    )
    assert not failures, "Forbidden Sprint 119 NS Agda surface:\n" + "\n".join(failures)
