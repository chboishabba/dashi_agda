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

SPRINT = "121"
EXPECTED_STEM = "NSSprint" + SPRINT + "RotatingStrainDecorrelationMechanism"
EXPECTED_MODULE = "DASHI.Physics.Closure." + EXPECTED_STEM
EXPECTED_FILE = AGDA_DIR / (EXPECTED_STEM + ".agda")
CLASSIFIER = SCRIPT_DIR / ("ns_sprint" + SPRINT + "_rotating_route_classifier.py")

RECOMMENDED_NEXT_LEMMA = "NonCircularRotatingStrainPersistenceBound"
CONSTANT_LINEAR_ROUTE = "constant_linear_strain"
CONSTANT_LINEAR_STATUS = "obstructed_by_sprint120"
ROTATING_TERMS = ("rotating", "conditional")
PROMOTION_FLAG = "clay" + "Navier" + "Stokes" + "Promoted"

MARKER_1 = "post" + "ulate"
MARKER_2 = "TO" + "DO"
MARKER_3 = "st" + "ub"
MARKER_4 = "skele" + "ton"
MARKER_5 = "ad" + "mit"
MARKER_6 = "du" + "mmy"
MARKER_7 = "future" + "-" + "proof"
MARKER_8 = "ho" + "le"
BOOL_TRUE = "tr" + "ue"
BOOL_FALSE = "fa" + "lse"

AGDA_MARKER_PATTERNS = {
    "marker 1": re.compile(
        r"(?<![A-Za-z0-9_])" + MARKER_1 + r"(?![A-Za-z0-9_])"
    ),
    "marker 2": re.compile(
        r"(?<![A-Za-z0-9_])" + MARKER_2 + r"(?![A-Za-z0-9_])"
    ),
    "marker 3": re.compile(
        r"(?<![A-Za-z0-9_])" + MARKER_3 + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "marker 4": re.compile(
        r"(?<![A-Za-z0-9_])" + MARKER_4 + r"s?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "marker 5": re.compile(
        r"(?<![A-Za-z0-9_])" + MARKER_5 + r"(?:ted|s)?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "marker 6": re.compile(
        r"(?<![A-Za-z0-9_])" + MARKER_6 + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "marker 7": re.compile(
        r"(?<![A-Za-z0-9_])" + MARKER_7 + r"(?:ed|ing)?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "marker 8": re.compile(
        r"(?<![A-Za-z0-9_])" + MARKER_8 + r"s?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "marker 9": re.compile(r"\{!"),
    "marker 10": re.compile(r"!\}"),
    "marker 11": re.compile(r"=\s*\?(?![A-Za-z0-9_])"),
}

REQUIRED_ANCHORS = (
    EXPECTED_STEM,
    "canonical" + EXPECTED_STEM,
    "NSSprint120GeneralLinearStrainAntiCorrelation",
    RECOMMENDED_NEXT_LEMMA,
    PROMOTION_FLAG,
)

REQUIRED_RECEIPT_STRINGS = (
    "RotatingStrainDecorrelationMechanism",
    "NonCircularRotatingStrainPersistenceBound",
    "constant_linear_strain",
    "obstructed_by_sprint120",
    "rotating conditional",
    "open",
    "complete=false",
    "clay=false",
    "clayNavierStokesPromoted=false",
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


def sprint121_ns_agda_files() -> list[Path]:
    return sorted(path for path in AGDA_DIR.glob("NSSprint" + SPRINT + "*.agda") if path.is_file())


def require_sprint121_ns_agda_module() -> Path:
    modules = sprint121_ns_agda_files()
    assert modules == [EXPECTED_FILE], (
        "Sprint 121 NS must have exactly one Agda file, "
        + relative(EXPECTED_FILE)
        + "; found: "
        + ", ".join(relative(path) for path in modules)
    )
    assert agda_module_name(EXPECTED_FILE) == EXPECTED_MODULE
    return EXPECTED_FILE


def identifier_pattern(identifier: str) -> re.Pattern[str]:
    return re.compile(r"(?<![A-Za-z0-9_])" + re.escape(identifier) + r"(?![A-Za-z0-9_])")


def bool_assignment_pattern(identifier: str, value: bool) -> re.Pattern[str]:
    agda_value = BOOL_TRUE if value else BOOL_FALSE
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


def marker_failures(path: Path) -> list[str]:
    text = read_text(path)
    failures: list[str] = []
    for label, pattern in AGDA_MARKER_PATTERNS.items():
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


def payload_text(payloads: list[Any]) -> str:
    return json.dumps(payloads, sort_keys=True)


def route_payloads(payloads: list[Any], required_terms: tuple[str, ...]) -> list[dict[str, Any]]:
    matches: list[dict[str, Any]] = []
    for value in json_values(payloads):
        if not isinstance(value, dict):
            continue
        text = json.dumps(value, sort_keys=True).lower()
        if all(term.lower() in text for term in required_terms):
            matches.append(value)
    return matches


def route_has_status(payloads: list[Any], required_terms: tuple[str, ...], status: str) -> bool:
    return any(status.lower() in json.dumps(payload, sort_keys=True).lower() for payload in route_payloads(payloads, required_terms))


def no_complete_or_clay_route(payloads: list[Any]) -> bool:
    for value in json_values(payloads):
        if not isinstance(value, dict):
            continue
        route_text = json.dumps(value, sort_keys=True).lower()
        if "route" not in route_text:
            continue
        complete = value.get("complete", value.get("clay_complete", value.get("clayComplete")))
        clay = value.get("clay", value.get("clay_promoted", value.get("clay_navier_stokes_promoted")))
        if complete is True or clay is True:
            return False
    return True


def run_classifier(tmp_path: Path) -> tuple[subprocess.CompletedProcess[str], list[Any], str]:
    assert CLASSIFIER.exists(), "Sprint121 NS rotating route classifier is missing"

    out_dir = tmp_path / "ns_sprint121_rotating_route_classifier"
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


def test_rotating_route_classifier_exits_1_and_recommends_persistence_bound(
    tmp_path: Path,
) -> None:
    result, payloads, output_text = run_classifier(tmp_path)

    assert result.returncode == 1, output_text
    assert RECOMMENDED_NEXT_LEMMA in payload_text(payloads), output_text
    assert re.search(
        r'"recommended_next_lemma"\s*:\s*"' + re.escape(RECOMMENDED_NEXT_LEMMA) + r'"',
        payload_text(payloads),
    ), output_text


def test_rotating_route_classifier_marks_route_statuses_and_no_completion(
    tmp_path: Path,
) -> None:
    result, payloads, output_text = run_classifier(tmp_path)

    assert result.returncode == 1, output_text
    assert route_has_status(payloads, (CONSTANT_LINEAR_ROUTE,), CONSTANT_LINEAR_STATUS), output_text
    assert route_has_status(payloads, ROTATING_TERMS, "open"), output_text
    assert no_complete_or_clay_route(payloads), output_text


def test_everything_imports_sprint121_ns_rotating_strain_receipt_once() -> None:
    require_sprint121_ns_agda_module()
    everything = read_text(EVERYTHING)

    sprint121_import = "import " + EXPECTED_MODULE
    imports = re.findall(
        r"^\s*" + re.escape(sprint121_import) + r"\s*$",
        everything,
        re.MULTILINE,
    )

    assert imports, "DASHI/Everything.agda is missing import: " + EXPECTED_MODULE
    assert len(imports) == 1, "DASHI/Everything.agda imports more than once: " + EXPECTED_MODULE


def test_sprint121_ns_agda_receipt_strings_and_false_clay_promotion() -> None:
    path = require_sprint121_ns_agda_module()
    text = read_text(path)
    compact_text = re.sub(r"\s+", "", text)
    missing_anchors = [anchor for anchor in REQUIRED_ANCHORS if not identifier_pattern(anchor).search(text)]
    missing_strings = [
        required
        for required in REQUIRED_RECEIPT_STRINGS
        if required not in text and required not in compact_text
    ]
    failures = marker_failures(path)

    assert re.search(r"^\s*module\s+" + re.escape(EXPECTED_MODULE) + r"\s+where\s*$", text, re.MULTILINE), (
        relative(path) + " must declare module " + EXPECTED_MODULE
    )
    assert not missing_anchors, relative(path) + " is missing Sprint 121 anchors:\n" + "\n".join(missing_anchors)
    assert not missing_strings, relative(path) + " is missing Sprint 121 strings:\n" + "\n".join(missing_strings)
    assert bool_assignment_pattern(PROMOTION_FLAG, False).search(text), (
        relative(path) + " must explicitly keep " + PROMOTION_FLAG + " = false"
    )
    assert not bool_assignment_pattern(PROMOTION_FLAG, True).search(text), (
        relative(path) + " unexpectedly promotes Clay completion"
    )
    assert not failures, "Sprint 121 NS Agda surface has marker issues:\n" + "\n".join(failures)
