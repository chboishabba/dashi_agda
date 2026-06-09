from __future__ import annotations

import re
from collections.abc import Iterable
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
SCRIPTS_DIR = REPO_ROOT / "scripts"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "104"
AGDA_PREFIX = "NSSprint" + SPRINT
SCRIPT_PREFIX = "ns_sprint104"

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_TODO = "TO" + "DO"
TOKEN_STUB = "st" + "ub"
TOKEN_SKELETON = "skele" + "ton"
TOKEN_ADMIT = "ad" + "mit"
TOKEN_DUMMY = "dum" + "my"
TOKEN_FUTURE_PROOF = "future" + r"[\s-]*" + "proof"
TOKEN_HOLE = "ho" + "le"

FORBIDDEN_PATTERNS = {
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
    "dummy wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_DUMMY + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "deferred proof wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_FUTURE_PROOF + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "hole wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_HOLE + r"s?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "Agda hole start": re.compile(r"\{!"),
    "Agda hole end": re.compile(r"!\}"),
    "Agda hole assignment": re.compile(r"=\s*\?(?![A-Za-z0-9_])"),
    "Python ellipsis placeholder": re.compile(r"^\s*\.\.\.\s*(?:#.*)?$", re.MULTILINE),
    "Python pass placeholder": re.compile(r"^\s*pass\s*(?:#.*)?$", re.MULTILINE),
}

EXACT_SUBGATE_NAMES = (
    "DyadicShellEnergyDensity",
    "ConcentrationThresholdSelection",
    "ConcentrationLocusMeasurability",
    "ScaleLocalizedTightness",
    "NonCircularConcentrationMeasureSource",
)

FALSE_PROMOTION_FLAGS = (
    "clayNavierStokesPromoted",
)

DATA_DECL = re.compile(r"^\s*data\s+([A-Za-z][A-Za-z0-9_'-]*)\b")


def sprint104_ns_agda_files() -> list[Path]:
    return sorted(path for path in AGDA_DIR.glob(AGDA_PREFIX + "*.agda") if path.is_file())


def sprint104_ns_script_files() -> list[Path]:
    return sorted(path for path in SCRIPTS_DIR.glob(SCRIPT_PREFIX + "*.py") if path.is_file())


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def agda_module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO_ROOT).with_suffix("").parts)


def require_single_sprint104_ns_agda_module() -> Path:
    modules = sprint104_ns_agda_files()
    assert modules, (
        "missing Sprint 104 NS Agda module under "
        "DASHI/Physics/Closure/NSSprint104*.agda"
    )
    assert len(modules) == 1, (
        "expected exactly one Sprint 104 NS Agda module, found: "
        + ", ".join(relative(path) for path in modules)
    )
    return modules[0]


def identifier_pattern(identifier: str) -> re.Pattern[str]:
    return re.compile(
        r"(?<![A-Za-z0-9_])" + re.escape(identifier) + r"(?![A-Za-z0-9_])"
    )


def bool_assignment_pattern(identifier: str, value: bool) -> re.Pattern[str]:
    agda_value = "true" if value else "false"
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
    for label, pattern in FORBIDDEN_PATTERNS.items():
        for match in pattern.finditer(text):
            failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")

    if path.suffix == ".agda":
        for line, datatype in empty_datatypes(text):
            failures.append(f"{relative(path)}:{line}: empty datatype {datatype!r}")

    return failures


def test_sprint104_ns_agda_module_exists_exactly_once_and_has_no_incomplete_markers() -> None:
    path = require_single_sprint104_ns_agda_module()
    failures = incomplete_marker_failures(path)

    assert not failures, "Forbidden Sprint 104 NS Agda surface:\n" + "\n".join(failures)


def test_sprint104_ns_scripts_exist_and_have_no_incomplete_markers() -> None:
    scripts = sprint104_ns_script_files()
    assert scripts, "missing Sprint 104 NS scripts under scripts/ns_sprint104*.py"

    failures = [
        failure
        for path in scripts
        for failure in incomplete_marker_failures(path)
    ]

    assert not failures, "Forbidden Sprint 104 NS script surface:\n" + "\n".join(failures)


def test_sprint104_ns_agda_module_contains_exact_subgate_names() -> None:
    path = require_single_sprint104_ns_agda_module()
    text = read_text(path)

    missing = [
        name for name in EXACT_SUBGATE_NAMES if not identifier_pattern(name).search(text)
    ]

    assert not missing, (
        relative(path)
        + " is missing exact Sprint 104 strain-compression subgate names:\n"
        + "\n".join(missing)
    )


def test_sprint104_ns_agda_module_keeps_clay_navier_stokes_promotion_false() -> None:
    path = require_single_sprint104_ns_agda_module()
    text = read_text(path)

    missing_false = [
        flag for flag in FALSE_PROMOTION_FLAGS if not bool_assignment_pattern(flag, False).search(text)
    ]
    unexpected_true = [
        flag for flag in FALSE_PROMOTION_FLAGS if bool_assignment_pattern(flag, True).search(text)
    ]

    assert not missing_false, (
        relative(path)
        + " must explicitly keep Sprint 104 NS promotion flags false:\n"
        + "\n".join(missing_false)
    )
    assert not unexpected_true, (
        relative(path)
        + " unexpectedly promotes Sprint 104 NS closure:\n"
        + "\n".join(unexpected_true)
    )


def test_everything_imports_sprint104_ns_agda_module_once_after_integration() -> None:
    path = require_single_sprint104_ns_agda_module()
    module_name = agda_module_name(path)
    everything = read_text(EVERYTHING)

    imports = re.findall(
        r"^\s*import\s+" + re.escape(module_name) + r"\s*$",
        everything,
        re.MULTILINE,
    )

    assert imports, "DASHI/Everything.agda is missing import: " + module_name
    assert len(imports) == 1, "DASHI/Everything.agda imports more than once: " + module_name
