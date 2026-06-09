from __future__ import annotations

import re
from collections.abc import Iterable
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "106"
EXPECTED_MODULE = "DASHI.Physics.Closure.NSSprint106LittlewoodPaleyShellProjector"
EXPECTED_FILE = AGDA_DIR / "NSSprint106LittlewoodPaleyShellProjector.agda"

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_TODO = "TO" + "DO"
TOKEN_STUB = "st" + "ub"
TOKEN_SKELETON = "skele" + "ton"
TOKEN_ADMIT = "ad" + "mit"
TOKEN_HOLE = "ho" + "le"

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
    "gap marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_HOLE + r"s?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "Agda gap start": re.compile(r"\{!"),
    "Agda gap end": re.compile(r"!\}"),
    "Agda question-mark placeholder": re.compile(r"=\s*\?(?![A-Za-z0-9_])"),
}

REQUIRED_ANCHORS = (
    "NSSprint106LittlewoodPaleyShellProjector",
    "canonicalNSSprint106LittlewoodPaleyShellProjector",
    "canonicalNSSprint106LittlewoodPaleyShellProjectorReceipt",
    "Sprint105LittlewoodPaleyShellProjectorAnchor",
    "canonicalSprint105LittlewoodPaleyShellProjectorAnchor",
    "LittlewoodPaleyShellProjectorDecomposition",
    "LittlewoodPaleyShellProjectorSplitsIntoFiveSubgates",
    "LittlewoodPaleyProjectorSubgateStatus",
    "canonicalLittlewoodPaleyShellProjectorDecompositionStatus",
    "SmoothDyadicCutoffPartition",
    "FourierMultiplierBoundedness",
    "LerayCompatibleProjection",
    "DivergenceFreeProjectionCommutation",
    "NonCircularProjectorConstruction",
    "requiredLittlewoodPaleyShellProjectorSubgates",
    "littlewoodPaleyShellProjectorDecompositionLedgerClosed",
    "smoothDyadicCutoffPartitionClosed",
    "fourierMultiplierBoundednessClosed",
    "lerayCompatibleProjectionClosed",
    "divergenceFreeProjectionCommutationClosed",
    "nonCircularProjectorConstructionClosed",
    "littlewoodPaleyShellProjectorClosed",
    "dyadicShellEnergyDensityClosed",
    "highFrequencyConcentrationMeasureClosed",
    "strainCompressionAtHighFrequencyConcentrationPointsClosed",
    "signedLowModeFluxLowerBoundClosed",
    "timeIntegratedFluxSurplusClosed",
    "finiteKStarCollapseClosed",
    "clayNavierStokesPromoted",
    "failClosedLittlewoodPaleyShellProjectorDecomposition",
)

EXACT_SUBGATE_NAMES = (
    "SmoothDyadicCutoffPartition",
    "FourierMultiplierBoundedness",
    "LerayCompatibleProjection",
    "DivergenceFreeProjectionCommutation",
    "NonCircularProjectorConstruction",
)

CLOSED_FALSE_FLAGS = (
    "smoothDyadicCutoffPartitionClosed",
    "fourierMultiplierBoundednessClosed",
    "lerayCompatibleProjectionClosed",
    "divergenceFreeProjectionCommutationClosed",
    "nonCircularProjectorConstructionClosed",
    "littlewoodPaleyShellProjectorClosed",
    "dyadicShellEnergyDensityClosed",
    "highFrequencyConcentrationMeasureClosed",
    "strainCompressionAtHighFrequencyConcentrationPointsClosed",
    "signedLowModeFluxLowerBoundClosed",
    "timeIntegratedFluxSurplusClosed",
    "finiteKStarCollapseClosed",
    "clayNavierStokesPromoted",
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


def sprint106_ns_agda_files() -> list[Path]:
    return sorted(path for path in AGDA_DIR.glob("NSSprint" + SPRINT + "*.agda") if path.is_file())


def require_sprint106_ns_agda_module() -> Path:
    modules = sprint106_ns_agda_files()
    assert modules, "missing Sprint 106 NS Agda module: " + relative(EXPECTED_FILE)
    assert modules == [EXPECTED_FILE], (
        "Sprint 106 NS must be exactly "
        + relative(EXPECTED_FILE)
        + "; found: "
        + ", ".join(relative(path) for path in modules)
    )
    assert agda_module_name(EXPECTED_FILE) == EXPECTED_MODULE
    return EXPECTED_FILE


def identifier_pattern(identifier: str) -> re.Pattern[str]:
    return re.compile(r"(?<![A-Za-z0-9_])" + re.escape(identifier) + r"(?![A-Za-z0-9_])")


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
    for label, pattern in FORBIDDEN_AGDA_PATTERNS.items():
        for match in pattern.finditer(text):
            failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")

    for line, datatype in empty_datatypes(text):
        failures.append(f"{relative(path)}:{line}: empty datatype {datatype!r}")

    return failures


def test_sprint106_ns_agda_file_exists_and_has_no_incomplete_markers() -> None:
    path = require_sprint106_ns_agda_module()
    failures = incomplete_marker_failures(path)

    assert not failures, "Forbidden Sprint 106 NS Agda surface:\n" + "\n".join(failures)


def test_everything_imports_sprint106_ns_littlewood_paley_shell_projector_once() -> None:
    require_sprint106_ns_agda_module()
    everything = read_text(EVERYTHING)

    imports = re.findall(
        r"^\s*import\s+" + re.escape(EXPECTED_MODULE) + r"\s*$",
        everything,
        re.MULTILINE,
    )

    assert imports, "DASHI/Everything.agda is missing import: " + EXPECTED_MODULE
    assert len(imports) == 1, "DASHI/Everything.agda imports more than once: " + EXPECTED_MODULE


def test_sprint106_ns_agda_module_contains_required_anchors() -> None:
    path = require_sprint106_ns_agda_module()
    text = read_text(path)

    missing = [anchor for anchor in REQUIRED_ANCHORS if not identifier_pattern(anchor).search(text)]

    assert not missing, relative(path) + " is missing Sprint 106 anchors:\n" + "\n".join(missing)


def test_sprint106_ns_agda_module_contains_exact_subgate_names() -> None:
    path = require_sprint106_ns_agda_module()
    text = read_text(path)

    missing = [subgate for subgate in EXACT_SUBGATE_NAMES if not identifier_pattern(subgate).search(text)]

    assert not missing, (
        relative(path)
        + " is missing exact Sprint 106 Littlewood-Paley shell-projector subgate names:\n"
        + "\n".join(missing)
    )


def test_sprint106_ns_agda_module_keeps_required_flags_closed_false() -> None:
    path = require_sprint106_ns_agda_module()
    text = read_text(path)

    missing_false = [
        flag for flag in CLOSED_FALSE_FLAGS if not bool_assignment_pattern(flag, False).search(text)
    ]
    unexpected_true = [
        flag for flag in CLOSED_FALSE_FLAGS if bool_assignment_pattern(flag, True).search(text)
    ]

    assert not missing_false, (
        relative(path) + " must explicitly set Sprint 106 closed flags false:\n" + "\n".join(missing_false)
    )
    assert not unexpected_true, (
        relative(path) + " unexpectedly sets closed/promotion flags true:\n" + "\n".join(unexpected_true)
    )
