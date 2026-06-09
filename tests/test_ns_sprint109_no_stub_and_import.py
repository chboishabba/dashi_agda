from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "109"
EXPECTED_MODULE = "DASHI.Physics.Closure.NSSprint109SmoothCompactSupportWitness"
EXPECTED_FILE = AGDA_DIR / "NSSprint109SmoothCompactSupportWitness.agda"

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_OPEN_WORK = "TO" + "DO"
TOKEN_INCOMPLETE = "st" + "ub"

FORBIDDEN_PATTERNS = {
    "unproved axiom marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_POSTULATE + r"(?![A-Za-z0-9_])"
    ),
    "open work marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_OPEN_WORK + r"(?![A-Za-z0-9_])"
    ),
    "incomplete implementation marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_INCOMPLETE + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
}

SPRINT108_ANCHORS = (
    "NSSprint108RadialBumpFunctionConstruction",
    "canonicalNSSprint108RadialBumpFunctionConstruction",
    "Sprint108SmoothCompactSupportWitnessAnchor",
    "canonicalSprint108SmoothCompactSupportWitnessAnchor",
)

EXACT_SUBGATE_NAMES = (
    "BaseExpSmoothFunction",
    "BoundaryFlatnessAtUnitRadius",
    "CompactSupportCutoffDefinition",
    "SmoothnessAcrossSupportBoundary",
    "NonCircularCompactSupportSource",
)

REQUIRED_FALSE_FLAGS = (
    "baseExpSmoothFunctionClosed",
    "boundaryFlatnessAtUnitRadiusClosed",
    "compactSupportCutoffDefinitionClosed",
    "smoothnessAcrossSupportBoundaryClosed",
    "nonCircularCompactSupportSourceClosed",
    "smoothCompactSupportWitnessClosed",
    "radialBumpFunctionConstructionClosed",
    "smoothDyadicCutoffPartitionClosed",
    "littlewoodPaleyShellProjectorClosed",
    "dyadicShellEnergyDensityClosed",
    "highFrequencyConcentrationMeasureClosed",
    "strainCompressionAtHighFrequencyConcentrationPointsClosed",
    "signedLowModeFluxLowerBoundClosed",
    "timeIntegratedFluxSurplusClosed",
    "finiteKStarCollapseClosed",
    "clayNavierStokesPromoted",
)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def agda_module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO_ROOT).with_suffix("").parts)


def sprint109_ns_agda_files() -> list[Path]:
    return sorted(path for path in AGDA_DIR.glob("NSSprint" + SPRINT + "*.agda") if path.is_file())


def require_sprint109_ns_agda_module() -> Path:
    modules = sprint109_ns_agda_files()
    assert modules == [EXPECTED_FILE], (
        "Sprint 109 NS must have exactly one Agda file, "
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


def test_sprint109_ns_agda_file_exists_and_has_no_incomplete_markers() -> None:
    path = require_sprint109_ns_agda_module()
    text = read_text(path)
    failures = [
        f"{relative(path)}:{line_for_offset(text, match.start())}: {label}"
        for label, pattern in FORBIDDEN_PATTERNS.items()
        for match in pattern.finditer(text)
    ]

    assert not failures, "Forbidden Sprint 109 NS Agda surface:\n" + "\n".join(failures)


def test_everything_imports_sprint109_ns_smooth_compact_support_witness_once() -> None:
    require_sprint109_ns_agda_module()
    everything = read_text(EVERYTHING)
    imports = re.findall(
        r"^\s*import\s+" + re.escape(EXPECTED_MODULE) + r"\s*$",
        everything,
        re.MULTILINE,
    )

    assert imports, "DASHI/Everything.agda is missing import: " + EXPECTED_MODULE
    assert len(imports) == 1, "DASHI/Everything.agda imports more than once: " + EXPECTED_MODULE


def test_sprint109_ns_agda_module_contains_sprint108_anchor_and_five_subgate_names() -> None:
    path = require_sprint109_ns_agda_module()
    text = read_text(path)
    required = SPRINT108_ANCHORS + EXACT_SUBGATE_NAMES
    missing = [name for name in required if not identifier_pattern(name).search(text)]

    assert not missing, relative(path) + " is missing Sprint 109 anchor/subgate names:\n" + "\n".join(missing)


def test_sprint109_ns_agda_module_keeps_required_downstream_flags_false() -> None:
    path = require_sprint109_ns_agda_module()
    text = read_text(path)
    missing_false = [
        flag for flag in REQUIRED_FALSE_FLAGS if not bool_assignment_pattern(flag, False).search(text)
    ]
    unexpected_true = [
        flag for flag in REQUIRED_FALSE_FLAGS if bool_assignment_pattern(flag, True).search(text)
    ]

    assert not missing_false, (
        relative(path) + " must explicitly set Sprint 109 downstream flags false:\n" + "\n".join(missing_false)
    )
    assert not unexpected_true, (
        relative(path) + " unexpectedly sets downstream/promotion flags true:\n" + "\n".join(unexpected_true)
    )
    assert bool_assignment_pattern("clayNavierStokesPromoted", False).search(text), (
        relative(path) + " must explicitly keep clayNavierStokesPromoted = false"
    )
    assert not bool_assignment_pattern("clayNavierStokesPromoted", True).search(text), (
        relative(path)
        + " must never set "
        + "clayNavierStokesPromoted"
        + " = "
        + "true"
    )
