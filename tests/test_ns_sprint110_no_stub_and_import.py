from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "110"
EXPECTED_STEM = "NSSprint" + SPRINT + "BaseExpSmoothFunction"
EXPECTED_MODULE = "DASHI.Physics.Closure." + EXPECTED_STEM
EXPECTED_FILE = AGDA_DIR / (EXPECTED_STEM + ".agda")

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_OPEN_WORK = "TO" + "DO"
TOKEN_INCOMPLETE = "st" + "ub"
TOKEN_GAP = "ho" + "le"
TOKEN_TRUE = "tr" + "ue"
TOKEN_FALSE = "fa" + "lse"
PROMOTION_FLAG = "clay" + "Navier" + "Stokes" + "Promoted"

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
    "gap wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_GAP + r"s?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "Agda gap start": re.compile(re.escape("{" + "!")),
    "Agda gap end": re.compile(re.escape("!" + "}")),
    "Agda gap assignment": re.compile(r"=\s*\?(?![A-Za-z0-9_])"),
}

SPRINT109_ANCHORS = (
    "NSSprint109SmoothCompactSupportWitness",
    "canonicalNSSprint109SmoothCompactSupportWitness",
    "Sprint109BaseExpSmoothFunctionAnchor",
    "canonicalSprint109BaseExpSmoothFunctionAnchor",
)

EXACT_SUBGATE_NAMES = (
    "ExpNegativeInverseSeedDefinition",
    "SmoothnessOnPositiveRadiusDomain",
    "DerivativeHierarchyPolynomialOverPower",
    "PositiveInteriorNonzeroWitness",
    "NonCircularBaseExpSource",
)

REQUIRED_FALSE_FLAGS = (
    "expNegativeInverseSeedDefinitionClosed",
    "smoothnessOnPositiveRadiusDomainClosed",
    "derivativeHierarchyPolynomialOverPowerClosed",
    "positiveInteriorNonzeroWitnessClosed",
    "nonCircularBaseExpSourceClosed",
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
    PROMOTION_FLAG,
)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def agda_module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO_ROOT).with_suffix("").parts)


def sprint110_ns_agda_files() -> list[Path]:
    return sorted(path for path in AGDA_DIR.glob("NSSprint" + SPRINT + "*.agda") if path.is_file())


def require_sprint110_ns_agda_module() -> Path:
    modules = sprint110_ns_agda_files()
    assert modules == [EXPECTED_FILE], (
        "Sprint 110 NS must have exactly one Agda file, "
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


def test_everything_imports_sprint110_ns_base_exp_smooth_function_once() -> None:
    require_sprint110_ns_agda_module()
    everything = read_text(EVERYTHING)
    imports = re.findall(
        r"^\s*import\s+" + re.escape(EXPECTED_MODULE) + r"\s*$",
        everything,
        re.MULTILINE,
    )

    assert imports, "DASHI/Everything.agda is missing import: " + EXPECTED_MODULE
    assert len(imports) == 1, "DASHI/Everything.agda imports more than once: " + EXPECTED_MODULE


def test_sprint110_ns_agda_file_exists_and_has_no_incomplete_markers() -> None:
    path = require_sprint110_ns_agda_module()
    text = read_text(path)
    failures = [
        f"{relative(path)}:{line_for_offset(text, match.start())}: {label}"
        for label, pattern in FORBIDDEN_PATTERNS.items()
        for match in pattern.finditer(text)
    ]

    assert not failures, "Forbidden Sprint 110 NS Agda surface:\n" + "\n".join(failures)


def test_sprint110_ns_agda_module_contains_sprint109_anchor_and_five_subgate_names() -> None:
    path = require_sprint110_ns_agda_module()
    text = read_text(path)
    required = SPRINT109_ANCHORS + EXACT_SUBGATE_NAMES
    missing = [name for name in required if not identifier_pattern(name).search(text)]

    assert not missing, relative(path) + " is missing Sprint 110 anchor/subgate names:\n" + "\n".join(missing)


def test_sprint110_ns_agda_module_keeps_required_downstream_flags_false() -> None:
    path = require_sprint110_ns_agda_module()
    text = read_text(path)
    missing_false = [
        flag for flag in REQUIRED_FALSE_FLAGS if not bool_assignment_pattern(flag, False).search(text)
    ]
    unexpected_true = [
        flag for flag in REQUIRED_FALSE_FLAGS if bool_assignment_pattern(flag, True).search(text)
    ]

    assert not missing_false, (
        relative(path) + " must explicitly set Sprint 110 downstream flags false:\n" + "\n".join(missing_false)
    )
    assert not unexpected_true, (
        relative(path) + " unexpectedly sets downstream/promotion flags true:\n" + "\n".join(unexpected_true)
    )
    assert bool_assignment_pattern(PROMOTION_FLAG, False).search(text), (
        relative(path) + " must explicitly keep " + PROMOTION_FLAG + " = " + TOKEN_FALSE
    )
    assert not bool_assignment_pattern(PROMOTION_FLAG, True).search(text), (
        relative(path) + " must never set " + PROMOTION_FLAG + " = " + TOKEN_TRUE
    )
