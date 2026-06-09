from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "96"
AGDA_PREFIX = "NSSprint" + SPRINT

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_TODO = "TO" + "DO"
TOKEN_STUB = "st" + "ub"
TOKEN_ADMIT = "ad" + "mit"
TOKEN_PLACEHOLDER = "place" + "holder"
TOKEN_FUTURE_PROOF = "future" + r"\s+" + "proof"

FORBIDDEN_PATTERNS = {
    "unproved axiom marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_POSTULATE + r"(?![A-Za-z0-9_])"
    ),
    "open work marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_TODO + r"(?![A-Za-z0-9_])"
    ),
    "stub wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_STUB + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "admit wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_ADMIT + r"(?:ted|s)?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "placeholder wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_PLACEHOLDER + r"s?(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "future proof phrasing": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_FUTURE_PROOF + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "Agda hole start": re.compile(r"\{!"),
    "Agda hole end": re.compile(r"!\}"),
    "Agda hole assignment": re.compile(r"=\s*\?(?![A-Za-z0-9_])"),
}

REQUIRED_ANCHORS = (
    "canonicalNSSprint96KStarCollapseMechanismConstraints",
    "FiniteTimeKStarCollapseMechanismCandidate",
    "EnergyCascadeDirection",
    "LowModeConcentrationWitness",
    "ViscousDampingCompatibility",
    "SingularityExtractionBridge",
    "KStarCollapseMechanismConstraints",
    "KStarCollapseMechanismResiduals",
    "failClosedKStarCollapseConstraints",
)

FALSE_CLOSURE_FLAGS = (
    "kStarCollapseMechanismClosed",
    "optionBFiniteTimeKStarCollapseClosed",
    "lowModeEnergyConcentrationMechanism",
    "viscousDampingOvercomeMechanism",
    "scalingCompatibleSelfSimilarity",
    "singularityExtractionWithoutCriterionFailure",
)

TRUE_CLOSURE_FLAGS = (
    "kStarCollapseConstraintLedgerClosed",
    "failClosedKStarCollapseConstraints",
)

CLAY_PROMOTED_TRUE_PATTERN = re.compile(
    r"(?<![A-Za-z0-9_])"
    r"clayNavierStokesPromoted"
    r"(?![A-Za-z0-9_])"
    r"(?:\s*:\s*[^\n=]+)?\s*=\s*true(?![A-Za-z0-9_])",
    re.MULTILINE,
)


def sprint96_ns_agda_files() -> list[Path]:
    return sorted(path for path in AGDA_DIR.glob(AGDA_PREFIX + "*.agda") if path.is_file())


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def relative(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def agda_module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO_ROOT).with_suffix("").parts)


def require_single_sprint96_ns_agda_module() -> Path:
    modules = sprint96_ns_agda_files()
    assert modules, (
        "missing Sprint 96 NS Agda module under "
        "DASHI/Physics/Closure/NSSprint96*.agda"
    )
    assert len(modules) == 1, (
        "expected exactly one Sprint 96 NS Agda module, found: "
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


def test_sprint96_ns_agda_module_exists_exactly_once_and_has_no_incomplete_markers() -> None:
    path = require_single_sprint96_ns_agda_module()
    text = read_text(path)

    failures: list[str] = []
    for label, pattern in FORBIDDEN_PATTERNS.items():
        for match in pattern.finditer(text):
            failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")

    assert not failures, "Forbidden Sprint 96 NS Agda surface:\n" + "\n".join(failures)


def test_sprint96_ns_agda_module_contains_required_kstar_collapse_constraint_anchors() -> None:
    path = require_single_sprint96_ns_agda_module()
    text = read_text(path)

    missing = [
        anchor for anchor in REQUIRED_ANCHORS if not identifier_pattern(anchor).search(text)
    ]

    assert not missing, relative(path) + " is missing Sprint 96 anchors:\n" + "\n".join(missing)


def test_sprint96_ns_agda_module_does_not_promote_clay_navier_stokes() -> None:
    path = require_single_sprint96_ns_agda_module()
    text = read_text(path)

    match = CLAY_PROMOTED_TRUE_PATTERN.search(text)
    assert match is None, (
        f"{relative(path)}:{line_for_offset(text, match.start())}: "
        "clayNavierStokesPromoted must not be true"
    )
    assert bool_assignment_pattern("clayNavierStokesPromoted", False).search(text), (
        relative(path) + " must explicitly keep clayNavierStokesPromoted false"
    )


def test_sprint96_ns_agda_module_keeps_collapse_mechanism_boundaries_false() -> None:
    path = require_single_sprint96_ns_agda_module()
    text = read_text(path)

    missing_false = [
        flag for flag in FALSE_CLOSURE_FLAGS if not bool_assignment_pattern(flag, False).search(text)
    ]
    unexpected_true = [
        flag for flag in FALSE_CLOSURE_FLAGS if bool_assignment_pattern(flag, True).search(text)
    ]

    assert not missing_false, (
        relative(path)
        + " must explicitly keep Sprint 96 boundary/collapse mechanisms false:\n"
        + "\n".join(missing_false)
    )
    assert not unexpected_true, (
        relative(path)
        + " unexpectedly closes Sprint 96 boundary/collapse mechanisms:\n"
        + "\n".join(unexpected_true)
    )


def test_sprint96_ns_agda_module_closes_only_constraint_ledger() -> None:
    path = require_single_sprint96_ns_agda_module()
    text = read_text(path)

    missing_true = [
        flag for flag in TRUE_CLOSURE_FLAGS if not bool_assignment_pattern(flag, True).search(text)
    ]

    assert not missing_true, (
        relative(path)
        + " must explicitly close only the Sprint 96 K* collapse constraint ledger:\n"
        + "\n".join(missing_true)
    )


def test_everything_imports_sprint96_ns_agda_module() -> None:
    path = require_single_sprint96_ns_agda_module()
    module = agda_module_name(path)
    everything = read_text(EVERYTHING)

    assert re.search(
        r"^\s*import\s+" + re.escape(module) + r"\s*$",
        everything,
        re.MULTILINE,
    ), "DASHI/Everything.agda is missing import: " + module
