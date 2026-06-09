from __future__ import annotations

import re
from collections.abc import Iterable
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "100"
AGDA_PREFIX = "NSSprint" + SPRINT

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
}

REQUIRED_ANCHORS = (
    "NSSprint100TimeIntegratedFluxSurplus",
    "canonicalNSSprint100TimeIntegratedFluxSurplus",
    "canonicalNSSprint100TimeIntegratedFluxSurplusReceipt",
    "canonicalSprint100TimeIntegratedFluxSurplusFlags",
    "TimeIntegratedFluxSurplus",
    "MissingTimeIntegratedFluxSurplusObject",
    "SignedLowModeFluxLowerBound",
    "FluxDissipationBalance",
    "PositiveSurplusWindow",
    "LerayEnergyFluxBudget",
    "NonCircularSurplusSource",
    "requiredTimeIntegratedFluxSurplusObjects",
    "timeIntegratedFluxSurplusLedgerClosed",
    "timeIntegratedFluxSurplusClosed",
    "residenceTimeAgainstViscosityClosed",
    "finiteTimeKStarCollapseClosed",
    "clayNavierStokesPromoted",
    "failClosedTimeIntegratedFluxSurplus",
    "canonicalSprint99FluxSurplusAnchor",
    "canonicalTimeIntegratedFluxSurplusStatus",
    "canonicalSignedLowModeFluxLowerBoundStatus",
    "canonicalFluxDissipationBalanceStatus",
    "canonicalPositiveSurplusWindowStatus",
    "canonicalLerayEnergyFluxBudgetStatus",
    "canonicalNonCircularSurplusSourceStatus",
)

FALSE_FLAGS = (
    "timeIntegratedFluxSurplusClosed",
    "residenceTimeAgainstViscosityClosed",
    "finiteTimeKStarCollapseClosed",
    "clayNavierStokesPromoted",
)

TRUE_FLAGS = (
    "timeIntegratedFluxSurplusLedgerClosed",
    "failClosedTimeIntegratedFluxSurplus",
)

DATA_DECL = re.compile(r"^\s*data\s+([A-Za-z][A-Za-z0-9_'-]*)\b")

CLAY_PROMOTED_TRUE_PATTERN = re.compile(
    r"(?<![A-Za-z0-9_])"
    r"clayNavierStokesPromoted"
    r"(?![A-Za-z0-9_])"
    r"(?:\s*:\s*[^\n=]+)?\s*=\s*true(?![A-Za-z0-9_])",
    re.MULTILINE,
)


def sprint100_ns_agda_files() -> list[Path]:
    return sorted(path for path in AGDA_DIR.glob(AGDA_PREFIX + "*.agda") if path.is_file())


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def agda_module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO_ROOT).with_suffix("").parts)


def require_single_sprint100_ns_agda_module() -> Path:
    modules = sprint100_ns_agda_files()
    assert modules, (
        "missing Sprint 100 NS Agda module under "
        "DASHI/Physics/Closure/NSSprint100*.agda"
    )
    assert len(modules) == 1, (
        "expected exactly one Sprint 100 NS Agda module, found: "
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


def test_sprint100_ns_agda_module_exists_exactly_once_and_has_no_incomplete_markers() -> None:
    path = require_single_sprint100_ns_agda_module()
    text = read_text(path)

    failures: list[str] = []
    for label, pattern in FORBIDDEN_PATTERNS.items():
        for match in pattern.finditer(text):
            failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")

    for line, datatype in empty_datatypes(text):
        failures.append(f"{relative(path)}:{line}: empty future-proof datatype {datatype!r}")

    assert not failures, "Forbidden Sprint 100 NS Agda surface:\n" + "\n".join(failures)


def test_sprint100_ns_agda_module_contains_required_time_integrated_flux_surplus_anchors() -> None:
    path = require_single_sprint100_ns_agda_module()
    text = read_text(path)

    missing = [
        anchor for anchor in REQUIRED_ANCHORS if not identifier_pattern(anchor).search(text)
    ]

    assert not missing, (
        relative(path)
        + " is missing Sprint 100 NS time-integrated flux surplus anchors:\n"
        + "\n".join(missing)
    )


def test_sprint100_ns_agda_module_keeps_time_integrated_flux_surplus_fail_closed() -> None:
    path = require_single_sprint100_ns_agda_module()
    text = read_text(path)

    missing_false = [
        flag for flag in FALSE_FLAGS if not bool_assignment_pattern(flag, False).search(text)
    ]
    unexpected_true = [
        flag for flag in FALSE_FLAGS if bool_assignment_pattern(flag, True).search(text)
    ]
    missing_true = [
        flag for flag in TRUE_FLAGS if not bool_assignment_pattern(flag, True).search(text)
    ]

    assert not missing_false, (
        relative(path)
        + " must explicitly keep Sprint 100 time-integrated flux surplus flags false:\n"
        + "\n".join(missing_false)
    )
    assert not unexpected_true, (
        relative(path)
        + " unexpectedly closes Sprint 100 time-integrated flux surplus flags:\n"
        + "\n".join(unexpected_true)
    )
    assert not missing_true, (
        relative(path)
        + " must explicitly record completed internal Sprint 100 ledger gates:\n"
        + "\n".join(missing_true)
    )


def test_sprint100_ns_agda_module_does_not_promote_clay_navier_stokes() -> None:
    path = require_single_sprint100_ns_agda_module()
    text = read_text(path)

    match = CLAY_PROMOTED_TRUE_PATTERN.search(text)
    assert match is None, (
        f"{relative(path)}:{line_for_offset(text, match.start())}: "
        "clayNavierStokesPromoted must not be true"
    )
    assert bool_assignment_pattern("clayNavierStokesPromoted", False).search(text), (
        relative(path) + " must explicitly keep clayNavierStokesPromoted false"
    )


def test_everything_imports_sprint100_ns_agda_module_once_after_integration() -> None:
    path = require_single_sprint100_ns_agda_module()
    module = agda_module_name(path)
    everything = read_text(EVERYTHING)

    imports = re.findall(
        r"^\s*import\s+" + re.escape(module) + r"\s*$",
        everything,
        re.MULTILINE,
    )

    assert imports, "DASHI/Everything.agda is missing import: " + module
    assert len(imports) == 1, "DASHI/Everything.agda imports more than once: " + module
