from __future__ import annotations

import re
from collections.abc import Iterable
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
SCRIPT_DIR = REPO_ROOT / "scripts"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "115"
PREVIOUS_MODULE = "DASHI.Physics.Closure.NSSprint114ThinCoreCrowReconnectionWindow"
EXPECTED_STEM = "NSSprint" + SPRINT + "ReconnectionFluxBudget"
EXPECTED_MODULE = "DASHI.Physics.Closure." + EXPECTED_STEM
EXPECTED_FILE = AGDA_DIR / (EXPECTED_STEM + ".agda")

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
PROMOTION_FLAG = "clay" + "Navier" + "Stokes" + "Promoted"

FORBIDDEN_SURFACE_PATTERNS = {
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
    "NSSprint114ThinCoreCrowReconnectionWindow",
    "canonicalNSSprint114ThinCoreCrowReconnectionWindow",
    "ReconnectionFluxBudgetFormulaLedger",
    "canonicalReconnectionFluxBudgetFormulaLedger",
    "Sprint115GateStatuses",
    "canonicalSprint115GateStatuses",
    "canonicalSprint115ReconnectionFluxBudgetFlags",
    PROMOTION_FLAG,
)

REQUIRED_RECEIPT_ANCHORS = (
    "nsSprint" + SPRINT + "ReconnectionFluxBudgetReceipt",
    "canonicalReconnectionFluxBudgetReceipt",
)

REQUIRED_FORMULAS = (
    "FluxBudget = integral_0_to_T_reconnect Pi_HH_to_L(t) dt",
    "T_reconnect ~ b^2 / Gamma",
    "integral_0_to_T_reconnect Pi_HH_to_L(t) dt",
    "Re_delta = Gamma / nu >> b^2 / delta^2",
    "FluxBudget >= KStarCollapseThreshold",
)

TRUE_FLAGS = (
    "sprint115ReconnectionFluxBudgetLedgerClosed",
    "sprint114ThinCoreCorrectionImported",
    "fluxIntegralFormulaRecorded",
    "reconnectionTimescaleRecorded",
    "viscousReynoldsConditionRecorded",
    "kstarCollapseThresholdRecorded",
)

FALSE_FLAGS = (
    "reconnectionWindowLowerBoundClosed",
    "positiveFluxAccumulationWindowClosed",
    "finiteTimeFluxSurplusFromCrowDominance",
    "finiteKStarCollapseClosed",
    "blowupCriterionBridgeClosed",
    PROMOTION_FLAG,
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


def sprint115_ns_agda_files() -> list[Path]:
    return sorted(path for path in AGDA_DIR.glob("NSSprint" + SPRINT + "*.agda") if path.is_file())


def sprint115_ns_script_files() -> list[Path]:
    return sorted(path for path in SCRIPT_DIR.glob("ns_sprint" + SPRINT + "*.py") if path.is_file())


def sprint115_ns_surfaces() -> list[Path]:
    return sprint115_ns_agda_files() + sprint115_ns_script_files()


def require_sprint115_ns_agda_module() -> Path:
    modules = sprint115_ns_agda_files()
    assert modules == [EXPECTED_FILE], (
        "Sprint 115 NS must have exactly one Agda file, "
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
    for label, pattern in FORBIDDEN_SURFACE_PATTERNS.items():
        for match in pattern.finditer(text):
            failures.append(f"{relative(path)}:{line_for_offset(text, match.start())}: {label}")

    if path.suffix == ".agda":
        for line, datatype in empty_datatypes(text):
            failures.append(f"{relative(path)}:{line}: empty datatype {datatype!r}")

    return failures


def test_sprint115_ns_agda_file_exists_with_expected_module_name() -> None:
    path = require_sprint115_ns_agda_module()
    text = read_text(path)

    assert re.search(r"^\s*module\s+" + re.escape(EXPECTED_MODULE) + r"\s+where\s*$", text, re.MULTILINE), (
        relative(path) + " must declare module " + EXPECTED_MODULE
    )


def test_everything_imports_sprint115_ns_after_sprint114_once() -> None:
    require_sprint115_ns_agda_module()
    everything = read_text(EVERYTHING)
    expected_import = "import " + EXPECTED_MODULE
    previous_import = "import " + PREVIOUS_MODULE
    imports = re.findall(
        r"^\s*" + re.escape(expected_import) + r"\s*$",
        everything,
        re.MULTILINE,
    )

    assert imports, "DASHI/Everything.agda is missing import: " + EXPECTED_MODULE
    assert len(imports) == 1, "DASHI/Everything.agda imports more than once: " + EXPECTED_MODULE
    assert previous_import in everything, "DASHI/Everything.agda is missing previous Sprint114 import"
    assert everything.index(previous_import) < everything.index(expected_import), (
        "DASHI/Everything.agda must import Sprint115 after Sprint114"
    )


def test_sprint115_ns_agda_contains_required_anchors_and_canonical_receipts() -> None:
    path = require_sprint115_ns_agda_module()
    text = read_text(path)
    required = REQUIRED_ANCHORS + REQUIRED_RECEIPT_ANCHORS
    missing = [name for name in required if not identifier_pattern(name).search(text)]

    assert not missing, relative(path) + " is missing Sprint 115 anchors:\n" + "\n".join(missing)


def test_sprint115_ns_agda_contains_required_reconnection_flux_formulas() -> None:
    path = require_sprint115_ns_agda_module()
    text = read_text(path)
    missing = [formula for formula in REQUIRED_FORMULAS if formula not in text]

    assert not missing, relative(path) + " is missing Sprint 115 formula strings:\n" + "\n".join(missing)


def test_sprint115_ns_agda_keeps_clay_promotion_false_and_budget_gates_fail_closed() -> None:
    path = require_sprint115_ns_agda_module()
    text = read_text(path)
    missing_true = [flag for flag in TRUE_FLAGS if not bool_assignment_pattern(flag, True).search(text)]
    missing_false = [flag for flag in FALSE_FLAGS if not bool_assignment_pattern(flag, False).search(text)]
    unexpected_true = [flag for flag in FALSE_FLAGS if bool_assignment_pattern(flag, True).search(text)]

    assert not missing_true, (
        relative(path) + " must explicitly close these Sprint 115 ledger flags:\n" + "\n".join(missing_true)
    )
    assert not missing_false, (
        relative(path) + " must explicitly keep these Sprint 115 gates false:\n" + "\n".join(missing_false)
    )
    assert not unexpected_true, (
        relative(path) + " unexpectedly closes fail-closed Sprint 115 gates:\n" + "\n".join(unexpected_true)
    )


def test_sprint115_ns_agda_and_scripts_have_no_forbidden_markers() -> None:
    surfaces = sprint115_ns_surfaces()
    assert surfaces, "Sprint 115 NS must have at least one Agda or script surface"
    failures = [failure for path in surfaces for failure in incomplete_marker_failures(path)]

    assert not failures, "Forbidden Sprint 115 NS surfaces:\n" + "\n".join(failures)
