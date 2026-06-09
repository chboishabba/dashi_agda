from __future__ import annotations

import re
from collections.abc import Iterable
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
SCRIPT_DIR = REPO_ROOT / "scripts"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

SPRINT = "114"
PREVIOUS_MODULE = "DASHI.Physics.Closure.NSSprint113CrowPersistenceUnderNSEvolution"
EXPECTED_STEM = "NSSprint" + SPRINT + "ThinCoreCrowReconnectionWindow"
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
    "NSSprint113CrowPersistenceUnderNSEvolution",
    "canonicalNSSprint113CrowPersistenceUnderNSEvolution",
    "ThinCoreCrowRegimeCorrection",
    "canonicalThinCoreCrowRegimeCorrection",
    "ReconnectionWindowBlocker",
    "canonicalReconnectionWindowBlocker",
    PROMOTION_FLAG,
)

REQUIRED_RECEIPT_ANCHORS = (
    "nsSprint" + SPRINT + "ThinCoreCrowReconnectionWindowReceipt",
    "canonicalThinCoreCrowReconnectionWindowReceipt",
)

REQUIRED_BLOCKER_STRINGS = (
    "thin-core Crow reconnection-window correction",
    "thin-core Crow-dominant comparison regime",
    "ReconnectionWindowLowerBound / finite flux surplus",
)

TRUE_FLAGS = (
    "sprint114ThinCoreCorrectionLedgerClosed",
    "sprint112ThickCoreConditionCorrected",
    "thinCoreCrowDominanceRegimeClosed",
    "ellipticBackreactionBoundClosed",
)

FALSE_FLAGS = (
    "reconnectionWindowLowerBoundClosed",
    "viscousDecayWindowClosed",
    "nonlinearDeformationControlClosed",
    "positiveFluxAccumulationWindowClosed",
    "finiteTimeFluxSurplusFromCrowDominance",
    "finiteKStarCollapseClosed",
    "strainCompressionAtHighFrequencyConcentrationPointsClosed",
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


def sprint114_ns_agda_files() -> list[Path]:
    return sorted(path for path in AGDA_DIR.glob("NSSprint" + SPRINT + "*.agda") if path.is_file())


def sprint114_ns_script_files() -> list[Path]:
    return sorted(path for path in SCRIPT_DIR.glob("ns_sprint" + SPRINT + "*.py") if path.is_file())


def sprint114_ns_surfaces() -> list[Path]:
    return sprint114_ns_agda_files() + sprint114_ns_script_files()


def require_sprint114_ns_agda_module() -> Path:
    modules = sprint114_ns_agda_files()
    assert modules == [EXPECTED_FILE], (
        "Sprint 114 NS must have exactly one Agda file, "
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


def test_sprint114_ns_agda_file_exists_and_has_no_incomplete_markers() -> None:
    path = require_sprint114_ns_agda_module()
    failures = incomplete_marker_failures(path)

    assert not failures, "Forbidden Sprint 114 NS Agda surface:\n" + "\n".join(failures)


def test_sprint114_ns_agda_and_script_surfaces_have_no_forbidden_markers() -> None:
    require_sprint114_ns_agda_module()
    surfaces = sprint114_ns_surfaces()
    assert surfaces, "Sprint 114 NS Agda/scripts surfaces are missing"

    failures = [failure for path in surfaces for failure in incomplete_marker_failures(path)]

    assert not failures, "Forbidden Sprint 114 NS Agda/scripts surface:\n" + "\n".join(failures)


def test_everything_imports_sprint114_ns_after_sprint113_once() -> None:
    require_sprint114_ns_agda_module()
    everything = read_text(EVERYTHING)

    previous_import = "import " + PREVIOUS_MODULE
    sprint114_import = "import " + EXPECTED_MODULE
    imports = re.findall(
        r"^\s*" + re.escape(sprint114_import) + r"\s*$",
        everything,
        re.MULTILINE,
    )

    assert imports, "DASHI/Everything.agda is missing import: " + EXPECTED_MODULE
    assert len(imports) == 1, "DASHI/Everything.agda imports more than once: " + EXPECTED_MODULE
    assert previous_import in everything, "DASHI/Everything.agda is missing import: " + PREVIOUS_MODULE
    assert everything.index(previous_import) < everything.index(sprint114_import), (
        "DASHI/Everything.agda must import Sprint114 after Sprint113"
    )


def test_sprint114_ns_agda_module_contains_required_receipt_and_canonical_anchors() -> None:
    path = require_sprint114_ns_agda_module()
    text = read_text(path)
    required = REQUIRED_ANCHORS + REQUIRED_RECEIPT_ANCHORS
    missing = [anchor for anchor in required if not identifier_pattern(anchor).search(text)]

    assert not missing, relative(path) + " is missing Sprint 114 anchors:\n" + "\n".join(missing)


def test_sprint114_ns_agda_records_thin_core_and_reconnection_window_blockers() -> None:
    path = require_sprint114_ns_agda_module()
    text = read_text(path)
    missing = [blocker for blocker in REQUIRED_BLOCKER_STRINGS if blocker not in text]

    assert not missing, (
        relative(path)
        + " must record thin-core correction and reconnection-window blocker strings:\n"
        + "\n".join(missing)
    )


def test_sprint114_ns_agda_keeps_corrections_blocked_and_clay_promotion_false() -> None:
    path = require_sprint114_ns_agda_module()
    text = read_text(path)

    missing_true = [flag for flag in TRUE_FLAGS if not bool_assignment_pattern(flag, True).search(text)]
    unexpected_false = [flag for flag in TRUE_FLAGS if bool_assignment_pattern(flag, False).search(text)]
    missing_false = [flag for flag in FALSE_FLAGS if not bool_assignment_pattern(flag, False).search(text)]
    unexpected_true = [flag for flag in FALSE_FLAGS if bool_assignment_pattern(flag, True).search(text)]

    assert not missing_true, (
        relative(path) + " must explicitly record Sprint 114 receipt flags true:\n" + "\n".join(missing_true)
    )
    assert not unexpected_false, (
        relative(path) + " must not set Sprint 114 receipt flags false:\n" + "\n".join(unexpected_false)
    )
    assert not missing_false, (
        relative(path) + " must explicitly keep correction/downstream/Clay flags false:\n" + "\n".join(missing_false)
    )
    assert not unexpected_true, (
        relative(path) + " unexpectedly promotes correction/downstream/Clay flags true:\n" + "\n".join(unexpected_true)
    )
    assert bool_assignment_pattern(PROMOTION_FLAG, False).search(text), (
        relative(path) + " must explicitly keep " + PROMOTION_FLAG + " = " + TOKEN_FALSE
    )
    assert not bool_assignment_pattern(PROMOTION_FLAG, True).search(text), (
        relative(path) + " must never set " + PROMOTION_FLAG + " = " + TOKEN_TRUE
    )
