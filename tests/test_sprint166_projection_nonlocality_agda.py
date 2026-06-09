from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
CLOSURE_DIR = REPO_ROOT / "DASHI" / "Physics" / "Closure"
OBLIGATION_INDEX = REPO_ROOT / "DASHI" / "Promotion" / "ObligationIndex.agda"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

CONTROL_CARD_KEYS = ("O:", "R:", "C:", "S:", "L:", "P:", "G:", "F:")
MODULE_PREFIX = "DASHI.Physics.Closure."

P0_ANCHOR_TERMS = (
    "P0",
    "P0ClayFiniteHodgeNSTopologicalStackReceipt",
    "canonicalP0ClayFiniteHodgeNSTopologicalStackReceipt",
)
SPRINT164_ANCHOR_TERMS = (
    "Sprint164",
    "NSSprint164MicrolocalTopologicalBridgeBoundaryReceipt",
    "MicrolocalTopologicalBridgeBoundary",
)
TARGET_NAME_TERMS = (
    "ProjectionNonlocality",
    "PressureNonlocality",
    "P0",
    "Sprint164",
)
TRUE_TARGET_FIELD_TERMS = (
    ("projection", "nonlocality", "target", "recorded"),
    ("pressure", "nonlocality", "target", "recorded"),
    ("nonlocal", "projection", "target", "recorded"),
    ("p0", "anchor"),
    ("sprint164", "anchor"),
)
FALSE_THEOREM_PROMOTION_TERMS = (
    ("projection", "nonlocality", "theorem"),
    ("pressure", "nonlocality", "closure"),
    ("mechanism", "exhaustion", "full", "clay"),
    ("full", "clay", "ns", "solved"),
    ("clay", "navier", "stokes", "promoted"),
    ("terminal", "promotion"),
)


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def read_text(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT).as_posix()}"
    return path.read_text(encoding="utf-8", errors="replace")


def bool_assignments(text: str) -> list[tuple[str, str]]:
    typed_assignments = re.findall(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*Bool\s*\n\1\s*=\s*(true|false)\b",
        text,
    )
    record_assignments = re.findall(
        r"(?:^|\s;\s*)\b([A-Za-z][A-Za-z0-9_']*)\s*=\s*(true|false)\b",
        text,
    )
    return typed_assignments + [
        assignment for assignment in record_assignments if assignment not in typed_assignments
    ]


def has_evidence(
    text: str,
    *,
    name_terms: tuple[str, ...],
    value: bool,
) -> bool:
    expected = "true" if value else "false"
    for name, assigned in bool_assignments(text):
        if assigned == expected and all(
            normalize(term) in normalize(name) for term in name_terms
        ):
            return True

    proof_decl = re.compile(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*"
        r"([A-Za-z][A-Za-z0-9_']*)\s*≡\s*"
        rf"{expected}\b"
    )
    for match in proof_decl.finditer(text):
        normalized_evidence = normalize(" ".join(match.groups()))
        if all(normalize(term) in normalized_evidence for term in name_terms):
            return True
    return False


def sprint166_receipts() -> list[Path]:
    return sorted(
        path
        for path in CLOSURE_DIR.glob("*Sprint166*.agda")
        if "projection" in normalize(path.stem)
        and "nonlocal" in normalize(path.stem)
        and "receipt" in normalize(path.stem)
    )


def module_name_for(path: Path) -> str:
    return path.relative_to(REPO_ROOT).with_suffix("").as_posix().replace("/", ".")


def import_lines(text: str, module_name: str) -> list[str]:
    return re.findall(
        r"^import\s+" + re.escape(module_name) + r"(?:\s+as\s+[A-Za-z][A-Za-z0-9_']*)?\s*$",
        text,
        flags=re.MULTILINE,
    )


@pytest.fixture(scope="module")
def receipt_text() -> tuple[Path, str, str]:
    receipts = sprint166_receipts()
    assert receipts, (
        "missing Sprint166 projection/nonlocality Agda receipt under "
        "DASHI/Physics/Closure"
    )
    assert len(receipts) == 1, [
        path.relative_to(REPO_ROOT).as_posix() for path in receipts
    ]
    receipt = receipts[0]
    module_name = module_name_for(receipt)
    return receipt, module_name, read_text(receipt)


def run_agda(path: Path) -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, str(path.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_sprint166_receipt_module_name_matches_path(
    receipt_text: tuple[Path, str, str],
) -> None:
    receipt, module_name, text = receipt_text
    assert module_name.startswith(MODULE_PREFIX)
    assert text.splitlines()[0] == f"module {module_name} where"
    assert "Sprint166" in receipt.name


def test_sprint166_receipt_typechecks_with_agda(
    receipt_text: tuple[Path, str, str],
) -> None:
    receipt, _, _ = receipt_text
    run_agda(receipt)


def test_sprint166_receipt_records_projection_nonlocality_targets_and_anchors(
    receipt_text: tuple[Path, str, str],
) -> None:
    _, _, text = receipt_text
    normalized = normalize(text)

    for term in TARGET_NAME_TERMS + P0_ANCHOR_TERMS + SPRINT164_ANCHOR_TERMS:
        assert normalize(term) in normalized, term

    for terms in TRUE_TARGET_FIELD_TERMS:
        assert has_evidence(text, name_terms=terms, value=True), (
            "missing true target-recorded/anchor evidence for " + repr(terms)
        )

    for key in CONTROL_CARD_KEYS:
        assert normalize(key) in normalized, f"missing O/R/C/S/L/P/G/F string {key}"


def test_sprint166_receipt_keeps_theorem_and_promotion_fields_false(
    receipt_text: tuple[Path, str, str],
) -> None:
    _, _, text = receipt_text

    for terms in FALSE_THEOREM_PROMOTION_TERMS:
        assert has_evidence(text, name_terms=terms, value=False), (
            "missing false theorem/promotion evidence for " + repr(terms)
        )

    forbidden_true_flags = [
        name
        for name, assigned in bool_assignments(text)
        if assigned == "true"
        and any(
            token in normalize(name)
            for token in ("promoted", "promotion", "clay", "solved")
        )
        and "target" not in normalize(name)
        and "recorded" not in normalize(name)
        and "anchor" not in normalize(name)
    ]
    assert forbidden_true_flags == []


def test_sprint166_obligation_index_integration_is_present(
    receipt_text: tuple[Path, str, str],
) -> None:
    _, module_name, _ = receipt_text
    text = read_text(OBLIGATION_INDEX)
    normalized = normalize(text)

    for term in (
        "Sprint166",
        module_name,
        "ProjectionNonlocality",
        "PressureNonlocality",
        "P0",
        "Sprint164",
        "promotesClay",
    ):
        assert normalize(term) in normalized, term

    assert re.search(r"\bpromotesClay\s*=\s*false\b", text), (
        "Sprint166 ObligationIndex row must fail closed"
    )


def test_sprint166_everything_imports_receipt_once(
    receipt_text: tuple[Path, str, str],
) -> None:
    _, module_name, _ = receipt_text
    text = read_text(EVERYTHING)
    imports = import_lines(text, module_name)
    assert imports == [f"import {module_name}"]
