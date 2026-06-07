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
CLAY_PROMOTION_FLAGS = (
    "fullClayNSSolved",
    "full_clay_ns_solved",
    "fullNavierStokesSolutionConstructed",
    "clayNavierStokesPromoted",
)


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def has_named_bool_assignment(
    text: str,
    *,
    name_terms: tuple[str, ...],
    value: bool | None = None,
) -> bool:
    bool_decl = re.compile(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*Bool\s*\n\1\s*=\s*(true|false)\b"
    )
    for match in bool_decl.finditer(text):
        if value is not None and match.group(2) != ("true" if value else "false"):
            continue
        normalized_name = normalize(match.group(1))
        if all(normalize(term) in normalized_name for term in name_terms):
            return True
    return False


def has_true_evidence(text: str, *, name_terms: tuple[str, ...]) -> bool:
    if has_named_bool_assignment(text, name_terms=name_terms, value=True):
        return True

    true_proof = re.compile(
        r"\b([A-Za-z][A-Za-z0-9_']*)\s*:\s*"
        r"([A-Za-z][A-Za-z0-9_']*)\s*≡\s*true\b"
    )
    for match in true_proof.finditer(text):
        normalized_evidence = normalize(" ".join(match.groups()))
        if all(normalize(term) in normalized_evidence for term in name_terms):
            return True
    return False


def sprint161_receipts() -> list[Path]:
    return sorted(
        path
        for path in CLOSURE_DIR.glob("*Sprint161*.agda")
        if "receipt" in normalize(path.stem)
    )


@pytest.fixture(scope="module")
def receipt_text() -> tuple[Path, str]:
    receipts = sprint161_receipts()
    if not receipts:
        pytest.skip("Sprint161 Agda receipt has not landed yet")
    assert len(receipts) == 1, [
        path.relative_to(REPO_ROOT).as_posix() for path in receipts
    ]
    receipt = receipts[0]
    return receipt, receipt.read_text(encoding="utf-8")


def test_sprint161_receipt_exists() -> None:
    receipts = sprint161_receipts()
    assert receipts, "missing Sprint161 Agda receipt under DASHI/Physics/Closure"
    assert len(receipts) == 1, [
        path.relative_to(REPO_ROOT).as_posix() for path in receipts
    ]


def test_sprint161_receipt_typechecks_with_agda(
    receipt_text: tuple[Path, str],
) -> None:
    receipt, _ = receipt_text
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, str(receipt.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_sprint161_receipt_records_anchors_flags_and_routes(
    receipt_text: tuple[Path, str],
) -> None:
    _, text = receipt_text
    normalized = normalize(text)

    assert "Sprint161" in text
    assert "Sprint160" in text
    assert has_true_evidence(text, name_terms=("Sprint160", "anchor")), (
        "missing true Sprint160 anchor evidence"
    )
    assert has_true_evidence(text, name_terms=("Sprint161", "boundary")), (
        "missing true Sprint161 boundary evidence"
    )

    assert has_named_bool_assignment(text, name_terms=("boundary",), value=True)
    assert has_named_bool_assignment(text, name_terms=("route",), value=True)

    route_names = re.findall(r"\b([A-Za-z][A-Za-z0-9_']*Route[A-Za-z0-9_']*)\b", text)
    assert len(set(route_names)) >= 2, "missing named Sprint161 route surfaces"

    for key in CONTROL_CARD_KEYS:
        assert normalize(key) in normalized, f"missing O/R/C/S/L/P/G/F string {key}"


def test_sprint161_receipt_keeps_clay_promotion_fail_closed(
    receipt_text: tuple[Path, str],
) -> None:
    _, text = receipt_text

    for name in CLAY_PROMOTION_FLAGS:
        if name in text:
            assert agda_bool_assignment(text, name, False), name

    assert not re.search(
        r"\b(?:fullClayNSSolved|full_clay_ns_solved|"
        r"fullNavierStokesSolutionConstructed|clayNavierStokesPromoted)"
        r"\s*=\s*true\b",
        text,
    )


def test_sprint161_obligation_index_integration_if_present(
    receipt_text: tuple[Path, str],
) -> None:
    receipt, _ = receipt_text
    assert OBLIGATION_INDEX.is_file(), "missing DASHI/Promotion/ObligationIndex.agda"
    text = OBLIGATION_INDEX.read_text(encoding="utf-8")
    if "Sprint161" not in text:
        pytest.skip("Sprint161 ObligationIndex integration has not landed yet")

    normalized = normalize(text)
    module_name = receipt.relative_to(REPO_ROOT).with_suffix("").as_posix().replace("/", ".")

    for term in ("Sprint161", "boundary", "route"):
        assert normalize(term) in normalized, term
    assert module_name in text


def test_sprint161_everything_import_if_present(
    receipt_text: tuple[Path, str],
) -> None:
    receipt, _ = receipt_text
    assert EVERYTHING.is_file(), "missing DASHI/Everything.agda"
    text = EVERYTHING.read_text(encoding="utf-8")
    module_name = receipt.relative_to(REPO_ROOT).with_suffix("").as_posix().replace("/", ".")
    imports = re.findall(
        r"^import\s+(DASHI\.Physics\.Closure\.[A-Za-z0-9_']*Sprint161[A-Za-z0-9_']*)\s*$",
        text,
        flags=re.MULTILINE,
    )
    if not imports:
        pytest.skip("Sprint161 Everything integration has not landed yet")
    assert imports == [module_name]
