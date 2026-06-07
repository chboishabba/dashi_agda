from __future__ import annotations

import re
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
AGDA_FILE = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "YMBTMetricRatioDefectGapFinite.agda"
)


def read_source() -> str:
    return AGDA_FILE.read_text(encoding="utf-8")


def test_ym_bt_metric_ratio_defect_gap_finite_typechecks() -> None:
    result = subprocess.run(
        ["agda", str(AGDA_FILE.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )

    assert result.returncode == 0, result.stdout


def test_ym_bt_metric_ratio_defect_gap_finite_formula_terms() -> None:
    source = read_source()

    assert "data PrimeSample : Set where" in source
    for term in ("p2", "p3", "p5"):
        assert re.search(rf"(?m)^\s*{term}\s*:", source)

    assert "kappaFormulaNumerator p =" in source
    assert "(primeNat p - 1) * (primeNat p - 1)" in source
    assert "kappaFormulaDenominator p =" in source
    assert "primeNat p * primeNat p" in source

    expected_equalities = [
        "numerator p2KappaRatio ≡ 1",
        "denominator p2KappaRatio ≡ 4",
        "numerator p3KappaRatio ≡ 4",
        "denominator p3KappaRatio ≡ 9",
        "numerator p5KappaRatio ≡ 16",
        "denominator p5KappaRatio ≡ 25",
    ]
    for equality in expected_equalities:
        assert equality in source

    for proof_name in (
        "p2NumeratorPositive",
        "p3NumeratorPositive",
        "p5NumeratorPositive",
        "p2DepthIndependent",
        "p3DepthIndependent",
        "p5DepthIndependent",
    ):
        assert re.search(rf"(?m)^{proof_name}\s*=\s*refl$", source)


def test_ym_bt_metric_ratio_defect_gap_finite_flags_are_fail_closed() -> None:
    source = read_source()

    expected_flags = {
        "finiteBTGapRecorded": "true",
        "infDepthUniformForFiniteSample": "true",
        "strictSelectedHodgeVariationPairingClosed": "false",
        "continuumMassGapPromoted": "false",
        "clayYangMillsPromoted": "false",
    }
    for name, value in expected_flags.items():
        assert re.search(rf"(?m)^{name}\s*:\s*Bool\s*$", source)
        assert re.search(rf"(?m)^{name}\s*=\s*{value}\s*$", source)


def test_ym_bt_metric_ratio_defect_gap_finite_has_no_placeholders() -> None:
    source = read_source()
    forbidden = {
        "postulate": r"(?<![A-Za-z0-9_])postulate(?![A-Za-z0-9_])",
        "hole start": r"\{!",
        "hole end": r"!\}",
        "skeleton": r"(?<![A-Za-z0-9_])skeleton(?![A-Za-z0-9_])",
    }

    failures = [
        label
        for label, pattern in forbidden.items()
        if re.search(pattern, source, flags=re.IGNORECASE)
    ]
    assert not failures, "forbidden markers found: " + ", ".join(failures)
