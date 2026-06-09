from __future__ import annotations

import re
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSDefectLaplacianRankOneSpectrum.agda"
)
MODULE_NAME = "DASHI.Physics.Closure.NSDefectLaplacianRankOneSpectrum"

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_TODO = "TO" + "DO"
TOKEN_STUB = "st" + "ub"
TOKEN_PLACEHOLDER = "place" + "holder"

FORBIDDEN_PATTERNS = {
    "unproved axiom marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_POSTULATE + r"(?![A-Za-z0-9_])"
    ),
    "open work marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_TODO + r"(?![A-Za-z0-9_])"
    ),
    "incomplete surface wording": re.compile(
        r"(?<![A-Za-z0-9_])(?:" + TOKEN_STUB + "|" + TOKEN_PLACEHOLDER + r"s?)(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "Agda hole start": re.compile(r"\{!"),
    "Agda hole end": re.compile(r"!\}"),
}


def read_module() -> str:
    assert MODULE_PATH.exists(), (
        "missing Agda module: "
        + str(MODULE_PATH.relative_to(REPO_ROOT))
    )
    return MODULE_PATH.read_text(encoding="utf-8", errors="replace")


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def identifier_pattern(identifier: str) -> re.Pattern[str]:
    return re.compile(
        r"(?<![A-Za-z0-9_])" + re.escape(identifier) + r"(?![A-Za-z0-9_])"
    )


def bool_export_pattern(export: str, value: bool) -> re.Pattern[str]:
    agda_bool = "true" if value else "false"
    return re.compile(
        r"(?<![A-Za-z0-9_])"
        + re.escape(export)
        + r"(?![A-Za-z0-9_])"
        + r"(?:\s*:\s*[^\n=]+)?\s*=\s*"
        + agda_bool
        + r"(?![A-Za-z0-9_])",
        re.MULTILINE,
    )


def nat_export_pattern(export: str, value: int) -> re.Pattern[str]:
    return re.compile(
        r"(?<![A-Za-z0-9_])"
        + re.escape(export)
        + r"(?![A-Za-z0-9_])"
        + r"(?:\s*:\s*[^\n=]+)?\s*=\s*"
        + str(value)
        + r"(?![A-Za-z0-9_])",
        re.MULTILINE,
    )


def test_ns_defect_laplacian_rank_one_module_exists_and_has_no_incomplete_markers() -> None:
    text = read_module()

    assert f"module {MODULE_NAME} where" in text

    failures: list[str] = []
    for label, pattern in FORBIDDEN_PATTERNS.items():
        for match in pattern.finditer(text):
            failures.append(
                f"{MODULE_PATH.relative_to(REPO_ROOT)}:{line_for_offset(text, match.start())}: {label}"
            )

    assert not failures, "Forbidden Agda surface markers:\n" + "\n".join(failures)


def test_ns_defect_laplacian_rank_one_exports_required_finite_surface_names() -> None:
    text = read_module()

    required_names = [
        "AngleState",
        "radialZero",
        "shallowPiOverSix",
        "balancedPiOverFour",
        "steepPiOverThree",
        "tangentialPiOverTwo",
        "lambdaDeltaNumerator16",
        "lambdaDeltaFormulaHolds",
        "zeroMode",
        "zeroModeIffRadialTangential",
        "maxWitness",
        "maxWitnessNumerator16Is4",
        "offZeroPositive",
        "offZeroPositiveShallow",
        "offZeroPositiveBalanced",
        "offZeroPositiveSteep",
        "NSDefectLaplacianRankOneSpectrumReceipt",
        "canonicalNSDefectLaplacianRankOneSpectrumReceipt",
    ]
    missing = [name for name in required_names if not identifier_pattern(name).search(text)]

    assert not missing, "missing required finite surface names:\n" + "\n".join(missing)


def test_ns_defect_laplacian_rank_one_records_exact_denominators_and_formula_text() -> None:
    text = read_module()

    required_literals = [
        "lambda_delta(alpha)=cos^2(alpha)sin^2(alpha)",
        "0,3,4,3,0",
        "4/16=1/4",
        "zeroMode iff radial/tangential",
    ]
    missing_literals = [literal for literal in required_literals if literal not in text]

    assert not missing_literals, "missing formula literals:\n" + "\n".join(missing_literals)
    assert nat_export_pattern("lambdaDeltaDenominator16", 16).search(text)
    assert nat_export_pattern("lambdaDeltaMaxDenominator4", 4).search(text)
    assert nat_export_pattern("angleStateCount", 5).search(text)


def test_ns_defect_laplacian_rank_one_clay_promotion_is_false() -> None:
    text = read_module()

    assert bool_export_pattern("clayNavierStokesPromoted", False).search(text)
    assert bool_export_pattern("fullClayNSSolved", False).search(text)
    assert "clayNavierStokesPromoted=false" in text
    assert "NSDefectLaplacianRankOnePromotion" in text
    assert "nsDefectLaplacianRankOnePromotionImpossibleHere" in text
    assert "clayNavierStokesPromoted = true" not in text


def test_ns_defect_laplacian_rank_one_agda_typechecks_standalone() -> None:
    result = subprocess.run(
        ["agda", "-i", ".", str(MODULE_PATH.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )

    assert result.returncode == 0, result.stdout
