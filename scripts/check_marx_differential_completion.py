#!/usr/bin/env python3
"""Fail-closed source audit for the Marx differential completion lane."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

FILES = [
    "DASHI/Analysis/MarxDifferentialCore.agda",
    "DASHI/Analysis/MarxPolynomialDifferential.agda",
    "DASHI/Analysis/MarxConstructiveRealAdapter.agda",
    "DASHI/Analysis/MarxConstructiveRealRingNormalisation.agda",
    "DASHI/Analysis/MarxFastCauchyCompletionCutset.agda",
    "DASHI/Analysis/MarxFastCauchyDerivativeCompletion.agda",
    "DASHI/Analysis/MarxPowerRuleNormalisation.agda",
    "DASHI/Analysis/MarxReciprocalQuotientNormalisation.agda",
    "DASHI/Analysis/MarxOrdinaryDerivativeBridge.agda",
    "DASHI/Analysis/MarxHigherCalculus.agda",
    "DASHI/Analysis/MarxFrechetProduct.agda",
    "DASHI/Analysis/MarxExteriorIntegration.agda",
    "DASHI/Analysis/MarxDifferentialRegression.agda",
    "DASHI/Analysis/MarxDifferentialBundle.agda",
    "DASHI/Governance/TraumaExploitationDifferential.agda",
    "DASHI/Governance/GeopoliticalDifferentialEvidence.agda",
    "DASHI/Governance/GeopoliticalGlobalPlayerCriterion.agda",
    "DASHI/Governance/IsraelCyberLegalStatusCandidate.agda",
]

FORBIDDEN = (
    "postulate",
    "{!!}",
    "?}",
    "TERMINATING",
    "NON_TERMINATING",
    "sorry",
    "admit ",
)

REQUIRED = {
    "DASHI/Analysis/MarxDifferentialCore.agda": (
        "MarxFactorisation",
        "rawDiagonalQuotientImpossible",
        "chainRule",
    ),
    "DASHI/Analysis/MarxConstructiveRealRingNormalisation.agda": (
        "ordinaryConstructiveRealMarxAlgebra",
        "ordinaryMarxCarrierNonterminal",
    ),
    "DASHI/Analysis/MarxFastCauchyCompletionCutset.agda": (
        "selectedFastCauchyMarxAlgebra",
        "selectedFastCauchyCarrierNonterminal",
    ),
    "DASHI/Analysis/MarxFastCauchyDerivativeCompletion.agda": (
        "selectedFastCauchyDerivativeSeam",
        "selectedFastCauchyCompatibilityAuthority",
    ),
    "DASHI/Analysis/MarxPowerRuleNormalisation.agda": (
        "powerDerivativeNatScale",
        "polynomialDerivativeInterpretationCommutes",
    ),
    "DASHI/Analysis/MarxReciprocalQuotientNormalisation.agda": (
        "reciprocalDerivativeDenominatorSquared",
        "quotientRule",
        "LocallyNonzeroAt",
    ),
    "DASHI/Analysis/MarxOrdinaryDerivativeBridge.agda": (
        "NormalizedRemainderVanishes",
        "marxFactorisationAndDiagonalContinuityGiveOrdinaryDerivative",
        "marxDerivativeEqualsOrdinaryDerivative",
    ),
    "DASHI/Analysis/MarxHigherCalculus.agda": (
        "FrechetDerivativeAt",
        "frechetChainRule",
        "constantJacobianDoesNotEntailGlobalInjectivity",
    ),
    "DASHI/Analysis/MarxFrechetProduct.agda": (
        "BilinearProduct",
        "frechetProduct",
        "frechetProductDerivativeFormula",
    ),
    "DASHI/Analysis/MarxExteriorIntegration.agda": (
        "alternatingAdjacent",
        "exteriorDerivativeSquaredZero",
        "riemannSum",
        "FundamentalTheoremBridge",
    ),
    "DASHI/Governance/GeopoliticalDifferentialEvidence.agda": (
        "provisionalOrderDoesNotEntailFinalMeritsJudgment",
        "gainEvidenceAloneCannotPromote",
    ),
    "DASHI/Governance/GeopoliticalGlobalPlayerCriterion.agda": (
        "ConcreteGlobalPlayerSupported",
        "denominatorCompatibilityReceipt",
    ),
    "DASHI/Governance/IsraelCyberLegalStatusCandidate.agda": (
        "currentFixtureCannotPromoteMechanism",
        "traumaExportMechanismStatus",
    ),
}


def fail(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    for relative in FILES:
        path = ROOT / relative
        if not path.is_file():
            fail(f"missing required file: {relative}")
        text = path.read_text(encoding="utf-8")
        for token in FORBIDDEN:
            if token in text:
                fail(f"forbidden proof escape {token!r} in {relative}")
        for token in REQUIRED.get(relative, ()):
            if token not in text:
                fail(f"missing required declaration {token!r} in {relative}")

    bundle = (ROOT / "DASHI/Analysis/MarxDifferentialBundle.agda").read_text(
        encoding="utf-8"
    )
    for relative in FILES:
        if relative.endswith("MarxDifferentialBundle.agda"):
            continue
        module_name = relative[:-5].replace("/", ".")
        if module_name.startswith("DASHI.Analysis.Marx") or module_name.startswith(
            "DASHI.Governance."
        ):
            if module_name not in bundle:
                fail(f"bundle does not import {module_name}")

    print(f"Marx differential completion audit passed for {len(FILES)} files")


if __name__ == "__main__":
    main()
