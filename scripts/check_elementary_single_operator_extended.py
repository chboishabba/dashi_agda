#!/usr/bin/env python3
"""Fail-closed source audit for the extended EML/ternary tranche."""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]

REQUIRED_FILES = [
    "DASHI/Foundations/ElementarySingleOperator.agda",
    "DASHI/Foundations/EMLAnalyticDomain.agda",
    "DASHI/Foundations/EMLPositiveRealAnalyticPackage.agda",
    "DASHI/Foundations/EMLComplexBranchPackage.agda",
    "DASHI/Foundations/EMLConcreteSmokeModel.agda",
    "DASHI/Foundations/ElementaryCalculator.agda",
    "DASHI/Foundations/ElementaryCalculatorAnalyticPackage.agda",
    "DASHI/Foundations/TernaryElementaryOperatorCandidate.agda",
    "DASHI/Foundations/TernaryWitnessIndependentRepresentation.agda",
    "DASHI/Foundations/TernaryElementarySearchCertificate.agda",
    "DASHI/Foundations/SpectralCountingComplexity.agda",
    "DASHI/Foundations/DivergenceComparisonPackage.agda",
    "DASHI/Physics/NavierStokes/DissipationNullComputationalCarrier.agda",
    "DASHI/Algebra/Quantum/BraKet.agda",
    "DASHI/Algebra/Quantum/TernaryCircuit.agda",
    "DASHI/Promotion/FiniteTernaryQuantumCircuitAdapter.agda",
    "DASHI/Foundations/ElementarySingleOperatorBundle.agda",
    "DASHI/Foundations/ElementarySingleOperatorExtendedRegression.agda",
    "DASHI/Unified/StructuralComplexitySurvivalBundle.agda",
    "scripts/search_ternary_elementary_candidates.py",
]

REQUIRED_SYMBOLS = {
    "DASHI/Foundations/EMLAnalyticDomain.agda": [
        "DefinedSource",
        "DefinedEML",
        "compileEML-preserves-defined",
        "AnalyticEMLCompilerPackage",
    ],
    "DASHI/Foundations/ElementaryCalculator.agda": [
        "CalculatorExpr",
        "lowerCalculator",
        "compileCalculator-correct",
        "constantPi",
        "calcArcTanh",
    ],
    "DASHI/Foundations/ElementaryCalculatorAnalyticPackage.agda": [
        "CalculatorAnalyticPackage",
        "calculatorCompiledDefined",
        "calculatorCompiledHasMeaning",
        "CalculatorUniversalityReceipt",
    ],
    "DASHI/Foundations/TernaryWitnessIndependentRepresentation.agda": [
        "ReusableWitnessUnit",
        "witnessIndependent",
        "contextsGiveTernaryRepresentation",
    ],
    "DASHI/Foundations/TernaryElementarySearchCertificate.agda": [
        "RewriteCertificate",
        "expLogStep",
        "logExpStep",
        "CertifiedSearchCandidate",
    ],
    "DASHI/Algebra/Quantum/TernaryCircuit.agda": [
        "QutritBasis",
        "QutritCircuit",
        "inverseGateLeft",
        "canonicalFiniteQutritPermutationSemantics",
    ],
}

FORBIDDEN_PROMOTIONS = [
    r"fullQutritQuantumComputerPromoted\s*=\s*true",
    r"fullAutomorphicWeylLawPromoted\s*=\s*true",
    r"timeDependentUniversalityPromoted\s*=\s*true",
    r"universalStrictWinnerPromoted\s*=\s*true",
]


def fail(message: str) -> None:
    print(f"[fail] {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> int:
    for relative in REQUIRED_FILES:
        path = ROOT / relative
        if not path.is_file():
            fail(f"missing required file: {relative}")

    for relative, symbols in REQUIRED_SYMBOLS.items():
        text = (ROOT / relative).read_text(encoding="utf-8")
        for symbol in symbols:
            if symbol not in text:
                fail(f"{relative} missing required symbol {symbol}")

    tranche_text = "\n".join(
        (ROOT / relative).read_text(encoding="utf-8")
        for relative in REQUIRED_FILES
        if relative.endswith(".agda")
    )
    for pattern in FORBIDDEN_PROMOTIONS:
        if re.search(pattern, tranche_text):
            fail(f"forbidden promotion matched: {pattern}")

    # New analytic/search modules must expose obligations as records rather than
    # silently adding local postulates.  The imported canonical real authority
    # remains the repository's existing explicit axiom boundary.
    for relative in REQUIRED_FILES:
        if not relative.endswith(".agda"):
            continue
        text = (ROOT / relative).read_text(encoding="utf-8")
        if re.search(r"^\s*postulate\b", text, flags=re.MULTILINE):
            fail(f"new tranche contains local postulate: {relative}")

    search_script = ROOT / "scripts/search_ternary_elementary_candidates.py"
    with tempfile.TemporaryDirectory() as tmp:
        out = pathlib.Path(tmp) / "scout.json"
        subprocess.run(
            [
                sys.executable,
                str(search_script),
                "--max-depth",
                "1",
                "--beam-width",
                "20",
                "--top-k",
                "2",
                "--out",
                str(out),
            ],
            cwd=ROOT,
            check=True,
        )
        payload = out.read_text(encoding="utf-8")
        if '"status": "scoutOnly"' not in payload:
            fail("scout output lost fail-closed status")
        for target in ("one", "exp", "log", "sub", "eml"):
            if f'"{target}"' not in payload:
                fail(f"scout output missing target {target}")

    print("[ok] extended EML/ternary source audit passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
