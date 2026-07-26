#!/usr/bin/env python3
"""Fail if the Clay-facing Stage-3 tranche introduces proof holes or postulates."""

from __future__ import annotations

from pathlib import Path

FILES = [
    "DASHI/Physics/Closure/NSTriadKNLiteralDyadicShellConstants.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3ExactCarrier.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3RealityPhaseAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3GalerkinEquationAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNCoarseGainDiagnostics.agda",
    "DASHI/Physics/Closure/NSTriadKNRefinedQuantitativeClassification.agda",
    "DASHI/Physics/Closure/NSTriadKNLegacyCoordinateInterpretationAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNCutoffUniformClasswiseEstimateProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNSignedUniformGapProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNArbitraryDataAprioriProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNPhysicalTriadFrontierProgram.agda",
]

FORBIDDEN = (
    "postulate",
    "{!!}",
    "?}",
    "{-# TERMINATING #-}",
    "{-# NON_TERMINATING #-}",
)


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    failures: list[str] = []

    for relative in FILES:
        path = root / relative
        if not path.is_file():
            failures.append(f"missing: {relative}")
            continue

        text = path.read_text(encoding="utf-8")
        for marker in FORBIDDEN:
            if marker in text:
                failures.append(f"{relative}: forbidden marker {marker!r}")

        if text.count("(") != text.count(")"):
            failures.append(f"{relative}: unbalanced parentheses")
        if text.count("{") != text.count("}"):
            failures.append(f"{relative}: unbalanced braces")

    if failures:
        for failure in failures:
            print(failure)
        return 1

    print(f"checked {len(FILES)} Clay-facing Stage-3 files: no holes or postulates")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
