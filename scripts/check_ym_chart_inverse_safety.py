#!/usr/bin/env python3
"""Fail-closed audit for restricted chart and finite inverse applicability."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "DASHI" / "Physics" / "YangMills"

REQUIRED = {
    "BalabanRestrictedFluctuationCoordinateBijection.agda": [
        "RestrictedChartData",
        "restrictedChartInjective",
        "restrictedChartSurjective",
        "restrictedRoundTripsGiveBijection",
        "JacobianCollisionData",
        "constantJacobianCollisionRefutesGlobalInjectivity",
        "restrictedFluctuationCoordinateBijectionLevel = machineChecked",
        "jacobianAloneImpliesGlobalBijectionLevel = counterexample",
    ],
    "BalabanFiniteConstrainedInverseApplicability.agda": [
        "FiniteConstrainedCarrier",
        "FiniteConstrainedInverseApplicability",
        "selectedFiniteInverseCertificate",
        "selectedFiniteGreenOperatorBound",
        "selectedInverseLeftOnConstraint",
        "selectedInverseRightOnConstraint",
        "selectedInverseNormBoundOnConstraint",
        "finiteConstrainedInverseApplicabilityAssemblyLevel = machineChecked",
    ],
}

FORBIDDEN = ("postulate", "{!!}", "{-# TERMINATING #-", "= _")
errors: list[str] = []
for filename, needles in REQUIRED.items():
    path = BASE / filename
    if not path.exists():
        errors.append(f"missing {path.relative_to(ROOT)}")
        continue
    text = path.read_text(encoding="utf-8")
    for forbidden in FORBIDDEN:
        if forbidden in text:
            errors.append(f"{filename}: forbidden proof escape {forbidden!r}")
    for needle in needles:
        if needle not in text:
            errors.append(f"{filename}: missing required surface {needle!r}")

if errors:
    print("[fail] chart/inverse safety audit")
    for error in errors:
        print(f" - {error}")
    raise SystemExit(1)

print("[ok] restricted chart and constrained inverse safety are present")
