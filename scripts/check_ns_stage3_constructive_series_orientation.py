#!/usr/bin/env python3
"""Fail closed on constructive-real comparison and Schur substitution."""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

FILES = (
    "DASHI/Physics/Closure/NSTriadKNConstructiveRealCandidateComparison.agda",
    "DASHI/Physics/Closure/NSTriadKNGrafakosTorresPowerLawOrientation.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationWeightedExponentIdentity.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationLiteralShellSubstitution.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationAffineFamilySubstitution.agda",
    "DASHI/Physics/Closure/NSTriadKNStage3ConstructiveSeriesOrientationIntegration.agda",
)

PROVENANCE = ("-- PROVENANCE", "-- Authors:", "-- Title:", "-- Venue/year:", "-- DOI:", "-- Relationship:")
FORBIDDEN = ("{!!}", "?}", "{-# TERMINATING #-}", "{-# NON_TERMINATING #-}")
POSTULATE = re.compile(r"(?m)^\s*postulate(?:\s|$)")


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    failures: list[str] = []
    for relative in FILES:
        path = root / relative
        if not path.is_file():
            failures.append(f"missing: {relative}")
            continue
        text = path.read_text(encoding="utf-8")
        if POSTULATE.search(text):
            failures.append(f"{relative}: forbidden postulate")
        for marker in FORBIDDEN:
            if marker in text:
                failures.append(f"{relative}: forbidden marker {marker!r}")
        for marker in PROVENANCE:
            if marker not in text:
                failures.append(f"{relative}: missing provenance marker {marker!r}")
        for opening, closing in (("(", ")"), ("{", "}")):
            if text.count(opening) != text.count(closing):
                failures.append(f"{relative}: unbalanced {opening}{closing}")

    verifier = root / "scripts/ns_stage3_power_law_orientation_audit.py"
    if not verifier.is_file():
        failures.append("missing power-law substitution exact verifier")
    else:
        result = subprocess.run([sys.executable, str(verifier)], cwd=root, check=False, capture_output=True, text=True)
        if result.returncode:
            failures.append(result.stderr.strip() or result.stdout.strip())

    if failures:
        print("\n".join(failures))
        return 1
    print(
        "checked constructive-real comparison and output-relocation Schur substitution: "
        "6 Agda modules, exact verifier, provenance, no holes/postulates/escapes; "
        "literal rows and six epsilon slopes closed while dyadic tail, numeric "
        "bases/directions, positive epsilon and Check A remain fail-closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
