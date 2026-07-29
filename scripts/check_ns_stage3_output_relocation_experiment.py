#!/usr/bin/env python3
"""Fail closed on the output-relocation vertical-slice experiment."""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

FILES = (
    "DASHI/Physics/Closure/NSTriadKNInageHighHighComparatorAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3RelocationInstantiation.agda",
    "DASHI/Physics/Closure/NSTriadKNOutputRelocationWeightedExponentIdentity.agda",
    "DASHI/Physics/Closure/NSTriadKNStage3OutputRelocationVerticalSlice.agda",
    "DASHI/Physics/Closure/NSTriadKNStage3OutputRelocationExperimentIntegration.agda",
)

PROVENANCE = ("-- PROVENANCE", "-- Title:", "-- Venue/year:", "-- DOI:", "-- Relationship:")
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

    verifier = root / "scripts/ns_stage3_output_relocation_vertical_slice_audit.py"
    if not verifier.is_file():
        failures.append("missing output-relocation exact verifier")
    else:
        result = subprocess.run(
            [sys.executable, str(verifier)],
            cwd=root,
            check=False,
            capture_output=True,
            text=True,
        )
        if result.returncode:
            failures.append(result.stderr.strip() or result.stdout.strip())

    if failures:
        print("\n".join(failures))
        return 1
    print(
        f"checked output-relocation experiment: {len(FILES)} Agda modules, "
        "exact audit, provenance, no holes/postulates/termination escapes; "
        "concrete carrier and weighted exponent closed, while constructive "
        "series, numeric vector and epsilon remain correctly fail-closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
