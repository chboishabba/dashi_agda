#!/usr/bin/env python3
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
EXPECT = {
    "DASHI/Physics/Propulsion/Rocketdyne1974MaterialIdentityAndConstitutiveDataExact.agda": [
        "wc103IdentityPaid", "vh101CoatingPaid", "haynes25At2000F", "c103HistoricalCreepAnchor"
    ],
    "DASHI/Physics/Propulsion/Rocketdyne1974TwoMaterialDiscriminatorExact.agda": [
        "sameModelRule", "haynesDamageObserved", "wc103FollowupSurvived", "currentDiscriminator"
    ],
    "DASHI/Physics/Propulsion/Rocketdyne1974IdentifiabilityCutExact.agda": [
        "twoThicknessesSameLoad", "geometryFreeStressNotUnique"
    ],
}

def main() -> int:
    failures = []
    for rel, tokens in EXPECT.items():
        p = ROOT / rel
        if not p.exists():
            failures.append(f"missing file: {rel}")
            continue
        text = p.read_text(encoding="utf-8")
        for token in tokens:
            if token not in text:
                failures.append(f"{rel}: missing export {token}")
    if failures:
        print("Rocketdyne thermomechanical max-cut: FAIL")
        print("\n".join(failures))
        return 1
    print("Rocketdyne thermomechanical max-cut: PASS")
    return 0

if __name__ == "__main__":
    sys.exit(main())
