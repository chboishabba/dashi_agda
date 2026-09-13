from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Law/SensibLawWoogaroo9281PreclearanceConvergenceExact.agda": [
        "module DASHI.Law.SensibLawWoogaroo9281PreclearanceConvergenceExact where",
        "negotiated9281DecisionNotice",
        "approved9281GeneralArrangement",
        "condition6aLocalFederalGate",
        "approvedPlanEPBCExecutionGate",
        "springfield8575EnvironmentalPreclearanceProtocol",
        "springfield8575SignedChecklistProtocol",
        "Atlas.springfield8575January2026PreliminaryDocumentation",
        "localConditionAndProponentProtocolConvergeOnFederalClearance",
        "proponentProtocolDoesNotEqualOperativePart9Condition",
        "signedChecklistDoesNotEqualFederalApproval",
        "sourceCitationDoesNotPaySameActionIdentity",
        "condition6aSatisfactionRecordFirstLeaf",
        "signedEnvironmentalPreclearancePackageSecondLeaf",
        "canonicalPreclearanceConvergencePareto",
    ],
    "DASHI/Law/SensibLawWoogarooPreservationEverything.agda": [
        "import DASHI.Law.SensibLawWoogaroo9281PreclearanceConvergenceExact",
    ],
}

missing = []
for rel, needles in REQUIRED.items():
    path = ROOT / rel
    if not path.exists():
        missing.append(f"missing file: {rel}")
        continue
    text = path.read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            missing.append(f"{rel}: missing {needle}")

if missing:
    raise SystemExit("\n".join(missing))

print("Woogaroo 9281 preclearance convergence + attribution static contract: OK")
