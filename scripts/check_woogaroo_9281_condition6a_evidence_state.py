from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Law/SensibLawWoogaroo9281Condition6aEvidenceStateExact.agda": [
        "module DASHI.Law.SensibLawWoogaroo9281Condition6aEvidenceStateExact where",
        "condition6aSatisfactionNotRecoverableFromPublicRegister",
        "publicSilenceDoesNotProveNonSubmission",
        "conditionExistenceDoesNotProveSatisfaction",
        "finalPDNoticeDoesNotProveNoLaterPart9Decision",
        "condition6aAcquisitionBundle",
        "sameClearingPhaseRequiredBeforePromotion",
        "canonicalCondition6aEvidencePareto",
    ],
    "DASHI/Law/SensibLawWoogarooPreservationEverything.agda": [
        "import DASHI.Law.SensibLawWoogaroo9281Condition6aEvidenceStateExact",
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

print("Woogaroo 9281 condition-6(a) evidence-state static contract: OK")
