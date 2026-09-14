from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Law/SensibLawWoogaroo9281Condition6aResponseClassifierExact.agda": [
        "module DASHI.Law.SensibLawWoogaroo9281Condition6aResponseClassifierExact where",
        "noControlledActionEvidenceCase",
        "part9ApprovalCase",
        "historicalOrUnrelatedInstrumentCase",
        "condition6aRecordUnavailableCase",
        "noControlledActionEvidenceNeedsSameProposedClearing",
        "part9ApprovalNeedsSameActionGeometryPhaseAndOperativeTime",
        "historicalInstrumentDoesNotTransferAuthorisation",
        "classificationDoesNotEqualConditionSatisfaction",
        "currentCondition6aClassificationState",
        "canonicalCondition6aResponsePareto",
    ],
    "DASHI/Law/SensibLawWoogarooPreservationEverything.agda": [
        "import DASHI.Law.SensibLawWoogaroo9281Condition6aResponseClassifierExact",
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

print("Woogaroo 9281 Condition 6(a) response-classifier static contract: OK")
