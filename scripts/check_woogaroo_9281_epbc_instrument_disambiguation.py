from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Law/SensibLawWoogaroo9281EPBCInstrumentDisambiguationExact.agda": [
        "module DASHI.Law.SensibLawWoogaroo9281EPBCInstrumentDisambiguationExact where",
        "firstNine2016ReferralDecision",
        "firstNine2016VariationDecision",
        "firstNine2016FinalApprovalReceipt",
        "firstNineApprovalIsOperativeButDifferentAction",
        "epbc2016ApprovalDoesNotPay9281Condition6aWithoutSameAction",
        "epbc2016ApprovalDoesNotPay8575Authorisation",
        "genericSpringfieldApprovalDoesNotIdentifyCondition6aInstrument",
        "condition6aLiteralInstrumentStillOpen",
        "canonicalInstrumentDisambiguationPareto",
    ],
    "DASHI/Law/SensibLawWoogarooPreservationEverything.agda": [
        "import DASHI.Law.SensibLawWoogaroo9281EPBCInstrumentDisambiguationExact",
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

print("Woogaroo 9281 EPBC instrument disambiguation static contract: OK")
