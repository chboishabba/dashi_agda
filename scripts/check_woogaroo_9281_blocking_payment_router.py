from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Law/SensibLawWoogaroo9281BlockingPaymentRouterExact.agda": [
        "module DASHI.Law.SensibLawWoogaroo9281BlockingPaymentRouterExact where",
        "condition6aLiteralSubmissionPayment",
        "samePhasePreclearancePayment",
        "authoritativeGeometryPayment",
        "imminencePayment",
        "standingCounselPayment",
        "currentBlockingPaymentState",
        "condition6aAndSamePhaseRemainFirstCut",
        "sourceDerivedGeometryDoesNotPayAuthoritativeGeometry",
        "counselEscalationEligibilityDoesNotEqualLegalConclusion",
        "canonicalBlockingPaymentPareto",
    ],
    "DASHI/Law/SensibLawWoogarooPreservationEverything.agda": [
        "import DASHI.Law.SensibLawWoogaroo9281BlockingPaymentRouterExact",
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

print("Woogaroo 9281 blocking payment router static contract: OK")
