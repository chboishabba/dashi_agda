from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Law/SensibLawWoogarooEPBC8575PortalClockManifestationExact.agda": [
        "module DASHI.Law.SensibLawWoogarooEPBC8575PortalClockManifestationExact where",
        "epbcAct95B130Source",
        "epbcPortal8575ManifestationSource",
        "officialReferralsSpatialService",
        "saveWoogarooProcessSummary",
        "finalPDPublicationStatusPaid",
        "minister95BReceiptDateOpen",
        "section95BReceiptStartsClock",
        "requiredFeePaymentPartOfReceiptGate",
        "section130FortyBusinessDayClock",
        "section130WrittenExtensionMayLengthenPeriod",
        "finalPDPublicationDoesNotStartClockByItself",
        "decisionStatusExpiredDoesNotImplySupersedingReferral",
        "decisionStatusPublishedDoesNotEqualPart9Approval",
        "portalStatusDoesNotPayOperativeLegalState",
        "referralBoundaryDoesNotEqualDevelopmentFootprint",
        "moreThan850IsCommunityAccountedCountOnly",
        "exactSubmissionCountRemainsOpen",
        "canonicalPortalClockPareto",
    ],
    "DASHI/Law/SensibLawWoogarooPreservationEverything.agda": [
        "import DASHI.Law.SensibLawWoogarooEPBC8575PortalClockManifestationExact",
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

print("Woogaroo EPBC 8575 portal/clock manifestation static contract: OK")
