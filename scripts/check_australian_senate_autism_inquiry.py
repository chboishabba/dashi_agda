from pathlib import Path

p = Path("DASHI/Governance/AustralianSenateAutismInquiryExact.agda")
assert p.exists(), "missing AustralianSenateAutismInquiryExact.agda"

s = p.read_text()
for needle in [
    "senateAutismReportISBN",
    "committeeRecommendationDoesNotEqualImplementation",
    "governmentSupportDoesNotEqualImplementation",
    "sourceIdentityImportsTruthIsFalse",
    "recommendation18IntersectionalFocus",
    "autismLabelCannotRecoverSituatedNeed",
    "orderedPaymentFrontier",
    "oeisSuppliesNoAuthority",
]:
    assert needle in s, f"missing {needle}"

print("ok")
