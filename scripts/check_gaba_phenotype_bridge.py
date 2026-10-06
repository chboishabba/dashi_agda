from pathlib import Path

p = Path("DASHI/Biology/GABAPhenotypeBridgeExact.agda")
assert p.exists(), "missing GABAPhenotypeBridgeExact.agda"
text = p.read_text(encoding="utf-8")

required = [
    "record PromotionValidation",
    "record RegionalToWholeBrainBridge",
    "record GroupToIndividualBridge",
    "record AssociationToCausalBridge",
    "record SynchronyAttachmentBridge",
    "record NeurochemicalInflammationBridge",
    "data EvidenceFamily",
    "record SensoryGABAInteractionCarrier",
    "record GABARetrievalMemoryBridge",
    "record ADHDEvidenceGap",
    "causalPromotionRequiresExistingEstimand",
    "sameGABAEvidenceDifferentContextCanChangeLoad",
    "schmitzEvidenceDoesNotByItselfChangeMemory",
]
for needle in required:
    assert needle in text, f"missing bridge surface: {needle}"

for forbidden in [
    "autismCausedByLowGABA :",
    "adhdCausedByLowGABA :",
    "synchronyMeansInsecureAttachment :",
    "gabaCausesNeuroinflammation :",
]:
    assert forbidden not in text, f"forbidden promotion present: {forbidden}"

print("GABA phenotype bridge surface checks passed")
