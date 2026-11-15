from pathlib import Path

p = Path("DASHI/Biology/GABAPhenotypeEvidenceInstantiationExact.agda")
assert p.exists(), "missing GABAPhenotypeEvidenceInstantiationExact.agda"
text = p.read_text(encoding="utf-8")

required = [
    "nguyen2024SynchronyAttachmentAssociation",
    "nguyen2024SynchronyAttachmentBridge",
    "crowley2016NeuroimmuneEvidence",
    "crowley2016NeuroimmuneBridge",
    "schur2016ADHDMetaReceipt",
    "puts2020ADHDStriatalReceipt",
    "harris2021ADHDSensorimotorReceipt",
    "cheng2026ADHDSerumReceipt",
    "canonicalADHDEvidenceHeterogeneityAtlas",
    "adhdEvidenceDoesNotPayGeneralLowGABA",
    "adhdEvidenceDoesNotPayInverseSeverityLaw",
    "canonicalGABAEvidenceInstantiationBoundary",
]
for needle in required:
    assert needle in text, f"missing required instantiation surface: {needle}"

for forbidden in [
    "adhdGeneralLowGABA :",
    "higherGABAMeansLowerADHDSeverity :",
    "synchronyDefinesAttachment :",
    "neuroinflammationDefinesAutism :",
]:
    assert forbidden not in text, f"forbidden promotion present: {forbidden}"

print("GABA phenotype evidence-instantiation surface checks passed")
