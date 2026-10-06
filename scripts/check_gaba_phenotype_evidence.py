from pathlib import Path

p = Path("DASHI/Biology/GABAPhenotypeEvidenceExact.agda")
assert p.exists(), "missing GABAPhenotypeEvidenceExact.agda"

text = p.read_text(encoding="utf-8")

required = [
    "record RegionalGABAEvidence",
    "associationDoesNotImplyCausalSufficiency",
    "regionalGABADifferenceDoesNotImplyWholeBrainDifference",
    "groupMeanDoesNotClassifyIndividual",
    "diagnosisDoesNotDetermineGABALevel",
    "thoughtSuppressionEvidenceDoesNotPromoteToEmotionSuppression",
    "noAttachmentBridgeFromSynchronyWithoutReceipt",
    "noNeuroinflammationBridgeFromGABAWithoutReceipt",
    "schmitz2017ThoughtSuppression",
    "autismGABAMetaAnalysis2024",
]

for needle in required:
    assert needle in text, f"missing required surface: {needle}"

for forbidden in [
    "autismCausedByLowGABA :",
    "adhdCausedByLowGABA :",
    "insecureAttachmentByDefinition :",
]:
    assert forbidden not in text, f"forbidden causal promotion present: {forbidden}"

print("GABA phenotype evidence surface checks passed")
