from pathlib import Path

root = Path(__file__).resolve().parents[1]

atlas = root / "DASHI/Biology/KitzerowBH4EvidenceAtlasExact.agda"
priority = root / "DASHI/Biology/KitzerowPriorityGenealogyExact.agda"
regression = root / "DASHI/Biology/KitzerowBH4EvidenceRegression.agda"

assert atlas.exists(), "missing KitzerowBH4EvidenceAtlasExact.agda"
assert priority.exists(), "missing KitzerowPriorityGenealogyExact.agda"
assert regression.exists(), "missing KitzerowBH4EvidenceRegression.agda"

atlas_text = atlas.read_text()
priority_text = priority.read_text()
regression_text = regression.read_text()

for token in [
    "scientificSupport",
    "priorityStatus",
    "contactStatus",
    "wholeModelConfirmed",
    "wholeModelConfirmedIsFalse",
    "ojhaNOToTSC2ToMTOR",
    "stanfordReticularThalamus",
    "italyConnectivitySubtypes",
    "japanCellularStress",
    "brazilBH4Review",
    "naviauxThreeHit",
    "melilloNeuroimmuneCascade",
    "iaccDevelopmentalSystems",
]:
    assert token in atlas_text, f"missing atlas token: {token}"

for token in [
    "publicDisclosure2023",
    "formalPreprint2024",
    "priorArtBeforeKitzerow",
    "explicitContactClaim",
    "verifiedPrimaryContact",
    "independentConvergence",
    "attributionConcern",
    "plagiarismProven",
    "plagiarismProvenIsFalse",
]:
    assert token in priority_text, f"missing priority token: {token}"

for token in [
    "supportDoesNotImplyPriority",
    "priorityDoesNotImplyContact",
    "contactDoesNotImplyPlagiarism",
    "nodeSupportDoesNotConfirmWholeGraph",
]:
    assert token in regression_text, f"missing regression token: {token}"

print("kitzerow BH4 priority regression: ok")
