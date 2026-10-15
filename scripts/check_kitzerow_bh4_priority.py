from pathlib import Path

root = Path(__file__).resolve().parents[1]

atlas = root / "DASHI/Biology/KitzerowBH4EvidenceAtlasExact.agda"
priority = root / "DASHI/Biology/KitzerowPriorityGenealogyExact.agda"
regression = root / "DASHI/Biology/KitzerowBH4EvidenceRegression.agda"
registry = root / "DASHI/Biology/KitzerowBH4SourceRegistry.agda"
maxcut = root / "DASHI/Biology/KitzerowBH4EvidenceMaxCut.agda"
focused = root / "DASHI/Biology/KitzerowBH4EvidenceEverything.agda"
acquisition = root / "docs/biology/KitzerowBH4PriorityAcquisition.md"

for path in [atlas, priority, regression, registry, maxcut, focused, acquisition]:
    assert path.exists(), f"missing Kitzerow max-cut file: {path.relative_to(root)}"

atlas_text = atlas.read_text()
priority_text = priority.read_text()
regression_text = regression.read_text()
registry_text = registry.read_text()
maxcut_text = maxcut.read_text()
acquisition_text = acquisition.read_text()

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
    "bh4CytoprotectionPriorArt",
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
    "stanfordContactEvidence",
    "princetonAssessment",
    "PublicationReferenceStatus",
    "publicationReferenceStatus",
    "kitzerowNotFoundInArticleText",
    "creatorReportsUncited",
    "stanford2025ReferenceEvidence",
    "ojha2026ReferenceEvidence",
    "brazil2025ReferenceEvidence",
]:
    assert token in priority_text, f"missing priority/reference token: {token}"

for token in [
    "supportDoesNotImplyPriority",
    "priorityDoesNotImplyContact",
    "contactDoesNotImplyPlagiarism",
    "nodeSupportDoesNotConfirmWholeGraph",
    "stanfordContactRemainsUnverifiedPrimary",
    "priorArtSubtractionIsRequired",
    "contactDoesNotImplyArticleCitation",
]:
    assert token in regression_text, f"missing regression token: {token}"

for token in [
    "SourceRecord",
    "kitzerow2024BH4",
    "kitzerow2024Allostatic",
    "kitzerowTimeline",
    "eichwald2023BH4",
    "ojha2026",
    "stanford2025",
]:
    assert token in registry_text, f"missing registry token: {token}"

for token in [
    "KitzerowBH4SourceRegistry",
    "KitzerowBH4EvidenceAtlasExact",
    "KitzerowPriorityGenealogyExact",
    "KitzerowBH4EvidenceRegression",
]:
    assert token in maxcut_text, f"missing max-cut import: {token}"

assert "explicitContactClaim" in acquisition_text
assert "not" in acquisition_text.lower() and "verifiedPrimaryContact" in acquisition_text
assert "uncited" in acquisition_text.lower()

print("kitzerow BH4 priority max-cut regression: ok")
