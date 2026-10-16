from pathlib import Path

root = Path(__file__).resolve().parents[1]

atlas = root / "DASHI/Biology/KitzerowBH4EvidenceAtlasExact.agda"
priority = root / "DASHI/Biology/KitzerowPriorityGenealogyExact.agda"
regression = root / "DASHI/Biology/KitzerowBH4EvidenceRegression.agda"
registry = root / "DASHI/Biology/KitzerowBH4SourceRegistry.agda"
maxcut = root / "DASHI/Biology/KitzerowBH4EvidenceMaxCut.agda"
focused = root / "DASHI/Biology/KitzerowBH4EvidenceEverything.agda"
acquisition = root / "docs/biology/KitzerowBH4PriorityAcquisition.md"
external_core = root / "DASHI/Biology/ExternalBiologyEvidenceCore.agda"
mapping = root / "DASHI/Biology/ExternalBiologyMappingRevisionExact.agda"
admission = root / "DASHI/Biology/ExternalBiologyConsumerAdmissionExact.agda"
uniprot = root / "DASHI/Biology/UniProtExternalKnowledgeExact.agda"
bridge = root / "DASHI/Biology/KitzerowUniProtCrossPollinationExact.agda"
external_regression = root / "DASHI/Biology/ExternalBiologyRegression.agda"
external_root = root / "DASHI/Biology/ExternalBiologyEverything.agda"
uniprot_acquisition = root / "scripts/acquire_uniprot_bio_certificate.py"

for path in [
    atlas,
    priority,
    regression,
    registry,
    maxcut,
    focused,
    acquisition,
    external_core,
    mapping,
    admission,
    uniprot,
    bridge,
    external_regression,
    external_root,
    uniprot_acquisition,
]:
    assert path.exists(), f"missing Kitzerow/external-biology max-cut file: {path.relative_to(root)}"

atlas_text = atlas.read_text()
priority_text = priority.read_text()
regression_text = regression.read_text()
registry_text = registry.read_text()
maxcut_text = maxcut.read_text()
focused_text = focused.read_text()
acquisition_text = acquisition.read_text()
external_core_text = external_core.read_text()
mapping_text = mapping.read_text()
admission_text = admission.read_text()
uniprot_text = uniprot.read_text()
bridge_text = bridge.read_text()
external_regression_text = external_regression.read_text()
external_root_text = external_root.read_text()
uniprot_acquisition_text = uniprot_acquisition.read_text()

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

for token in [
    "DatasetSnapshot",
    "ProteinRef",
    "SequenceWitness",
    "EvidenceBundle",
    "BiologicalClaim",
    "datasetAssertionCreatesBiologicalTruth",
    "reviewedStatusImpliesDirectExperimentalProof",
]:
    assert token in external_core_text, f"missing external-biology core token: {token}"

for token in [
    "CrossDatabaseMapping",
    "RevisionReceipt",
    "crossReferenceAloneCreatesEntityIdentity",
    "absenceFromCurrentDatasetMeansBiologicalNonexistence",
]:
    assert token in mapping_text, f"missing mapping/revision token: {token}"

for token in [
    "BiologicalConsumer",
    "ConsumerAssessment",
    "consumerAdmissionCreatesBiologicalTruth",
    "clinicalActionConsumer",
]:
    assert token in admission_text, f"missing consumer-admission token: {token}"

for token in [
    "P09417",
    "DHPR_HUMAN",
    "RHEA:17869",
    "01EAB47E5C55913647DB7DBAD571D960",
    "qdprToPDB9DTW",
    "qdprToAlphaFold",
    "qdprMechanismAssessment",
]:
    assert token in uniprot_text, f"missing UniProt witness token: {token}"

for token in [
    "qdprBH4AvailabilityAdapter",
    "Atlas.bh4Availability",
    "qdprNodeSupportConfirmsWholeGraph",
    "uniprotAnnotationEstablishesKitzerowPriority",
    "uniprotAnnotationEstablishesAttributionBreach",
]:
    assert token in bridge_text, f"missing Kitzerow/UniProt bridge token: {token}"

for token in [
    "datasetAssertionDoesNotCreateTruth",
    "mappingDoesNotCollapseIdentity",
    "admissionDoesNotCreateTruth",
    "qdprClaimDoesNotConfirmWholeKitzerowGraph",
]:
    assert token in external_regression_text, f"missing external regression token: {token}"

for token in [
    "KitzerowUniProtCrossPollinationExact",
    "ExternalBiologyRegression",
]:
    assert token in focused_text, f"missing focused-root external biology import: {token}"

for token in [
    "ExternalBiologyEvidenceCore",
    "UniProtExternalKnowledgeExact",
    "KitzerowUniProtCrossPollinationExact",
    "ExternalBiologyRegression",
]:
    assert token in external_root_text, f"missing external biology root import: {token}"

for token in [
    "raw_sha256",
    "x-uniprot-release",
    "uniProtKBCrossReferences",
    "database_assertion_creates_biological_truth",
]:
    assert token in uniprot_acquisition_text, f"missing UniProt acquisition token: {token}"

assert "explicitContactClaim" in acquisition_text
assert "not" in acquisition_text.lower() and "verifiedPrimaryContact" in acquisition_text
assert "uncited" in acquisition_text.lower()

print("kitzerow BH4 + external biology max-cut regression: ok")
