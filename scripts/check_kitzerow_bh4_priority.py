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
bh4_system = root / "DASHI/Biology/BH4SystemStateExact.agda"
oxide = root / "DASHI/Biology/NitrogenOxideSpeciesCouplingExact.agda"
n2o = root / "DASHI/Biology/NitrousOxideMetabolismEvidenceExact.agda"
nongin_oxide = root / "DASHI/Biology/NonginNangNitrogenOxideRefinementExact.agda"
system_maxcut = root / "DASHI/Biology/KitzerowBH4SystemNongNangMaxCutExact.agda"
system_regression = root / "DASHI/Biology/BH4NongNangMaxCutRegression.agda"
implementation_plan = root / "docs/superpowers/plans/2026-10-17-bh4-nong-nang-maxcut.md"

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
    bh4_system,
    oxide,
    n2o,
    nongin_oxide,
    system_maxcut,
    system_regression,
    implementation_plan,
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
bh4_system_text = bh4_system.read_text()
oxide_text = oxide.read_text()
n2o_text = n2o.read_text()
nongin_oxide_text = nongin_oxide.read_text()
system_maxcut_text = system_maxcut.read_text()
system_regression_text = system_regression.read_text()

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
    "0852F9F0CA38AB1C",
    "sha256:7ef73e73b15eb967db526cc5ba2970965992ff348e758b57057e1bc61def3936",
    "qdprToPDB9DTW",
    "qdprToAlphaFold",
    "qdprMechanismAssessment",
]:
    assert token in uniprot_text, f"missing UniProt witness token: {token}"

for token in [
    "BH4PoolState",
    "EnzymeDemand",
    "BH4SystemState",
    "FluxBalanceWitness",
    "reactionAnnotationPaysWholeFluxBalance",
    "cofactorRequirementProvesCompetitionBetweenConsumers",
]:
    assert token in bh4_system_text, f"missing BH4 system token: {token}"

for token in [
    "nitricOxide",
    "nitrousOxide",
    "nitricOxideNotNitrousOxide",
    "NOSCouplingTransitionWitness",
    "proteinPresenceEstablishesUncoupling",
    "nitrousOxideIsCanonicalNOSProduct",
]:
    assert token in oxide_text, f"missing nitrogen-oxide coupling token: {token}"

for token in [
    "10.1503/cmaj.230196",
    "cobalaminOxidationReceipt",
    "methionineSynthaseReceipt",
    "nitrousOxideEvidenceCreatesNOSUncouplingProof",
    "cobalaminOxidationEstablishesBH4Depletion",
]:
    assert token in n2o_text, f"missing N2O evidence token: {token}"

for token in [
    "Nongin.OnePointOneCarrier",
    "chemicalFrameSensitiveConsumer",
    "coarseNitrogenOxideCannotServeFineConsumer",
    "userGenealogyRecordsNongEqualsNang",
    "nongNangAliasIdentifiesNitricOxide",
]:
    assert token in nongin_oxide_text, f"missing Nongin/NANG refinement token: {token}"

for token in [
    "P30793",
    "P30047",
    "Q03393",
    "P35270",
    "P61457",
    "P09417",
    "P29475",
    "P35228",
    "P29474",
    "P00439",
    "P07101",
    "P17752",
    "Q8IWU9",
    "Q6ZNB7",
    "P49815",
    "P42345",
    "qdprRegenerationEdge",
    "bh4ToNOSCouplingEdge",
    "nosToTSC2Edge",
    "liveResiduals",
    "nitrousOxideLaneCreatesKitzerowMechanism",
]:
    assert token in system_maxcut_text, f"missing BH4 system max-cut token: {token}"

for token in [
    "nitricOxideIsNotNitrousOxide",
    "coarseNitrogenOxideCannotServeFineChemicalConsumer",
    "proteinPresenceDoesNotEstablishNOSUncoupling",
    "reactionAnnotationDoesNotPayWholeFluxBalance",
    "nangCobalaminLaneDoesNotBecomeNOSLane",
    "isolatedNodesDoNotConfirmKitzerowWholeGraph",
]:
    assert token in system_regression_text, f"missing system regression token: {token}"

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
    "KitzerowBH4SystemNongNangMaxCutExact",
    "BH4NongNangMaxCutRegression",
    "NonginNangNitrogenOxideRefinementExact",
]:
    assert token in focused_text, f"missing focused-root BH4/NONG/NANG import: {token}"
    assert token in external_root_text, f"missing external-root BH4/NONG/NANG import: {token}"

for token in [
    "raw_sha256",
    "x-uniprot-release",
    "uniProtKBCrossReferences",
    "database_assertion_creates_biological_truth",
    "--kitzerow-bh4-panel",
    "KITZEROW_BH4_PANEL",
    "P35270",
    "P29474",
    "Q6ZNB7",
    "complete_panel_creates_whole_model_confirmation",
]:
    assert token in uniprot_acquisition_text, f"missing UniProt acquisition token: {token}"

assert "explicitContactClaim" in acquisition_text
assert "not" in acquisition_text.lower() and "verifiedPrimaryContact" in acquisition_text
assert "uncited" in acquisition_text.lower()

print("kitzerow BH4 + external biology + NONG/NANG system max-cut regression: ok")
