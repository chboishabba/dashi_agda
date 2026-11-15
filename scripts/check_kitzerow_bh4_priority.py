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
panel_certificate = root / "DASHI/Biology/UniProtBH4PanelCertificateExact.agda"
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
wikimedia_identity = root / "DASHI/Wikimedia/BH4ProteinWikimediaIdentityExact.agda"
wikimedia_regression = root / "DASHI/Wikimedia/BH4ProteinWikimediaIdentityRegression.agda"
wikimedia_root = root / "DASHI/Wikimedia/BH4ProteinWikimediaEverything.agda"
wikimedia_acquisition = root / "scripts/acquire_wikimedia_bio_identity.py"
wikimedia_checker = root / "scripts/check_bh4_wikimedia_identity.py"
wikimedia_doc = root / "docs/biology/WikimediaBiologyIdentityAcquisition.md"
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
    panel_certificate,
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
    wikimedia_identity,
    wikimedia_regression,
    wikimedia_root,
    wikimedia_acquisition,
    wikimedia_checker,
    wikimedia_doc,
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
panel_certificate_text = panel_certificate.read_text()
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
wikimedia_identity_text = wikimedia_identity.read_text()
wikimedia_regression_text = wikimedia_regression.read_text()
wikimedia_root_text = wikimedia_root.read_text()
wikimedia_acquisition_text = wikimedia_acquisition.read_text()

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
    "UniProtPanelCertificate",
    "requestedMembers : Nat",
    "acquiredMembers : Nat",
    "failedMembers : Nat",
    "everyMemberBytePinned",
    "a56d2ea6bda05c47dacab457738c272f53ec58a53bcb12df88e2394797bd4fef",
    "ab0f7cd5427d5ab003220f6ddfc793b5c639389ef46c675ceb4a17ffcf183320",
    "completePanelCreatesAllocatorFlux",
]:
    assert token in panel_certificate_text, f"missing exact panel certificate token: {token}"

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
    "exactProteinPanelAcquisitionClosed",
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
    "exactPanelAcquisitionIsClosed",
    "allSixteenPanelRecordsArePinned",
    "completePanelStillDoesNotCreateAllocatorFlux",
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
    "UniProtBH4PanelCertificateExact",
    "BH4ProteinWikimediaIdentityExact",
    "BH4ProteinWikimediaIdentityRegression",
]:
    assert token in focused_text, f"missing focused-root max-cut import: {token}"
    assert token in external_root_text, f"missing external-root max-cut import: {token}"

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

for token in [
    "SnowballExternalIdentityAvailabilityExact",
    "P352",
    "P702",
    "P688",
    "Q1487359",
    "Q409532",
    "Q420604",
    "Q420766",
    "Q21115057",
    "Q14884995",
    "geneQidMayBeUsedAsProteinQidWithoutP688P702Witness",
    "wikipediaNarrativeCreatesMechanisticEvidence",
]:
    assert token in wikimedia_identity_text, f"missing Wikimedia identity token: {token}"

for token in [
    "geneQidCannotSilentlyBecomeProteinQid",
    "qidDoesNotCreateSequenceIdentity",
    "wikipediaDoesNotCreateMechanisticEvidence",
    "p352IdentityDoesNotCreateFlux",
]:
    assert token in wikimedia_regression_text, f"missing Wikimedia identity regression token: {token}"

for token in [
    "BH4ProteinWikimediaIdentityExact",
    "BH4ProteinWikimediaIdentityRegression",
]:
    assert token in wikimedia_root_text, f"missing Wikimedia focused-root import: {token}"

for token in [
    "from acquire_uniprot_bio_certificate import KITZEROW_BH4_PANEL",
    "WIKIDATA_SPARQL",
    "wdt:P352",
    "exact_p352_qids",
    "reciprocal_p688_paid",
    "qid_round_trip_paid",
    "complete_identity_panel_creates_biological_truth",
]:
    assert token in wikimedia_acquisition_text, f"missing Wikimedia acquisition token: {token}"

assert "explicitContactClaim" in acquisition_text
assert "not" in acquisition_text.lower() and "verifiedPrimaryContact" in acquisition_text
assert "uncited" in acquisition_text.lower()

print("kitzerow BH4 + external biology + NONG/NANG + Wikimedia identity max-cut regression: ok")
