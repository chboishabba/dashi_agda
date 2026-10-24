"""Static/source-bound regression for the Aquino/Maxwell/Epstein/CA case delta.

These checks do NOT certify Agda, the source documents, or historical truth.
The Agda kernel command is tracked separately in the roadmap.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Cognition/AquinoMaxwellEpsteinCAMaxCutExact.agda"
ROLLUP = ROOT / "DASHI/Cognition/Everything.agda"
ROADMAP = ROOT / "docs/research/aquino-maxwell-epstein-ca-maxcut-20261024.md"


def test_existing_prior_art_reused_not_cloned():
    text = OWNER.read_text()
    assert "import DASHI.Cognition.BannonCambridgeAnalyticaInfluenceInfrastructureExact as CA" in text
    assert "import DASHI.Cognition.EpsteinMasterPlanAttributionBoundaryExact as Plan" in text
    assert "import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy" in text
    assert "module DASHI.Cognition.AquinoMaxwellEpsteinCAMaxCutExact where" in text
    assert "import DASHI.Cognition.AquinoMaxwellEpsteinCAMaxCutExact" in ROLLUP.read_text()


def test_source_roots_roles_and_contradictions_are_retained():
    text = OWNER.read_text()
    for fragment in (
        "wylieRoot", "aquinoVallelyRoot", "fourthCircuitRoot",
        "ftcRoot", "houseJudiciaryRoot", "buaDOJRoot",
        "dojFBIMemoRoot", "epsteinCorrespondenceRoot",
        "judicialProceduralDecision", "regulatoryFinding",
        "attributedFirstPersonTestimony", "disputedAgencyReview",
        "1992-02-26", "2025-07",
    ):
        assert fragment in text
    assert "The House hearing and Wylie's submitted statement" in ROADMAP.read_text()


def test_attribution_firewalls_and_same_object_checks():
    text = OWNER.read_text()
    for fragment in (
        "robertMaxwellIsNotRobertMercer ()",
        "mindWarIsNotStargate ()",
        "aquinoToSCLUnpaid = refl",
        "aquinoToEpsteinUnpaid = refl",
        "promisMaxwellUnpaid = refl",
        "unifiedHierarchyUnpaid = refl",
        "existingCAMediaReuseUnpaid = refl",
        "existingMasterPlanHierarchyUnpaid = refl",
        "existingGenealogyDoesNotPromoteAnalogy = refl",
        "noWitnessMultiplication ()",
        "noTechniquePromotion ()",
        "noGuiltByAllegation ()",
        "noUnifiedCommandFromNetworkPath ()",
    ):
        assert fragment in text


def test_source_locator_or_attributed_local_owner():
    text = OWNER.read_text()
    assert "https://committees.parliament.uk/writtenevidence/89475/html/" in text
    assert "https://law.justia.com/cases/federal/appellate-courts/F2/957/139/2044/" in text
    assert "https://www.justice.gov/opa/media/1407001/dl" in text
    assert "TrumpMarALagoBannonBridgeExact" in text
    assert ROADMAP.exists()


def test_woogaroo_and_itir_prior_art_consumed_by_existing_owner():
    source = OWNER.read_text()
    owners = {
        "DASHI.Law.EvidenceProvenanceDependencyDagExact as Provenance":
            ROOT / "DASHI/Law/EvidenceProvenanceDependencyDagExact.agda",
        "DASHI.Core.ProvenanceClosureIndependenceExact as RootClosure":
            ROOT / "DASHI/Core/ProvenanceClosureIndependenceExact.agda",
        "DASHI.Core.SourceAcquisitionGeometryExact as Acquisition":
            ROOT / "DASHI/Core/SourceAcquisitionGeometryExact.agda",
        "DASHI.Core.ITIRInvestigationAcquisitionParetoExact as ITIR":
            ROOT / "DASHI/Core/ITIRInvestigationAcquisitionParetoExact.agda",
        "DASHI.Core.ITIRInvestigationWorkbenchProjectionExact as Workbench":
            ROOT / "DASHI/Core/ITIRInvestigationWorkbenchProjectionExact.agda",
        "DASHI.Core.MultipartSameObjectReconstructionExact as Multipart":
            ROOT / "DASHI/Core/MultipartSameObjectReconstructionExact.agda",
    }
    for module, path in owners.items():
        assert f"import {module}" in source
        assert path.exists(), f"Missing existing canonical owner: {path}"
    # Case-specific evidence is NOT imported from a separate unrelated legal fact.
    assert "import DASHI.Law.SensibLawWoogarooEvidenceDependencyMatrixExact" not in source


def test_bidi_source_independence_and_acquisition_stages():
    source = OWNER.read_text()
    for fragment in (
        "caseIndependentProducerRequirement = refl",
        "Provenance.reverseProvenance Provenance.independentCorroborationConsumer",
        "Provenance.independentProducerReceipt",
        "caseReprintsNotIndependent = refl",
        "caseMissingSourceIsNotAbsence = refl",
        "caseUIIsNotEvidence = refl",
        "caseIdentityNeedsFullReconstruction = refl",
        "discoveryDoesNotPayInspection ()",
        "proceduralFindingDoesNotPaySubstantiveFact ()",
        "eventTimeOverlapDoesNotPayCommand ()",
        "analogyDoesNotPayProgramme ()",
    ):
        assert fragment in source


def test_per_consumer_witnesses_remain_unpaid_without_original_artefacts():
    source = OWNER.read_text()
    for named_cut in (
        "sclTransferCut", "bannonWorkProductCut",
        "promisExecutableCut", "aquinoHistoricalTransferCut",
        "commandHierarchyCut",
    ):
        assert f"{named_cut} : CaseDependencyCut" in source
        assert f"{named_cut} = case-dependency-cut" in source
    assert source.count("true true true false false") >= 5
    assert "canonicalCaseCuts : List CaseDependencyCut" in source
    for target in (
        "sclCorporateWorkProductTarget", "bannonEpsteinFilmWorkProductTarget",
        "promisMaxwellExecutableTarget", "aquinoSCLTransferTarget",
    ):
        assert f"{target} = Acquisition.sourceAcquisitionTarget" in source
    assert source.count("false false false") >= 4


def test_itir_pareto_are_candidacy_not_evidence():
    source = OWNER.read_text()
    assert "sclCAOriginalContractRoute = ITIR.investigation-candidate" in source
    assert "bannonActualFilmRoute = ITIR.investigation-candidate" in source
    assert "caseFiveAxisAuthority = ITIR.investigationParetoView" in source
    assert source.count("true refl false refl false refl") >= 2
    assert "axes:illustrative-calibration" in source
    assert "numeric axes are scenario/routing calibration" in source
