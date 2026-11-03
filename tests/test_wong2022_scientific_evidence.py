"""Red/green tests for Wong 2022 DASHI-only evidence integrity.

These test a source contract. They do not type-check Agda proof terms.
"""
from pathlib import Path

from scripts.check_wong2022_scientific_evidence import (
    CORE,
    DOC,
    ROOT,
    SCIENTIFIC,
    SOURCE,
    AGGREGATE,
    check_agda,
    inspect_source_bundle,
    load_source_bundle,
)


def test_current_wong2022_source_contract_is_consistent():
    bundle = load_source_bundle(ROOT)
    assert not inspect_source_bundle(bundle)


def test_missing_safe_flag_is_rejected():
    bundle = load_source_bundle(ROOT)
    bundle[CORE] = bundle[CORE].replace("{-# OPTIONS --safe #-}", "")
    assert any("Golden core" in text or "safe" in text for text in inspect_source_bundle(bundle))


def test_postulate_and_unsolved_meta_are_rejected():
    bundle = load_source_bundle(ROOT)
    bundle[CORE] += "\npostulate\n  unwarranted : Set\n"
    assert any("postulate" in text for text in inspect_source_bundle(bundle))
    bundle = load_source_bundle(ROOT)
    bundle[CORE] += "\nunsafeHole : Set\nunsafeHole = {! !}\n"
    assert any("trust escape/hole" in text for text in inspect_source_bundle(bundle))


def test_missing_primary_doi_or_titre_is_rejected():
    bundle = load_source_bundle(ROOT)
    bundle[SOURCE] = bundle[SOURCE].replace(
        "10.1038/s41467-022-28386-6", "missing-source", 
    )
    assert any("10.1038" in text for text in inspect_source_bundle(bundle))
    bundle = load_source_bundle(ROOT)
    bundle[SOURCE] = bundle[SOURCE].replace('"1.7"', '"unknown"')
    assert any('"1.7"' in text for text in inspect_source_bundle(bundle))


def test_missing_original_stoichiometric_owner_reuse_is_rejected():
    bundle = load_source_bundle(ROOT)
    bundle[SCIENTIFIC] = bundle[SCIENTIFIC].replace(
        "Stoich.certifyMetabolicStoichiometry bridge",
        "unpaid physical conservation",
    )
    assert any("Stoich.certifyMetabolicStoichiometry" in text for text in inspect_source_bundle(bundle))


def test_deferred_connector_import_and_missing_root_integration_are_rejected():
    bundle = load_source_bundle(ROOT)
    bundle[CORE] += "\nimport DASHI.Wikimedia.SensibLawFakeConnector\n"
    assert any("deferred" in text for text in inspect_source_bundle(bundle))
    bundle = load_source_bundle(ROOT)
    bundle[AGGREGATE] = bundle[AGGREGATE].replace(
        "import DASHI.Biology.Wong2022ScientificMetabolicBridgeExact", ""
    )
    assert any("Wong2022ScientificMetabolicBridgeExact" in text for text in inspect_source_bundle(bundle))


def test_missing_roadmap_is_rejected():
    bundle = load_source_bundle(ROOT)
    bundle.pop(DOC)
    assert any("missing file" in text for text in inspect_source_bundle(bundle))


def test_checker_absence_does_not_masquerade_as_acceptance(monkeypatch):
    from scripts import check_wong2022_scientific_evidence as audit

    monkeypatch.setattr(audit.shutil, "which", lambda _exe: None)
    state = check_agda(Path(ROOT), required=True)
    assert state["state"] == "unavailable"
    assert state["success"] is False


def test_source_stereochemical_descriptor_drift_stays_review_blocking():
    from scripts.check_wong2022_scientific_evidence import LEDGER

    bundle = load_source_bundle(ROOT)
    bundle[LEDGER] = bundle[LEDGER].replace(
        "ZAGRKAFMISFKIO-IAPIXIRKSA-N", "unreviewed-identifier"
    )
    assert any(
        "ZAGRKAFMISFKIO-IAPIXIRKSA-N" in failure
        for failure in inspect_source_bundle(bundle)
    )


def test_patent_is_a_distinct_attributed_source_not_a_biological_proof():
    from scripts.check_wong2022_scientific_evidence import PATENT_ATLAS

    bundle = load_source_bundle(ROOT)
    assert not inspect_source_bundle(bundle)
    bundle[PATENT_ATLAS] = bundle[PATENT_ATLAS].replace(
        "10.1128/AEM.02137-14", "unattributed-2014-paper"
    )
    assert any(
        "10.1128/AEM.02137-14" in failure
        for failure in inspect_source_bundle(bundle)
    )


def test_patent_does_not_replace_original_2014_research_owner():
    from scripts.check_wong2022_scientific_evidence import PATENT_ATLAS

    bundle = load_source_bundle(ROOT)
    bundle[PATENT_ATLAS] = bundle[PATENT_ATLAS].replace(
        "robinsonPanaccione2014", "lostOriginalResearchOwner"
    )
    assert any(
        "robinsonPanaccione2014" in failure
        for failure in inspect_source_bundle(bundle)
    )


def test_patent_golden_core_forbids_claim_to_experiment_promotion():
    from scripts.check_wong2022_scientific_evidence import PATENT_GOLDEN

    bundle = load_source_bundle(ROOT)
    bundle[PATENT_GOLDEN] = bundle[PATENT_GOLDEN].replace(
        "patentClaimNotObservedExperiment",
        "patentClaimTreatedAsExperimentalEvidence",
    )
    assert any(
        "patentClaimNotObservedExperiment" in failure
        for failure in inspect_source_bundle(bundle)
    )
    bundle = load_source_bundle(ROOT)
    bundle[PATENT_GOLDEN] += "\npostulate\n  invented : Set\n"
    assert any("trust escape/hole" in failure for failure in inspect_source_bundle(bundle))


def test_patent_family_does_not_promote_to_legal_clearance():
    from scripts.check_wong2022_scientific_evidence import PATENT_ATLAS

    bundle = load_source_bundle(ROOT)
    bundle[PATENT_ATLAS] = bundle[PATENT_ATLAS].replace(
        "freedomToOperateOpinionPaidIsFalse",
        "falseLegalClearanceClaim",
    )
    assert any(
        "freedomToOperateOpinionPaidIsFalse" in failure
        for failure in inspect_source_bundle(bundle)
    )
