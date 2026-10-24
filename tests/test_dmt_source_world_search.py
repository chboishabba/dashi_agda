"""Source-world validation/proof-search contracts, NOT proof of paper results."""
import copy
import importlib.util
from pathlib import Path
import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "dmt_world_search", ROOT/"scripts/dmt_source_world_search.py")
engine = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(engine)


def world():
    return engine.load_world()


def test_original_source_tree_and_lineages_are_exact():
    w = world()
    assert len(w["observed_git_tree"]["files"]) == 56
    assert len([x for x in w["observed_git_tree"]["files"]
                if x["path"].startswith("fMRI/")]) == 40
    assert w["counts"]["repository_paired_subjects"] == 20
    assert w["counts"]["original_pnas_static_n"] == 16
    assert w["counts"]["readme_unspecified_n"] == 15
    assert w["safety"]["send_email"] is False
    sources = {s["id"]: s for s in w["sources"]}
    assert sources["source_eeg_repro"]["lineage_root"] == "pnas2023"
    assert sources["pnas_reanalysis2025"]["lineage_root"] == "pnas2023"


def test_source_claim_is_not_empirical_reproduction():
    result = {x["consumer"]: x for x in engine.claim_status(world())}
    assert result["c_public_files"]["state"] == "source_attested_only"
    assert result["c_static_reproduction"]["state"] == "acquisition_blocked"
    assert "original_static_fd" in result["c_static_reproduction"]["missing"]
    assert "data_use_review" in result["c_static_reproduction"]["missing"]
    assert result["c_external_entity"]["state"] == "acquisition_blocked"
    assert result["c_published_precursor"]["state"] == "source_attested_only"


def test_acquisition_frontier_does_not_claim_promotion():
    candidates = {x["id"]: x for x in engine.action_candidates(world())}
    assert candidates["a_original_motion_primary"]["state"] == "candidate_admissible"
    assert candidates["b_rights_review"]["state"] == "candidate_admissible"
    assert candidates["c_source_bytes"]["state"] == "source_prerequisite_blocked"
    assert candidates["d_replay_static"]["state"] == "source_prerequisite_blocked"
    assert candidates["e_phase_matrices"]["state"] == "candidate_admissible"
    assert not any(x["promotion_authorised"] for x in candidates.values())
    # Pareto must respect WHICH consumer is affected, not merely count leaves:
    # Sanders phase matrices are not "dominated" by a cheaper neural-QC search.
    assert candidates["a_original_motion_primary"]["pareto"]
    assert candidates["b_rights_review"]["pareto"]
    assert candidates["e_phase_matrices"]["pareto"]


def test_shortest_hypothetical_paths_are_not_acquisitions():
    w = world()
    before = copy.deepcopy(w)
    static = engine.hypothetical_plan(w, "c_static_reproduction")
    assert static["status"] == "conditional_plan_only"
    assert static["hypothetical_actions"] == [
        "a_original_motion_primary", "b_rights_review",
        "c_source_bytes", "d_replay_static"]
    assert static["evidence_created"] is False
    precursor = engine.hypothetical_plan(w, "c_temporal_replication")
    assert precursor["hypothetical_actions"] == ["e_phase_matrices"]
    assert w == before


def test_malformed_source_dependency_fails_closed():
    w = world()
    w["source_dependencies"].append({
        "from": "pnas_reanalysis2025", "to": "pnas2023",
        "type": "independent_replication"})
    with pytest.raises(ValueError, match="independent replication"):
        engine.validate_world(w)


def test_missing_evidence_not_known_absent_and_rights_not_implied():
    w = world()
    art = next(x for x in w["artifacts"] if x["id"] == "data_use_review")
    assert art["status"] == "notLocated"
    art["status"] = "knownAbsent"
    with pytest.raises(ValueError, match="negative-search"):
        engine.validate_world(w)
    art["status"] = "present"
    with pytest.raises(ValueError, match="specific locator"):
        engine.validate_world(w)


def test_dangling_artifacts_and_unsafe_actuation_are_rejected():
    w = world()
    w["claims"][0]["requires"].append("imaginary_author_permission")
    with pytest.raises(ValueError, match="nonexistent"):
        engine.validate_world(w)
    w = world()
    w["safety"]["send_email"] = True
    with pytest.raises(ValueError, match="External contact"):
        engine.validate_world(w)


def test_agda_source_world_instantiates_existing_reopening():
    path = ROOT/"DASHI/Cognition/ConsciousRealismDMTSourceWorldExact.agda"
    text = path.read_text(encoding="utf8")
    assert "import DASHI.Core.AttributedSourceCore" in text
    assert "import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact" in text
    assert "import DASHI.Core.CostedResidualInformationChoiceExact" in text
    assert "Acquire.obligationFromNotLocated" in text
    assert "Acquire.oneEdgeAcquisitionReopening" in text
    assert "qcDoesNotDirectlyEstablishExternalAgent" in text
    assert "phaseMatricesDoNotDirectlyEstablishExternalAgent" in text
    focus = (ROOT/"DASHI/Cognition/ConsciousRealismDMTEverything.agda").read_text()
    assert "ConsciousRealismDMTSourceWorldExact" in focus


def test_source_world_mutation_of_exact_git_inventory_fails():
    w = world()
    w["observed_git_tree"]["files"][0]["git_blob_sha1"] = "0" * 40
    with pytest.raises(ValueError, match="diverges"):
        engine.validate_world(w)
