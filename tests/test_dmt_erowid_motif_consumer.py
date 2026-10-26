"""Erowid: original-paper aggregate arithmetic vs actual motif transition evidence."""
import copy
import importlib.util
import json
from fractions import Fraction as F
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "dmt_erowid_audit", ROOT/"scripts/audit_dmt_erowid_motif_consumer.py")
module = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(module)


def bridge():
    return json.loads((ROOT /
        "Docs/receipts/DMTRecurringMotifErowidPriorArtBridge20261025.json"
        ).read_text(encoding="utf-8"))


def test_published_source_counts_preserved_without_raw_data_claim():
    report = module.published_counts()
    assert report["source_doi"] == "10.3389/fpsyg.2024.1397064"
    assert report["report_count"] == 39586
    assert report["DMT_report_count"] == 1121
    assert report["visual_effect_sentences"] == 143520
    assert report["reported_chi_square_N"] == 2246254
    assert report["raw_report_data_accessed"] is False
    assert report["subject_or_report_level_entity_prevalence_computed"] is False


def test_source_percent_and_chi_square_denominator_do_not_naively_match():
    result = module.published_counts()
    assert result["source_stated_visual_fraction_percent"] == "6.52"
    assert result["calculated_percent_if_chi_square_N_is_denominator"] == 6.389304
    assert result["counts_not_arithmetically_equal_to_published_percent"]
    assert result["cross_denominator_reconciliation_found"] is False


def test_no_faked_recurrence_from_stationary_marginals():
    result = module.stationary_marginal_counterexample()
    assert result["all_kernels_same_one_time_marginals"] is True
    assert result["observed_transition_joint_distributions_are_different"]
    assert result["toy_stationary_marginals"] == ["1/3", "1/3", "1/3"]
    assert result["lattice_to_tunnel_probabilities"] == {
        "absorbing_identity": "0",
        "deterministic_three_cycle": "1",
        "uniform_iid_mixing": "1/3"}
    assert result["transition_kernel_estimated_from_erowid"] is False


def test_exact_stochastic_matrix_guard_rejects_invalid_claim():
    with pytest.raises(ValueError, match="Invalid"):
        module.validate_stochastic(((F(1),),))
    with pytest.raises(ValueError, match="Invalid"):
        module.validate_stochastic(((F(2), F(-1), F(0)),)*3)
    for matrix in module.KERNELS.values():
        module.validate_stochastic(matrix)
        assert module.projected_distribution(module.INITIAL, matrix) == module.INITIAL


def test_noah_taxonomy_categories_and_known_existing_operators():
    doc = bridge()
    paper = doc["original_published_research"]
    assert paper["published_categories"] == [
        "Pattern", "Movement", "Color", "Entities",
        "Global visual alterations", "Distortion", "Affect", "Other"]
    assert len(doc["already_in_repo"]) == 8
    assert any(x["path"].endswith("/VisualMotifTransitionOperator.agda")
               for x in doc["already_in_repo"])
    assert doc["raw_data_governance"]["permission_obtained"] is False
    assert doc["raw_data_governance"]["raw_report_corpus_acquired"] is False
    assert doc["no_empirical_markov_kernel_fitted"] is True


def test_source_revisions_fail_closed():
    altered = bridge()
    altered["original_published_research"]["reported_dataset"]["dmt_reports"] = 999
    with pytest.raises(ValueError, match="Paper numbers changed"):
        module.published_counts(altered)
    altered = bridge()
    altered["original_published_research"]["doi"] = "fake-source"
    with pytest.raises(ValueError, match="DOI"):
        module.published_counts(altered)


def test_consumer_types_do_not_borrow_fmri_or_temporal_authority():
    report = module.audit()
    assert report["paper_category_is_not_a_verified_external_entity"]
    assert report["source"]["measured_motif_transition_matrix_computed"] is False
    assert report["source"]["independent_replication_of_original_narrative_classifier"] is False
    assert "same observations" in report["model_discriminator"]


def test_aggregate_recurrence_bridge_is_independent_of_fmri_world():
    doc = bridge()
    assert doc["provenance"]["original_DMT_source_world_counts_unchanged"]
    assert doc["pareto_recommendation"]["not_a_required_original_GFC_prerequisite"]
    assert doc["empirical_consumer_fibres"][2]["status"] == (
        "not_empirically_measured_from_published_study")
