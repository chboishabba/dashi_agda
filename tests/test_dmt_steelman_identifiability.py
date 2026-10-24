"""Exact synthetic no-identification witness and source-bounded DMT steelman."""
import importlib.util
import json
from fractions import Fraction as F
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "dmt_steelman", ROOT / "scripts/audit_dmt_steelman_identifiability.py"
)
module = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(module)


def test_exact_small_word_probabilities_positive_and_normalized():
    assert module.probability((1,), state_meaning="M2_agent_story") == F(14, 25)
    assert module.probability((0,), state_meaning="M1_endogenous") == F(11, 25)
    assert sum(module.probability((x,), state_meaning="M2_agent_story")
               for x in (0, 1)) == 1


def test_every_binary_observed_word_is_equivalent_up_to_six_steps():
    result = module.enumerate_observational_equivalence(6)
    assert result["all_word_probabilities_equal"]
    assert result["checked_binary_words"] == 126
    assert not result["inference_to_external_entity_permitted"]
    assert not result["any_finite_observation_word_separates_these_models"]


def test_finite_witness_validates_horizon_and_observable_alphabet():
    with pytest.raises(ValueError, match="horizon"):
        module.enumerate_observational_equivalence(0)
    with pytest.raises(ValueError, match="horizon"):
        module.enumerate_observational_equivalence(11)
    with pytest.raises(ValueError, match="0/1"):
        module.probability((2,), state_meaning="M2_agent_story")
    with pytest.raises(ValueError, match="Unknown causal"):
        module.probability((1,), state_meaning="M9_fake")


def test_hidden_target_independence_and_leakage_illustration():
    result = module.hidden_target_accuracy()
    assert set(result["all_observation_only_predictors_accuracy"].values()) == {"1/2"}
    assert result["best_unleaked_target_accuracy"] == "1/2"
    assert result["leaked_target_accuracy"] == "1"
    assert not result["source_dmt_study_had_concealed_target"]


def test_adversarial_witness_does_not_claim_real_data():
    report = module.audit(5)
    assert report["model_status"].startswith("synthetic semantic-relabelling")
    assert report["observational_equivalence"]["checked_binary_words"] == 62
    assert "not an empirical" in report["model_status"]
    assert report["hidden_target"]["source_dmt_study_had_concealed_target"] is False


def test_research_value_ledger_does_not_promote_ontology_or_model():
    dossier = json.loads((ROOT / "Docs/receipts/DMTSteelmanDiscriminatorValue20261024.json").read_text())
    assert dossier["schema"] == "dashi-dmt-steelman-discriminator-v1"
    assert dossier["critical_no_go"]["implementation"].endswith(
        "audit_dmt_steelman_identifiability.py")
    assert any(x["doi"] == "10.1093/nc/niaf069" for x in dossier["primary_roots"])
    assert any(x["id"] == "P1_no_identification" for x in dossier["ranked_research_payoffs"])
    assert any(x["id"] == "M1b" for x in dossier["adversarial_model_families"])
    assert dossier["status"]["new_human_data_recovered"] is False
    assert dossier["status"]["empirical_discriminator_computed"] is False
    assert len(dossier["outcome_matrix"]) >= 6
    assert dossier["source_independence"]["sanders2026"].find("overlap") >= 0
