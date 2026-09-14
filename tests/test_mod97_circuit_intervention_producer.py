import subprocess
import sys

from scripts.mod97_circuit_intervention_producer import (
    build_intervention_receipt,
    canonical_damage_microunits,
    interaction_excess,
    select_candidates_from_training,
)


def test_candidate_selection_uses_training_activations_only() -> None:
    training_activations = [
        [4.0, 0.0, 1.0, 0.5],
        [2.0, 0.0, 3.0, 0.5],
    ]
    assert select_candidates_from_training(training_activations, 2) == [0, 2]


def test_candidate_selection_is_invariant_to_held_out_changes() -> None:
    training_activations = [
        [4.0, 0.0, 1.0],
        [2.0, 0.0, 3.0],
    ]
    held_out_a = [[0.0, 1000.0, 0.0]]
    held_out_b = [[0.0, -1000.0, 0.0]]

    selected_a = select_candidates_from_training(training_activations, 2)
    selected_b = select_candidates_from_training(training_activations, 2)

    assert selected_a == selected_b == [0, 2]
    assert held_out_a != held_out_b


def test_interaction_excess_is_joint_minus_singletons() -> None:
    assert interaction_excess(0.2, 0.3, 0.8) == 0.3000000000000001


def test_signed_loss_effects_are_canonicalised_to_nonnegative_damage_nats() -> None:
    assert canonical_damage_microunits(0.0012344) == 1234
    assert canonical_damage_microunits(-0.5) == 0


def test_raw_receipt_does_not_promote_relations_or_beta() -> None:
    receipt = build_intervention_receipt(
        checkpoint_path="epoch-01000.pt",
        checkpoint_sha256="abc",
        selected_units=[0, 2],
        baseline_test_loss=1.0,
        singleton_effects={0: 0.2, 2: 0.3},
        pair_effects={(0, 2): 0.8},
    )

    assert receipt["selection"]["carrier"] == "training activations"
    assert receipt["selection"]["held_out_outcome_used"] is False
    assert receipt["evaluation"]["carrier"] == "held-out test split"
    assert receipt["evaluation"]["effect_orientation"] == "larger held-out loss is worse"
    assert receipt["evaluation"]["canonical_damage_scale"] == 1000000
    assert receipt["evaluation"]["singleton_effects"][0]["damage_microunits"] == 200000
    assert receipt["promotion"]["requirement_edges_paid"] is False
    assert receipt["promotion"]["relation_classification_paid"] is False
    assert receipt["promotion"]["beta_maximality_paid"] is False
    assert receipt["promotion"]["grokking_mechanism_paid"] is False


def test_same_layer_post_relu_ablations_do_not_pay_directional_requirements() -> None:
    receipt = build_intervention_receipt(
        checkpoint_path="epoch-01000.pt",
        checkpoint_sha256="abc",
        selected_units=[0, 2],
        baseline_test_loss=1.0,
        singleton_effects={0: 0.2, 2: 0.3},
        pair_effects={(0, 2): 0.8},
    )

    topology = receipt["requirement_evidence"]
    assert topology["candidate_layer"] == "single shared hidden layer"
    assert topology["intervention_site"] == "post-ReLU hidden activation"
    assert topology["directed_hidden_to_hidden_path"] is False
    assert topology["same_layer_pair_ablations_pay_direction"] is False
    assert topology["directional_requirement_rule"] == "not available from this producer"
    assert receipt["promotion"]["requirement_edges_paid"] is False


def test_direct_script_help_resolves_repo_local_imports() -> None:
    result = subprocess.run(
        [sys.executable, "scripts/mod97_circuit_intervention_producer.py", "--help"],
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr
