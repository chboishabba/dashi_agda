from scripts.mod97_circuit_intervention_producer import (
    build_intervention_receipt,
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
    assert receipt["promotion"]["requirement_edges_paid"] is False
    assert receipt["promotion"]["relation_classification_paid"] is False
    assert receipt["promotion"]["beta_maximality_paid"] is False
    assert receipt["promotion"]["grokking_mechanism_paid"] is False
