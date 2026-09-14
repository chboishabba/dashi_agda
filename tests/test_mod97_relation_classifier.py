import pytest

from scripts.mod97_relation_classifier import classify_pair_receipt
from scripts.mod97_relation_graph_compiler import compile_and_certify


def test_underpowered_pair_cannot_be_classified() -> None:
    receipt = classify_pair_receipt(
        left=0,
        right=1,
        left_damage=2,
        right_damage=2,
        joint_damage=7,
        interaction_threshold=1,
        adequacy_power_paid=False,
    )
    assert receipt["classification_paid"] is False
    assert receipt["classification"] == "underpowered"
    assert receipt["relation"] is None


def test_positive_excess_above_threshold_classifies_conflict() -> None:
    receipt = classify_pair_receipt(
        left=0,
        right=1,
        left_damage=2,
        right_damage=2,
        joint_damage=7,
        interaction_threshold=1,
        adequacy_power_paid=True,
    )
    assert receipt["interaction_excess"] == 3
    assert receipt["classification"] == "conflict"
    assert receipt["relation"] == "conflict"
    assert receipt["classification_paid"] is True


def test_additive_pair_classifies_independent_when_direction_is_unavailable() -> None:
    receipt = classify_pair_receipt(
        left=0,
        right=1,
        left_damage=2,
        right_damage=3,
        joint_damage=5,
        interaction_threshold=1,
        adequacy_power_paid=True,
    )
    assert receipt["classification"] == "independent"
    assert receipt["relation"] == "independent"
    assert receipt["classification_paid"] is True
    assert receipt["requirement_direction_paid"] is False


def test_current_observation_never_manufactures_gluing_requirement() -> None:
    receipt = classify_pair_receipt(
        left=0,
        right=1,
        left_damage=2,
        right_damage=2,
        joint_damage=4,
        interaction_threshold=1,
        adequacy_power_paid=True,
    )
    assert receipt["classification"] == "independent"
    assert receipt["relation"] == "independent"
    assert receipt["requirement_direction_paid"] is False
    assert receipt["gluing_requirement_available"] is False


def test_paid_classifier_receipts_feed_graph_compiler_without_field_rewrite() -> None:
    conflict = classify_pair_receipt(
        left=0,
        right=1,
        left_damage=2,
        right_damage=2,
        joint_damage=7,
        interaction_threshold=1,
        adequacy_power_paid=True,
    )
    independent = classify_pair_receipt(
        left=1,
        right=2,
        left_damage=2,
        right_damage=3,
        joint_damage=5,
        interaction_threshold=1,
        adequacy_power_paid=True,
    )

    compiled = compile_and_certify(
        node_count=3,
        relation_records=[conflict, independent],
    )
    assert compiled["compiled_graph"]["conflicts"] == [[0, 1]]
    assert compiled["compiled_graph"]["independent_pairs"] == [[1, 2]]
    assert compiled["beta_certificate"]["beta"] == 2


def test_negative_nat_damage_is_rejected() -> None:
    with pytest.raises(ValueError, match="non-negative"):
        classify_pair_receipt(
            left=0,
            right=1,
            left_damage=-1,
            right_damage=2,
            joint_damage=3,
            interaction_threshold=1,
            adequacy_power_paid=True,
        )
