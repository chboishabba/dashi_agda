import pytest

from scripts.mod97_relation_graph_compiler import (
    compile_and_certify,
    compile_relation_graph,
)


def test_unpaid_relation_classification_is_rejected() -> None:
    with pytest.raises(ValueError, match="classification"):
        compile_relation_graph(
            node_count=2,
            relation_records=[
                {
                    "left": 0,
                    "right": 1,
                    "relation": "conflict",
                    "classification_paid": False,
                }
            ],
        )


def test_requirement_without_paid_direction_is_rejected() -> None:
    with pytest.raises(ValueError, match="direction"):
        compile_relation_graph(
            node_count=2,
            relation_records=[
                {
                    "left": 0,
                    "right": 1,
                    "relation": "gluingRequirement",
                    "classification_paid": True,
                    "direction_paid": False,
                }
            ],
        )


def test_paid_canonical_relations_compile_without_wrongtype_collapse() -> None:
    graph = compile_relation_graph(
        node_count=3,
        relation_records=[
            {
                "left": 0,
                "right": 1,
                "relation": "conflict",
                "classification_paid": True,
            },
            {
                "left": 1,
                "right": 2,
                "relation": "gluingRequirement",
                "classification_paid": True,
                "direction_paid": True,
                "direction": "left_requires_right",
            },
            {
                "left": 0,
                "right": 2,
                "relation": "independent",
                "classification_paid": True,
            },
        ],
    )

    assert graph["conflicts"] == [[0, 1]]
    assert graph["requirements"] == [[1, 2]]
    assert graph["independent_pairs"] == [[0, 2]]
    assert graph["all_relation_classifications_paid"] is True
    assert graph["all_requirement_directions_paid"] is True


def test_mutual_requirement_expands_to_two_directed_closure_edges() -> None:
    graph = compile_relation_graph(
        node_count=2,
        relation_records=[
            {
                "left": 0,
                "right": 1,
                "relation": "gluingRequirement",
                "classification_paid": True,
                "direction_paid": True,
                "direction": "mutual_requirement",
            }
        ],
    )
    assert graph["requirements"] == [[0, 1], [1, 0]]


def test_compiler_can_feed_exact_beta_without_promoting_mechanism() -> None:
    receipt = compile_and_certify(
        node_count=3,
        relation_records=[
            {
                "left": 0,
                "right": 1,
                "relation": "conflict",
                "classification_paid": True,
            },
            {
                "left": 1,
                "right": 2,
                "relation": "independent",
                "classification_paid": True,
            },
        ],
    )

    assert receipt["beta_certificate"]["beta"] == 2
    assert receipt["beta_certificate"]["maximality_paid_by_finite_exhaustion"] is True
    assert receipt["input_payment"]["relation_graph_paid"] is True
    assert receipt["input_payment"]["requirement_direction_paid"] is True
    assert receipt["promotion"]["beta_for_supplied_paid_graph"] is True
    assert receipt["promotion"]["grokking_mechanism_paid"] is False
