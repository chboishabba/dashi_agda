from scripts.mod97_closed_compatible_capacity import (
    certify_closed_compatible_capacity,
    is_closed_compatible,
)


def test_conflict_free_is_not_enough_when_requirement_is_open() -> None:
    assert is_closed_compatible({0}, conflicts=set(), requirements={(0, 1)}) is False
    assert is_closed_compatible({0, 1}, conflicts=set(), requirements={(0, 1)}) is True


def test_exact_capacity_ignores_extra_blocked_raw_capacity() -> None:
    base = certify_closed_compatible_capacity(
        node_count=3,
        conflicts={(0, 1)},
        requirements=set(),
    )
    extra_blocked = certify_closed_compatible_capacity(
        node_count=4,
        conflicts={(0, 1), (2, 3)},
        requirements=set(),
    )
    assert base["beta"] == 2
    assert extra_blocked["beta"] == 2
    assert extra_blocked["raw_candidate_count"] == 4


def test_removing_conflict_strictly_increases_exact_capacity() -> None:
    blocked = certify_closed_compatible_capacity(
        node_count=3,
        conflicts={(0, 1)},
        requirements=set(),
    )
    clear = certify_closed_compatible_capacity(
        node_count=3,
        conflicts=set(),
        requirements=set(),
    )
    assert blocked["beta"] == 2
    assert clear["beta"] == 3


def test_requirement_closure_changes_admissible_family_not_relation_identity() -> None:
    receipt = certify_closed_compatible_capacity(
        node_count=3,
        conflicts={(0, 2)},
        requirements={(0, 1)},
    )
    assert receipt["beta"] == 2
    assert receipt["maximal_families"] == [[0, 1], [1, 2]]
    assert receipt["maximality_paid_by_finite_exhaustion"] is True
    assert receipt["subsets_examined"] == 8


def test_certificate_does_not_claim_grokking_mechanism() -> None:
    receipt = certify_closed_compatible_capacity(
        node_count=2,
        conflicts=set(),
        requirements=set(),
    )
    assert receipt["maximality_paid_by_finite_exhaustion"] is True
    assert receipt["relation_classification_paid"] is False
    assert receipt["grokking_mechanism_paid"] is False
