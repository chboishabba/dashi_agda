#!/usr/bin/env python3
"""Exact Grafakos--Torres small-epsilon and Stage-3 row-factor audit."""

from __future__ import annotations

from fractions import Fraction as Q


def verify_source_small_epsilon() -> dict[str, object]:
    # Grafakos--Torres Section 5.10, diagonal specialisation
    # p=q=r'=3, alpha_1=alpha_2=1, n=3.
    alpha_1 = Q(1)
    alpha_2 = Q(1)
    dimension = Q(3)
    epsilon = Q(1, 4)
    cancellation_1 = Q(3)
    cancellation_2 = Q(3)

    # Equation (43).
    output = (
        alpha_1
        + alpha_2
        + dimension / Q(6)
        - epsilon * Q(2, 3)
    )
    left = (
        alpha_1 * Q(4, 3)
        + alpha_2 * Q(2, 3)
        + dimension / Q(3)
        - epsilon * Q(2, 3)
    )
    right = (
        alpha_1 * Q(2, 3)
        + alpha_2 * Q(4, 3)
        + dimension / Q(3)
        - epsilon * Q(2, 3)
    )

    assert left == Q(17, 6)
    assert right == Q(17, 6)
    assert output == Q(7, 3)

    target_1 = Q(3) * alpha_1 - epsilon
    target_2 = Q(3) * alpha_2 - epsilon
    margins = {
        "epsilon": epsilon,
        "target1AboveEpsilon": target_1 - epsilon,
        "order1AboveTarget": cancellation_1 - target_1,
        "target2AboveEpsilon": target_2 - epsilon,
        "order2AboveTarget": cancellation_2 - target_2,
    }
    assert all(margin > 0 for margin in margins.values())
    assert margins == {
        "epsilon": Q(1, 4),
        "target1AboveEpsilon": Q(5, 2),
        "order1AboveTarget": Q(1, 4),
        "target2AboveEpsilon": Q(5, 2),
        "order2AboveTarget": Q(1, 4),
    }

    # The Agda source receipt clears denominators by 12.
    assert 12 * epsilon == 3
    assert 12 * target_1 == 33
    assert 12 * cancellation_1 == 36
    assert 12 * (target_1 - epsilon) == 30
    assert 12 * (cancellation_1 - target_1) == 3

    return {
        "weights": (left, right, output),
        "epsilon": epsilon,
        "margins": margins,
    }


def verify_row_factorisation() -> dict[str, object]:
    separated = {
        ("output", "unsplit", "left-low"): "low-high",
        ("output", "unsplit", "right-low"): "low-low",
        ("output", "unsplit", "output-low"): "output-relocation",
        ("first", "direct", "left-low"): "direct-first-convolution",
        ("first", "direct", "right-low"): "low-low",
        ("first", "direct", "output-low"): "low-high",
        ("first", "swapped", "left-low"): "second-frozen",
        ("first", "swapped", "right-low"): "low-high",
        ("first", "swapped", "output-low"): "low-high",
        ("second", "unsplit", "left-low"): "low-high",
        ("second", "unsplit", "right-low"): "second-frozen",
        ("second", "unsplit", "output-low"): "low-high",
    }
    assert len(separated) == 12
    assert len(set(separated.values())) == 5
    assert sum(value == "direct-first-convolution" for value in separated.values()) == 1
    assert separated[("first", "swapped", "left-low")] == "second-frozen"

    overlap = {
        (owner, geometry): f"{owner}-overlap"
        for owner in ("output", "first", "second")
        for geometry in ("near", "transition", "residual")
    }
    assert len(overlap) == 9
    assert len(set(overlap.values())) == 3
    for owner in ("output", "first", "second"):
        assert len(
            {
                overlap[(owner, geometry)]
                for geometry in ("near", "transition", "residual")
            }
        ) == 1

    total_rows = len(separated) + len(overlap)
    raw_slots = total_rows * 3
    independent_families = len(set(separated.values())) + len(set(overlap.values()))
    structural_independent_slots = independent_families * 3

    resolved_family = "output-relocation"
    resolved_family_count = 1
    resolved_slots = resolved_family_count * 3
    remaining_families = independent_families - resolved_family_count
    remaining_slots = structural_independent_slots - resolved_slots

    assert total_rows == 21
    assert raw_slots == 63
    assert independent_families == 8
    assert structural_independent_slots == 24
    assert resolved_family in set(separated.values())
    assert resolved_slots == 3
    assert remaining_families == 7
    assert remaining_slots == 21

    return {
        "separatedRows": len(separated),
        "overlapRows": len(overlap),
        "rawCoefficientSlots": raw_slots,
        "structuralIndependentFamilies": independent_families,
        "structuralIndependentCoefficientSlots": structural_independent_slots,
        "resolvedFamily": resolved_family,
        "resolvedCoefficientSlots": resolved_slots,
        "remainingIndependentFamilies": remaining_families,
        "remainingIndependentCoefficientSlots": remaining_slots,
    }


def main() -> int:
    source = verify_source_small_epsilon()
    factor = verify_row_factorisation()
    weights = ", ".join(str(value) for value in source["weights"])
    print(
        "verified Grafakos--Torres Section-5.10 source witness "
        f"({weights}) with epsilon={source['epsilon']} and five positive margins; "
        f"factorised {factor['separatedRows']} separated plus "
        f"{factor['overlapRows']} overlap rows from "
        f"{factor['rawCoefficientSlots']} raw slots through "
        f"{factor['structuralIndependentFamilies']} families / "
        f"{factor['structuralIndependentCoefficientSlots']} structural slots, "
        f"then resolved {factor['resolvedFamily']} to leave "
        f"{factor['remainingIndependentFamilies']} families / "
        f"{factor['remainingIndependentCoefficientSlots']} live slots"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
