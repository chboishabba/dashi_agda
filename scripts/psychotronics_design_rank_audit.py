#!/usr/bin/env python3
"""Exact *synthetic* design-rank audit for a proposed iTorus/Starship study.

No human measurements, device specifications, coil output or clinical data
are contained in this file. It demonstrates why a binary active/sham
comparison is non-identifying when electromagnetic drive and a perceptible
sound/vibration cue change together.

Columns: intercept, actual electromagnetic field E, sensory cue C, E*C.
Rows are idealised instrumentally verified exposure settings, not device
controls that have been implemented or shown physically achievable.

No external packages and no randomness; row rank uses exact Fractions.
Run: python3 scripts/psychotronics_design_rank_audit.py
"""
from fractions import Fraction
from typing import Iterable, Sequence

COLUMNS = ("intercept", "EM_field", "sensory_cue", "interaction")
ROWS = {
    "off_no_cue": (0, 0),
    "field_with_no_cue": (1, 0),
    "cue_with_no_field": (0, 1),
    "field_with_cue": (1, 1),
}


def row(field: int, cue: int) -> tuple[int, int, int, int]:
    assert field in (0, 1) and cue in (0, 1)
    return (1, field, cue, field * cue)


def rank_exact(matrix: Iterable[Sequence[int]]) -> int:
    """Gaussian elimination over rational numbers; no FP tolerance."""
    a = [[Fraction(x) for x in r] for r in matrix]
    if not a:
        return 0
    n = len(a[0])
    if any(len(r) != n for r in a):
        raise ValueError("ragged design")
    pivot_row = 0
    for col in range(n):
        pivot = next((i for i in range(pivot_row, len(a))
                      if a[i][col] != 0), None)
        if pivot is None:
            continue
        a[pivot_row], a[pivot] = a[pivot], a[pivot_row]
        fac = a[pivot_row][col]
        a[pivot_row] = [x / fac for x in a[pivot_row]]
        for i in range(len(a)):
            if i == pivot_row:
                continue
            fac = a[i][col]
            a[i] = [u - fac * v for u, v in zip(a[i], a[pivot_row])]
        pivot_row += 1
        if pivot_row == len(a):
            break
    return pivot_row


def design(names: Sequence[str]) -> list[tuple[int, int, int, int]]:
    return [row(*ROWS[name]) for name in names]


def predict(rows: Iterable[Sequence[int]], beta: Sequence[int]) -> list[int]:
    return [sum(x * b for x, b in zip(r, beta)) for r in rows]


def audit() -> dict[str, int | bool]:
    # Sham=0 field and cue, active=1 field *and* cue.
    coupled = design(["off_no_cue", "field_with_cue"])
    # Matched-cue RCT: the *conditional* EM contrast at C=1 is identifiable
    # from 01 versus 11, even without estimating EM main vs interaction.
    # This requires a real, safely masked, measured identical cue level.
    matched_cue = design(["cue_with_no_field", "field_with_cue"])
    # Adding sound-only distinguishes a cue main effect but cannot
    # distinguish EM main effect from EM×cue interaction.
    partial = design(["off_no_cue", "cue_with_no_field", "field_with_cue"])
    # Ideal 2x2 independently controlled factors: possible only after
    # independent bench documentation and credible sensory masking.
    orthogonal = design([
        "off_no_cue", "field_with_no_cue",
        "cue_with_no_field", "field_with_cue"
    ])

    assert rank_exact(coupled) == 2
    assert rank_exact(matched_cue) == 2
    assert rank_exact(partial) == 3
    assert rank_exact(orthogonal) == 4

    # Here field-only and cue-only are observationally indistinguishable.
    assert predict(coupled, (0, 1, 0, 0)) == [0, 1]
    assert predict(coupled, (0, 0, 1, 0)) == [0, 1]
    assert predict(orthogonal, (0, 1, 0, 0)) != predict(
        orthogonal, (0, 0, 1, 0)
    )

    # Two distinct coefficient vectors yield the *same* pair of
    # matched-cue predictions (and same conditional field contrast);
    # beta_EM and beta_EMxCue individually remain unidentified.
    assert predict(matched_cue, (0, 1, 0, 0)) == [0, 1]
    assert predict(matched_cue, (0, 0, 0, 1)) == [0, 1]
    matched_contrast = tuple(b - a for a, b in zip(
        matched_cue[0], matched_cue[1]
    ))
    assert matched_contrast == (0, 1, 0, 1)

    # In partial design, field-only and interaction-only also coincide.
    assert predict(partial, (0, 1, 0, 0)) == [0, 0, 1]
    assert predict(partial, (0, 0, 0, 1)) == [0, 0, 1]

    # A nominally four-arm study can still be rank-deficient if E and C
    # remain collinear. Number of arms is not the identifiability criterion.
    duplicate = design([
        "off_no_cue", "off_no_cue",
        "field_with_cue", "field_with_cue"
    ])
    assert rank_exact(duplicate) == 2

    return {
        "coupled_two_arm_rank": rank_exact(coupled),
        "matched_cue_two_arm_rank": rank_exact(matched_cue),
        "matched_cue_conditional_EM_contrast_exists": True,
        "EM_main_and_interaction_separately_identified_by_two_arms": False,
        "partial_three_arm_rank": rank_exact(partial),
        "independently_manipulated_two_by_two_rank": rank_exact(orthogonal),
        "duplicate_four_arm_rank": rank_exact(duplicate),
        "coefficient_count": len(COLUMNS),
        "measured_participants": 0,
        "physical_device_receipt": False,
        "real_world_blinding_established": False,
    }


if __name__ == "__main__":
    for name, value in audit().items():
        print(f"{name}: {value}")
