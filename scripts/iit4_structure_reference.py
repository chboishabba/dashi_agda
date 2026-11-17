#!/usr/bin/env python3
"""Finite IIT-4 cause-effect-structure arithmetic reference.

This module owns the composition-layer arithmetic that is independent of the
mechanism-MIP search itself:

* relation candidates are non-empty subsets of distinctions;
* a relation face contributes joint-overlap size times the weakest relatum's
  phi density over its unique cause/effect purview units;
* structure integrated information Phi is the plain sum of distinction and
  relation phi values.

The worked-example calibration records the published 2023 aB complex values as
an external regression oracle; it is not used to manufacture distinctions for
new systems.  New distinction values must come from a mechanism/purview MIP
implementation or an external PyPhi oracle.
"""
from __future__ import annotations

from itertools import combinations
from typing import Iterable, Sequence


def nonempty_relation_candidates(distinctions: Sequence[str]) -> tuple[tuple[str, ...], ...]:
    return tuple(
        combo
        for degree in range(1, len(distinctions) + 1)
        for combo in combinations(distinctions, degree)
    )


def relation_phi_from_overlap(
    distinction_phi: float,
    unique_purview_size: int,
    joint_overlap_size: int,
) -> float:
    if unique_purview_size <= 0:
        raise ValueError("unique purview size must be positive")
    if joint_overlap_size <= 0:
        return 0.0
    if distinction_phi < 0:
        raise ValueError("distinction phi must be non-negative")
    return joint_overlap_size * distinction_phi / unique_purview_size


def relation_phi(
    relata: Iterable[tuple[float, int]],
    joint_overlap_size: int,
) -> float:
    relata = tuple(relata)
    if not relata or joint_overlap_size <= 0:
        return 0.0
    return min(
        relation_phi_from_overlap(phi_d, purview_size, joint_overlap_size)
        for phi_d, purview_size in relata
    )


def big_phi(distinction_phis: Iterable[float], relation_phis: Iterable[float]) -> float:
    values = tuple(distinction_phis) + tuple(relation_phis)
    if any(value < 0 for value in values):
        raise ValueError("IIT-4 structure phi terms must be non-negative")
    return sum(values)


def worked_example_calibration() -> dict:
    """Published IIT-4 (2023) Fig. 1/2/4 aB calibration oracle.

    Source: current PyPhi worked example reproducing Albantakis et al. 2023.
    The values are intentionally labelled rounded/source-derived, not computed
    by this module's mechanism search.
    """
    return {
        "source": "Albantakis et al. 2023 / PyPhi worked-example calibration",
        "complex": "aB",
        "system_phi_s_rounded": 0.17,
        "distinction_count": 3,
        "phi_d_rounded": [0.33, 0.32, 0.07],
        "relation_count": 7,
        "a_aB_relation_phi_paper_rounded": 0.035,
        "a_aB_relation_phi_current_pyphi_rounded": 0.036,
        "sum_phi_distinctions_rounded": 0.72,
        "sum_phi_relations_rounded": 0.84,
        "big_phi_rounded": 1.56,
        "big_phi_is_system_phi_s": False,
    }


if __name__ == "__main__":
    print(worked_example_calibration())
