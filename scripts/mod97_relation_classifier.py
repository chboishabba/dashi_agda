#!/usr/bin/env python3
"""Producer-safe relation classification for the current Mod97 pair observation.

The current observation carries non-negative singleton/joint damage values and a
predeclared interaction threshold. It can pay conflict versus independent only
when the adequacy/power gate is paid. It cannot manufacture gluingRequirement:
requirement direction is non-identifiable from the symmetric pair-ablation
surface and must come from a richer, separately paid observation.
"""

from __future__ import annotations

from typing import Any


def classify_pair_receipt(
    *,
    left: int,
    right: int,
    left_damage: int,
    right_damage: int,
    joint_damage: int,
    interaction_threshold: int,
    adequacy_power_paid: bool,
) -> dict[str, Any]:
    if left == right:
        raise ValueError("pair endpoints must be distinct")
    for name, value in (
        ("left_damage", left_damage),
        ("right_damage", right_damage),
        ("joint_damage", joint_damage),
        ("interaction_threshold", interaction_threshold),
    ):
        if not isinstance(value, int) or value < 0:
            raise ValueError(f"{name} must be a non-negative integer")

    excess = max(0, joint_damage - (left_damage + right_damage))

    if not adequacy_power_paid:
        classification = "underpowered"
        relation = None
        classification_paid = False
    elif excess > interaction_threshold:
        classification = "conflict"
        relation = "conflict"
        classification_paid = True
    else:
        classification = "independent"
        relation = "independent"
        classification_paid = True

    return {
        "left": left,
        "right": right,
        "left_damage": left_damage,
        "right_damage": right_damage,
        "joint_damage": joint_damage,
        "interaction_excess": excess,
        "interaction_threshold": interaction_threshold,
        "threshold_rule": "conflict iff interaction_excess > interaction_threshold",
        "adequacy_power_paid": adequacy_power_paid,
        "observation_surface": "symmetric singleton/joint pair-ablation damage",
        "requirement_direction_paid": False,
        "gluing_requirement_available": False,
        "classification": classification,
        "relation": relation,
        "classification_paid": classification_paid,
        "boundary": (
            "This classifier pays only conflict/independent on the current observation. "
            "It cannot emit gluingRequirement because opposite directed closure worlds "
            "can expose the same pair-ablation effects."
        ),
    }
