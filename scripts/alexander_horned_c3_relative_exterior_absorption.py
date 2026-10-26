#!/usr/bin/env python3
"""Exact rational controls for RELATIVE Hatcher compact-map absorption.

Source: A. Hatcher, Algebraic Topology, Example 2B.2 (printed pp. 171-172).
Formal donor: Mathlib IsCompact.elim_directed_cover; adaptation: DASHI #1244.
This model is in R, NOT the 3D linked Hatcher X_n. It tests assumptions
of the new Lean interface, not the missing wild geometry or group colimit.
"""
import json
from fractions import Fraction as F


def radius(n: int) -> F:
    """Closed nested H_n = [-1/(n+1), 1/(n+1)] in the real line."""
    if n < 0:
        raise ValueError("Stage index must be nonnegative")
    return F(1, n + 1)


def compact_interval_stage_witness(low=F(1, 3), high=F(1, 2)) -> int:
    """Exact N with [low, high] disjoint from H_N, no floating point."""
    assert F(0) < low <= high
    n = 0
    while radius(n) >= low:
        n += 1
    assert low > radius(n)
    if n:
        assert low <= radius(n - 1)
    return n


def audit(depth=256):
    # Each H_n is closed, and H_{n+1} subset H_n; B=intersection H_n={0}.
    for n in range(depth):
        assert radius(n + 1) < radius(n)
    # Compact continuous image f([0,1])=[1/3,1/2] stays in E=R\{0}.
    n = compact_interval_stage_witness()
    assert n == 3  # H_2 includes 1/3; H_3 does not.
    # Test exact points of the entire affine map (endpoints give universal
    # interval lower/upper bounds, the samples are secondary controls).
    for k in range(depth + 1):
        t = F(k, depth)
        f_t = F(1, 3) + t / 6
        assert F(1, 3) <= f_t <= F(1, 2)
        assert f_t > radius(n)
    # The stages definitely do NOT cover ambient R: 0 is in every H_n.
    # They cover only E=R\{0}. Thus an ambient-univ hypothesis would fail.
    assert all(-radius(k) <= 0 <= radius(k) for k in range(depth))
    # Without compactness: discrete N -> 1/(k+1) has image in E,
    # but for every stage n the point at index k=n still lies in H_n.
    for k in range(depth):
        assert F(1, k + 1) == radius(k)
    # Without image avoidance: t -> t/2 on [0,1] hits limit B at t=0.
    assert F(0, 2) == 0
    assert all(radius(k) > 0 for k in range(depth))
    return {
        "status": "PASS",
        "relative_compact_image_stage": n,
        "ambient_univ_cover": False,
        "noncompact_domain_counterexample": "f(n)=1/(n+1) remains in H_n",
        "limit_avoidance_counterexample": "g(0)=0 in intersection H_n",
        "exact_rational_stages_checked": depth,
        "3d_hatcher_handlebody_constructed": False,
        "lean_kernel_verified": False,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
