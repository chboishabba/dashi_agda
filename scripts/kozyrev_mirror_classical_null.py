#!/usr/bin/env python3
"""Exact rational 2-D specular-reflection *toy* for a Kozyrev-like spiral.

NOT a model of the patent's uniquely specified geometry (none is supplied).
NOT Maxwell/acoustic wave propagation, a 3-D instrument, or evidence for torsion.
Source mathematics: ordinary specular reflection and angular momentum balance.
The geometry is a synthetic four-direction polygonal widening spiral.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import json


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1]


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def scale(x, a):
    return (x * a[0], x * a[1])


def parity(a):
    """Reflect the plane through the vertical axis."""
    return (-a[0], a[1])


def reflected(direction, tangent):
    """Reflect across the tangent line, preserving exact squared norm."""
    norm = dot(tangent, tangent)
    if not norm:
        raise ValueError("zero-length surface segment")
    return sub(scale(2 * dot(direction, tangent) / norm, tangent), direction)


def reflected_wall_impulse(direction, tangent):
    """Momentum delivered to wall, in arbitrary equal-ray momentum units."""
    return sub(direction, reflected(direction, tangent))


def sample_wall_torque(point, direction, tangent):
    """Out-of-plane angular impulse on wall, in synthetic geometry units."""
    return cross(point, reflected_wall_impulse(direction, tangent))


def synthetic_profile(steps=12, radial_step=Q(1, 5), start=Q(1)):
    """One arbitrary *polygon*, not the patented continuous surface."""
    if type(steps) is not int or not 2 <= steps <= 64:
        raise ValueError("steps must be an integer from 2 to 64")
    if start <= 0 or radial_step < 0:
        raise ValueError("radius must be positive; increment nonnegative")
    axes = ((Q(1), Q(0)), (Q(0), Q(1)), (Q(-1), Q(0)), (Q(0), Q(-1)))
    return [scale(start + radial_step * i, axes[i % 4]) for i in range(steps + 1)]


def ray_fixture(vertices, direction=(Q(3), Q(1))):
    """Independent unit-weight ray at each segment midpoint. No occlusion."""
    if dot(direction, direction) == 0:
        raise ValueError("direction cannot be zero")
    rows = []
    for a, b in zip(vertices, vertices[1:]):
        t = sub(b, a)
        mid = scale(Q(1, 2), add(a, b))
        outgoing = reflected(direction, t)
        impulse = reflected_wall_impulse(direction, t)
        rows.append({
            "point": mid, "tangent": t, "incoming": direction,
            "outgoing": outgoing, "wall_impulse": impulse,
            "wall_torque": cross(mid, impulse),
            "ray_energy_before": dot(direction, direction),
            "ray_energy_after": dot(outgoing, outgoing),
        })
    return rows


def fraction_str(q):
    return str(q)


def report():
    source = {
        "kind": "synthetic_2d_specular_polygon_no_material_calibration",
        "patent_source": "RU2122446C1; Kaznacheev and Trofimov; 1996 filed, 1998 published",
        "nominal_plate_height_mm": 2800,
        "nominal_plate_width_mm": 1200,
        "described_focus_mm": 500,
        "unresolved_thickness_tenths_mm": [5, 15],
        "spiral_elements_described": [8, 9, 10],
        "round_open_elements_described": [4, 6],
    }
    vertices = synthetic_profile()
    ordinary = ray_fixture(vertices)
    mirrored = ray_fixture([parity(v) for v in vertices], parity((Q(3), Q(1))))
    circular = ray_fixture(synthetic_profile(radial_step=Q(0)))
    return {
        "source_constraints": source,
        "limits": [
            "polygon profile is illustrative and is not derived from patent drawings",
            "independent rays are sampled at segment midpoints; not a transport or scattering solution",
            "squared direction norm is an equal-ray proxy, not calibrated joules",
            "torque is an arbitrary impulse unit; not steady physical torque in N m",
            "parity is exact; physical 3D, absorption, temperature, frequency and shadowing absent",
        ],
        "segments": len(ordinary),
        "energy_conservation_all": all(x["ray_energy_before"] == x["ray_energy_after"] for x in ordinary + mirrored + circular),
        "momentum_balance_all": all(add(x["outgoing"], x["wall_impulse"]) == x["incoming"] for x in ordinary + mirrored + circular),
        "parity_torque_reversal_all": all(a["wall_torque"] == -b["wall_torque"] for a, b in zip(ordinary, mirrored)),
        "spiral_wall_torque_sum": fraction_str(sum((x["wall_torque"] for x in ordinary), Q(0))),
        "mirrored_wall_torque_sum": fraction_str(sum((x["wall_torque"] for x in mirrored), Q(0))),
        "circular_control_wall_torque_sum": fraction_str(sum((x["wall_torque"] for x in circular), Q(0))),
        "physical_effect_established": False,
        "novel_torsion_effect_established": False,
        "patented_apparatus_geometry_identified": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="machine-readable synthetic report")
    args = parser.parse_args()
    result = report()
    if args.json:
        print(json.dumps(result, sort_keys=True, indent=2))
    else:
        for k, v in result.items():
            print(f"{k}: {v}")


if __name__ == "__main__":
    main()
