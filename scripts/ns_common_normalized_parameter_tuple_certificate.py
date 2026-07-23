#!/usr/bin/env python3
"""Finite common-parameter diagnostic for the four normalized NS boundary faces.

This is a deterministic falsification/candidate certificate only.  It searches no
continuum state space and carries no theorem authority.  Its purpose is to check
that one literal tuple, rather than four independently tuned tuples, survives the
same finite Galerkin face tests.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import numpy as np

from ns_boundary_face_galerkin_search import bisect_factor, inward_derivative, rescale_mask
from ns_periodic_galerkin_core import (
    fmt,
    h1_squared,
    make_geometry,
    packet_metrics,
    random_state,
)

SCHEMA = "ns_common_normalized_parameter_tuple_certificate.v1"

GAMMA_STAR = 0.07
PACKET_FRACTION_STAR = 0.64
OFF_PACKET_STAR = 0.36
SIZE_SQUARED_CEILING = 45.0
TARGET_SHELL = 0
CUTOFF = 3
SAMPLES = 16


def digest(payload: Any) -> str:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


def candidate_face_state(g, seed: int, face: str) -> np.ndarray:
    u = random_state(g, seed, energy=1.0)
    all_mask = np.ones(len(g.modes), dtype=bool)
    center_mask = g.shell_weights[TARGET_SHELL] > 0.999999
    outside_mask = g.shell_weights[2] > 1.0e-12

    if face == "gamma_floor":
        return bisect_factor(
            g,
            u,
            center_mask,
            lambda x: packet_metrics(g, x, TARGET_SHELL)["gamma"],
            GAMMA_STAR,
            increasing=True,
        )
    if face == "packet_fraction_floor":
        return bisect_factor(
            g,
            u,
            outside_mask,
            lambda x: packet_metrics(g, x, TARGET_SHELL)["packet"]
            / packet_metrics(g, x, TARGET_SHELL)["total"],
            PACKET_FRACTION_STAR,
            increasing=False,
        )
    if face == "off_packet_ceiling":
        return bisect_factor(
            g,
            u,
            outside_mask,
            lambda x: packet_metrics(g, x, TARGET_SHELL)["off"],
            OFF_PACKET_STAR,
            increasing=True,
        )
    if face == "size_ceiling":
        factor = np.sqrt(SIZE_SQUARED_CEILING / h1_squared(g, u))
        return rescale_mask(g, u, all_mask, factor)
    raise ValueError(face)


def common_region_checks(metrics: dict[str, float], size_squared: float) -> dict[str, bool]:
    packet_fraction = metrics["packet"] / metrics["total"]
    tolerance = 1.0e-8
    return {
        "gamma_floor": metrics["gamma"] >= GAMMA_STAR - tolerance,
        "packet_fraction_floor": packet_fraction >= PACKET_FRACTION_STAR - tolerance,
        "off_packet_ceiling": metrics["off"] <= OFF_PACKET_STAR + tolerance,
        "size_ceiling": size_squared <= SIZE_SQUARED_CEILING + tolerance,
    }


def build(samples: int = SAMPLES) -> dict[str, Any]:
    g = make_geometry(CUTOFF, max_shell=2)
    face_names = (
        "gamma_floor",
        "packet_fraction_floor",
        "off_packet_ceiling",
        "size_ceiling",
    )
    faces: dict[str, Any] = {}

    for face in face_names:
        values: list[float] = []
        witnesses: list[dict[str, Any]] = []
        for n in range(samples):
            seed = 7001 + 97 * n
            u = candidate_face_state(g, seed, face)
            inward, metrics = inward_derivative(g, u, face)
            size_squared = h1_squared(g, u)
            checks = common_region_checks(metrics, size_squared)
            values.append(inward)
            witnesses.append(
                {
                    "seed": seed,
                    "inward_derivative": fmt(inward),
                    "gamma": fmt(metrics["gamma"]),
                    "packet_fraction": fmt(metrics["packet"] / metrics["total"]),
                    "off_packet": fmt(metrics["off"]),
                    "size_squared": fmt(size_squared),
                    "common_region_checks": checks,
                    "in_common_region": all(checks.values()),
                }
            )

        worst_index = min(range(samples), key=lambda i: values[i])
        faces[face] = {
            "sample_count": samples,
            "minimum_inward_derivative": fmt(values[worst_index]),
            "maximum_inward_derivative": fmt(max(values)),
            "nonpositive_count": sum(value <= 0.0 for value in values),
            "strict_inward_on_sample": all(value > 0.0 for value in values),
            "all_witnesses_in_common_region": all(
                witness["in_common_region"] for witness in witnesses
            ),
            "worst_witness": witnesses[worst_index],
        }

    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "authority": "finite_deterministic_common_tuple_diagnostic_only",
        "cutoff": CUTOFF,
        "target_shell": TARGET_SHELL,
        "selected_tuple": {
            "gamma_floor": fmt(GAMMA_STAR),
            "packet_fraction_floor": fmt(PACKET_FRACTION_STAR),
            "off_packet_ceiling": fmt(OFF_PACKET_STAR),
            "size_squared_ceiling": fmt(SIZE_SQUARED_CEILING),
        },
        "packet_fraction_plus_off_packet": fmt(
            PACKET_FRACTION_STAR + OFF_PACKET_STAR
        ),
        "faces": faces,
        "all_faces_strict_inward_on_sample": all(
            result["strict_inward_on_sample"] for result in faces.values()
        ),
        "all_face_witnesses_use_common_region": all(
            result["all_witnesses_in_common_region"] for result in faces.values()
        ),
        "promotion": {
            "finite_common_tuple_is_continuum_proof": False,
            "strict_Dini_inwardness": False,
            "global_invariant_region": False,
        },
    }
    payload["sha256"] = digest(payload)
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--samples", type=int, default=SAMPLES)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    payload = build(args.samples)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
