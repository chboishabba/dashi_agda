#!/usr/bin/env python3
"""Finite constrained Galerkin search on all four compact-Gamma faces."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Callable

import numpy as np

from ns_periodic_galerkin_core import (
    enforce_reality,
    fmt,
    h1_squared,
    h1_squared_derivative,
    make_geometry,
    packet_metrics,
    project_state,
    random_state,
    rhs,
)

SCHEMA = "ns_boundary_face_galerkin_search.v1"


def digest(payload: Any) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def rescale_mask(g, u: np.ndarray, mask: np.ndarray, factor: float) -> np.ndarray:
    out = np.array(u, copy=True)
    out[mask] *= factor
    return enforce_reality(g, project_state(g, out))


def bisect_factor(
    g,
    u: np.ndarray,
    mask: np.ndarray,
    observable: Callable[[np.ndarray], float],
    target: float,
    increasing: bool = True,
) -> np.ndarray:
    lo, hi = 1.0e-4, 1.0e4
    for _ in range(80):
        mid = np.sqrt(lo * hi)
        value = observable(rescale_mask(g, u, mask, mid))
        if (value < target) == increasing:
            lo = mid
        else:
            hi = mid
    return rescale_mask(g, u, mask, np.sqrt(lo * hi))


def face_state(g, seed: int, face: str) -> np.ndarray:
    u = random_state(g, seed, energy=1.0)
    K = 0
    all_mask = np.ones(len(g.modes), dtype=bool)
    center_mask = g.shell_weights[0] > 0.999999
    outside_mask = g.shell_weights[2] > 1.0e-12

    if face == "gamma_floor":
        return bisect_factor(
            g,
            u,
            center_mask,
            lambda x: packet_metrics(g, x, K)["gamma"],
            0.5,
            increasing=True,
        )
    if face == "packet_energy_floor":
        packet = packet_metrics(g, u, K)["packet"]
        return rescale_mask(g, u, all_mask, np.sqrt(0.5 / packet))
    if face == "off_packet_ceiling":
        return bisect_factor(
            g,
            u,
            outside_mask,
            lambda x: packet_metrics(g, x, K)["off"],
            0.25,
            increasing=True,
        )
    if face == "size_ceiling":
        return rescale_mask(g, u, all_mask, np.sqrt(10.0 / h1_squared(g, u)))
    raise ValueError(face)


def inward_derivative(g, u: np.ndarray, face: str) -> tuple[float, dict[str, float]]:
    K = 0
    du = rhs(g, u, viscosity=1.0)
    metrics = packet_metrics(g, u, K, du)
    if face == "gamma_floor":
        value = metrics["gamma_derivative"]
    elif face == "packet_energy_floor":
        value = metrics["packet_derivative"]
    elif face == "off_packet_ceiling":
        value = -metrics["off_derivative"]
    elif face == "size_ceiling":
        value = -h1_squared_derivative(g, u, du)
    else:
        raise ValueError(face)
    return value, metrics


def build(samples: int = 16) -> dict[str, Any]:
    g = make_geometry(3, max_shell=2)
    faces: dict[str, Any] = {}
    for face in ("gamma_floor", "packet_energy_floor", "off_packet_ceiling", "size_ceiling"):
        values: list[float] = []
        witnesses: list[dict[str, Any]] = []
        for n in range(samples):
            seed = 7001 + 97 * n
            u = face_state(g, seed, face)
            inward, metrics = inward_derivative(g, u, face)
            values.append(inward)
            witnesses.append(
                {
                    "seed": seed,
                    "inward_derivative": fmt(inward),
                    "gamma": fmt(metrics["gamma"]),
                    "packet": fmt(metrics["packet"]),
                    "off": fmt(metrics["off"]),
                    "total": fmt(metrics["total"]),
                    "h1_squared": fmt(h1_squared(g, u)),
                }
            )
        worst_index = min(range(samples), key=lambda i: values[i])
        faces[face] = {
            "sample_count": samples,
            "minimum_inward_derivative": fmt(values[worst_index]),
            "maximum_inward_derivative": fmt(max(values)),
            "nonpositive_count": sum(v <= 0.0 for v in values),
            "strict_inward_on_sample": all(v > 0.0 for v in values),
            "worst_witness": witnesses[worst_index],
        }

    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "authority": "finite_deterministic_constrained_Galerkin_face_search_only",
        "cutoff": 3,
        "target_shell": 0,
        "targets": {
            "gamma_floor": fmt(0.5),
            "packet_energy_floor": fmt(0.5),
            "off_packet_ceiling": fmt(0.25),
            "size_squared_ceiling": fmt(10.0),
        },
        "faces": faces,
        "all_four_strict_on_sample": all(face["strict_inward_on_sample"] for face in faces.values()),
        "promotion": {
            "finite_search_is_proof": False,
            "strict_Dini_inwardness": False,
            "global_invariant_region": False,
        },
    }
    payload["sha256"] = digest(payload)
    return payload


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-json", type=Path, required=True)
    ap.add_argument("--samples", type=int, default=16)
    ap.add_argument("--pretty", action="store_true")
    args = ap.parse_args()
    payload = build(args.samples)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
