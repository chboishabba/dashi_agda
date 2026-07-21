#!/usr/bin/env python3
"""Finite full near-triad factor scan on the periodic Galerkin carrier."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import numpy as np

from ns_periodic_galerkin_core import (
    fmt,
    make_geometry,
    random_state,
    weighted_five_halves,
)

SCHEMA = "ns_near_triad_full_factor_scan.v1"


def digest(payload: Any) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def dominant_shells(g) -> np.ndarray:
    ids = sorted(g.shell_weights)
    matrix = np.asarray([g.shell_weights[j] for j in ids])
    return np.asarray([ids[i] for i in np.argmax(matrix, axis=0)], dtype=np.int64)


def component_values(g, u: np.ndarray, h: np.ndarray, K: int) -> dict[str, float]:
    shells = dominant_shells(g)
    target = g.shell_weights[K] ** 2
    totals = {"LH": 0.0 + 0.0j, "HL": 0.0 + 0.0j, "HH": 0.0 + 0.0j}

    for ki in range(len(g.modes)):
        if target[ki] == 0.0:
            continue
        ps = g.triad_p[ki]
        if ps.size == 0:
            continue
        qs = g.triad_q[ki]
        qvec = g.triad_qvec[ki]

        first_coeff = np.einsum("ij,ij->i", u[ps], qvec)
        second_coeff = np.einsum("ij,ij->i", h[ps], qvec)
        first_vectors = first_coeff[:, None] * h[qs]
        second_vectors = second_coeff[:, None] * u[qs]

        for row, pi, qi in zip(first_vectors, ps, qs):
            label = "LH" if shells[pi] < K and shells[qi] >= K else "HH"
            projected = g.projectors[ki] @ row
            totals[label] += target[ki] * np.vdot(h[ki], -1j * projected)
        for row, pi, qi in zip(second_vectors, ps, qs):
            label = "HL" if shells[qi] < K and shells[pi] >= K else "HH"
            projected = g.projectors[ki] @ row
            totals[label] += target[ki] * np.vdot(h[ki], -1j * projected)

    mode_h2 = np.sum(np.abs(h) ** 2, axis=1)
    energy = float(np.sum(target * mode_h2))
    dissipation = float(np.sum(target * g.ksq * mode_h2))
    u_norm = weighted_five_halves(g, u)
    denominator = u_norm * np.sqrt(max(energy, 0.0)) * np.sqrt(max(dissipation, 0.0))
    return {
        label: abs(float(np.real(value))) / denominator if denominator > 0 else 0.0
        for label, value in totals.items()
    }


def build(samples: int = 8) -> dict[str, Any]:
    rows = []
    global_max = {"LH": 0.0, "HL": 0.0, "HH": 0.0}
    witnesses: dict[str, Any] = {}
    for cutoff in (2, 3):
        g = make_geometry(cutoff, max_shell=2)
        K = 1
        cutoff_max = {"LH": 0.0, "HL": 0.0, "HH": 0.0}
        for n in range(samples):
            u_seed = 11003 + 211 * n + cutoff
            h_seed = 22003 + 223 * n + cutoff
            u = random_state(g, u_seed, energy=1.0)
            h = random_state(g, h_seed, energy=1.0)
            ratios = component_values(g, u, h, K)
            for label, value in ratios.items():
                cutoff_max[label] = max(cutoff_max[label], value)
                if value > global_max[label]:
                    global_max[label] = value
                    witnesses[label] = {
                        "cutoff": cutoff,
                        "u_seed": u_seed,
                        "h_seed": h_seed,
                        "ratio": fmt(value),
                    }
        rows.append(
            {
                "cutoff": cutoff,
                "target_shell": K,
                "samples": samples,
                "max_ratios": {label: fmt(value) for label, value in cutoff_max.items()},
            }
        )

    candidate_constants = {label: int(np.ceil(value)) for label, value in global_max.items()}
    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "authority": "finite_full_linearized_velocity_triad_factor_scan_only",
        "factor_norm": "weighted-five-halves(u)*sqrt(target-dissipation(h))*sqrt(target-energy(h))",
        "placement_rule": "LH if background p below K; HL if background q below K; all remaining terms HH",
        "rows": rows,
        "global_max_ratios": {label: fmt(value) for label, value in global_max.items()},
        "integer_candidate_constants": candidate_constants,
        "witnesses": witnesses,
        "promotion": {
            "finite_scan_is_product_theorem": False,
            "candidate_constants_cutoff_uniform": False,
            "universal_near_absorption": False,
        },
    }
    payload["sha256"] = digest(payload)
    return payload


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-json", type=Path, required=True)
    ap.add_argument("--samples", type=int, default=8)
    ap.add_argument("--pretty", action="store_true")
    args = ap.parse_args()
    payload = build(args.samples)
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, sort_keys=True, indent=2 if args.pretty else None) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
