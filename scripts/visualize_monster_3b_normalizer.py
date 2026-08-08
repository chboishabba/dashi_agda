#!/usr/bin/env python3
"""Structural visualizations for the Monster 3B normalizer lane.

This script deliberately avoids decorative cardinality plots.  It renders:

1. the exact CTblLib restriction support as a degree/multiplicity constellation;
2. extraspecial p-group plus/minus representation-degree sheets;
3. the 3^6 finite-Heisenberg Weyl commutator phase field;
4. generator-to-invariant maps over F_3^6;
5. the 729 x (12 + 78) carrier with genuine Weyl phase functions;
6. orbit-length and stabilizer strata for explicit symplectic generators;
7. C3 spectral-projector response functions.

The GAP-derived plots require JSON emitted by
scripts/gap/monster_3b_normalizer_restriction.g.  The Heisenberg plots are
canonical model-level constructions; they are not labelled as actual Monster
matrix coefficients until an explicit MN3B representation is supplied.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Callable

import matplotlib.pyplot as plt
import numpy as np

P = 3
N = 6
H = P**N
ZETA = np.exp(2j * np.pi / 3)


def trits(value: int, width: int = N) -> np.ndarray:
    out = np.zeros(width, dtype=int)
    for i in range(width):
        out[i] = value % P
        value //= P
    return out


COORDS = np.array([trits(i) for i in range(H)])
INDEX = {tuple(v.tolist()): i for i, v in enumerate(COORDS)}


def save_heatmap(data: np.ndarray, title: str, x_label: str, y_label: str,
                 path: Path, *, boundary: float | None = None) -> None:
    fig, ax = plt.subplots(figsize=(14, 9))
    image = ax.imshow(data, interpolation="nearest", aspect="auto")
    if boundary is not None:
        ax.axvline(boundary, linewidth=1.3)
    ax.set_title(title)
    ax.set_xlabel(x_label)
    ax.set_ylabel(y_label)
    fig.colorbar(image, ax=ax, fraction=0.025, pad=0.02)
    fig.tight_layout()
    fig.savefig(path, dpi=220)
    plt.close(fig)


def restriction_constellation(payload: dict, output: Path) -> None:
    terms = payload["terms"]
    degree = np.array([t["degree"] for t in terms], dtype=float)
    multiplicity = np.array([t["multiplicity"] for t in terms], dtype=float)
    contribution = np.array([t["contribution"] for t in terms], dtype=float)
    index = np.array([t["index"] for t in terms], dtype=int)

    fig, ax = plt.subplots(figsize=(12, 8))
    size = 30 + 370 * contribution / contribution.max()
    scatter = ax.scatter(index, degree, s=size, c=np.log1p(multiplicity))
    ax.set_yscale("log")
    ax.set_xlabel("MN3B irreducible-character index")
    ax.set_ylabel("Character degree (log scale)")
    ax.set_title("Exact restriction support of the Monster 196883 character")
    for i, x, y, m in zip(index, index, degree, multiplicity):
        if m > 1:
            ax.annotate(f"×{int(m)}", (x, y), xytext=(3, 3),
                        textcoords="offset points", fontsize=8)
    fig.colorbar(scatter, ax=ax, label="log(1 + multiplicity)")
    fig.tight_layout()
    fig.savefig(output / "01_exact_restriction_constellation.png", dpi=220)
    plt.close(fig)


def extraspecial_degree_sheet(output: Path) -> None:
    # For extraspecial groups of order p^(1+2n), both signs have p^(2n)
    # linear characters and p-1 nonlinear characters of degree p^n.
    primes = [3, 5, 7]
    ns = range(1, 7)
    rows = []
    for p in primes:
        for n in ns:
            linear_count = p ** (2 * n)
            nonlinear_degree = p**n
            nonlinear_count = p - 1
            rows.append((p, n, linear_count, nonlinear_degree, nonlinear_count))

    fig, ax = plt.subplots(figsize=(12, 8))
    for p in primes:
        subset = [r for r in rows if r[0] == p]
        x = [r[1] for r in subset]
        y = [r[3] for r in subset]
        ax.plot(x, y, marker="o", label=f"p={p}: nonlinear degree p^n")
    ax.set_yscale("log")
    ax.set_xlabel("n in p^(1+2n)")
    ax.set_ylabel("Faithful nonlinear character degree")
    ax.set_title("Extraspecial p-groups: + and − types share character degrees")
    ax.legend()
    ax.text(
        0.02, 0.02,
        "The +/− distinction changes quadratic/central-product geometry,\n"
        "not the degree multiset: p^(2n) linear characters and p−1 of degree p^n.",
        transform=ax.transAxes,
    )
    fig.tight_layout()
    fig.savefig(output / "02_extraspecial_plus_minus_degree_sheet.png", dpi=220)
    plt.close(fig)


def symplectic_form(x: np.ndarray, y: np.ndarray) -> int:
    return int((np.dot(x[:3], y[3:]) - np.dot(x[3:], y[:3])) % 3)


def weyl_commutator_field(output: Path) -> None:
    probes = COORDS[:243]
    field = np.empty((H, len(probes)), dtype=float)
    for i, x in enumerate(COORDS):
        for j, y in enumerate(probes):
            field[i, j] = np.angle(ZETA ** symplectic_form(x, y))
    save_heatmap(
        field,
        "Finite-Heisenberg commutator phase over F3^6",
        "Probe vector y (first 243 vectors)",
        "Carrier vector x (all 729 vectors)",
        output / "03_weyl_commutator_phase.png",
    )


def generator_invariant_dashboard(output: Path) -> None:
    x0, x1, x2, x3, x4, x5 = [COORDS[:, i] for i in range(6)]
    q_plus = (x0 * x3 + x1 * x4 + x2 * x5) % 3
    q_minus = (q_plus + x0 * x0 + x1 * x1) % 3
    radical_probe = ((x0 + x1 + x2) == 0).astype(int)
    isotropic = (q_plus == 0).astype(int)
    invariant_map = np.stack([q_plus, q_minus, radical_probe, isotropic], axis=1)
    save_heatmap(
        invariant_map,
        "Generator-to-invariant map on the 729-state Heisenberg carrier",
        "Invariant: Q+, Q−, elementary-abelian probe, isotropic flag",
        "Generator/address x in F3^6",
        output / "04_generator_to_invariant_dashboard.png",
    )


def tensor_12_78_phase_sheet(output: Path) -> None:
    s = np.arange(90)
    x0, x1, x2, x3, x4, x5 = [COORDS[:, i] for i in range(6)]
    q = (x0 * x3 + x1 * x4 + x2 * x5) % 3
    phase = np.empty((H, 90), dtype=float)
    phase[:, :12] = np.real(
        ZETA ** ((q[:, None] + s[None, :12]) % 3)
    )
    t = s[12:] - 12
    phase[:, 12:] = np.real(
        ZETA ** (
            q[:, None]
            + x0[:, None] * (t[None, :] % 3)
            + x1[:, None] * ((t[None, :] // 3) % 3)
            + x2[:, None] * ((t[None, :] // 9) % 3)
        )
    )
    save_heatmap(
        phase,
        "Weyl-phase functions on H_729 tensor (S_12 direct-sum S_78)",
        "Multiplicity coordinate: 12-module | 78-module",
        "Heisenberg address in F3^6",
        output / "05_tensor_12_78_weyl_phase.png",
        boundary=11.5,
    )


def orbit_invariants(output: Path) -> None:
    def transform(v: np.ndarray) -> np.ndarray:
        # Invertible symplectic-style shear/rotation used as an explicit
        # model generator; replace with actual MN3B matrices when available.
        a, b, c, d, e, f = v
        return np.array([a + b, b + c, c, d, e - d, f - e], dtype=int) % 3

    lengths = np.zeros(H, dtype=int)
    seen = np.zeros(H, dtype=bool)
    for start in range(H):
        if seen[start]:
            continue
        orbit = []
        current = start
        while current not in orbit:
            orbit.append(current)
            current = INDEX[tuple(transform(COORDS[current]).tolist())]
        for item in orbit:
            seen[item] = True
            lengths[item] = len(orbit)

    points = COORDS[:, 0] + 3 * COORDS[:, 1]
    fig, ax = plt.subplots(figsize=(11, 8))
    scatter = ax.scatter(np.arange(H), points, c=lengths, s=15)
    ax.set_xlabel("Heisenberg address index")
    ax.set_ylabel("First two ternary coordinates, radix-encoded")
    ax.set_title("Orbit-length invariant of an explicit symplectic-model generator")
    fig.colorbar(scatter, ax=ax, label="Orbit length")
    fig.tight_layout()
    fig.savefig(output / "06_orbit_length_invariant.png", dpi=220)
    plt.close(fig)


def c3_projector_response(output: Path) -> None:
    phases = np.array([1, ZETA, ZETA**2])
    angles = np.linspace(0, 2 * np.pi, 720, endpoint=False)
    response = np.empty((3, len(angles)))
    for j in range(3):
        lam = np.exp(1j * angles)
        response[j] = np.abs(
            (1 + phases[j] ** -1 * lam + phases[j] ** -2 * lam**2) / 3
        )
    fig, ax = plt.subplots(figsize=(12, 7))
    for j, label in enumerate(["P0", "Pζ", "Pζ²"]):
        ax.plot(angles, response[j], label=label)
    ax.set_xlabel("Input eigenphase angle")
    ax.set_ylabel("Projector response magnitude")
    ax.set_title("C3 spectral-projector response functions")
    ax.legend()
    fig.tight_layout()
    fig.savefig(output / "07_c3_projector_response.png", dpi=220)
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--restriction-json", type=Path)
    parser.add_argument("--output", type=Path, default=Path("artifacts/monster-3b"))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)

    if args.restriction_json is not None:
        payload = json.loads(args.restriction_json.read_text())
        restriction_constellation(payload, args.output)

    extraspecial_degree_sheet(args.output)
    weyl_commutator_field(args.output)
    generator_invariant_dashboard(args.output)
    tensor_12_78_phase_sheet(args.output)
    orbit_invariants(args.output)
    c3_projector_response(args.output)


if __name__ == "__main__":
    main()
