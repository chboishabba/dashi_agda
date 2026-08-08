#!/usr/bin/env python3
"""Generate structural Monster-3B/extraspecial representation dashboards.

The figures visualize functions, orbit geometry, Fourier phases, quadratic
forms, and generator-to-invariant maps.  They deliberately avoid decorative
cardinality charts.  GAP-derived branching data are used when present;
otherwise the script omits that panel rather than inventing constituents.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

P = 3
N = 6
H = P**N
ZETA = np.exp(2j * np.pi / P)


def ternary_vectors() -> np.ndarray:
    values = np.arange(H, dtype=np.int64)
    return np.stack([(values // (P**j)) % P for j in range(N)], axis=1)


def symplectic_pair(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    """Standard alternating form on F_3^3 + F_3^3."""
    return (
        np.sum(x[..., :3] * y[..., 3:], axis=-1)
        - np.sum(x[..., 3:] * y[..., :3], axis=-1)
    ) % P


def quadratic_phase(vectors: np.ndarray, sign: int) -> np.ndarray:
    """Two quadratic refinements sharing the same alternating polarization."""
    q = np.sum(vectors[:, :3] * vectors[:, 3:], axis=1) % P
    if sign < 0:
        q = (q + vectors[:, 0] ** 2 + vectors[:, 3] ** 2) % P
    return q


def save_matrix(data: np.ndarray, title: str, subtitle: str, path: Path,
                xlabel: str, ylabel: str, *, vmin=None, vmax=None) -> None:
    fig, ax = plt.subplots(figsize=(13, 9))
    image = ax.imshow(data, aspect="auto", interpolation="nearest", vmin=vmin, vmax=vmax)
    ax.set_title(title, pad=12)
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)
    ax.text(0.5, -0.085, subtitle, transform=ax.transAxes, ha="center", va="top")
    fig.colorbar(image, ax=ax, fraction=0.027, pad=0.02)
    fig.subplots_adjust(left=0.08, right=0.93, top=0.91, bottom=0.14)
    fig.savefig(path, dpi=220, bbox_inches="tight")
    plt.close(fig)


def extraspecial_plus_minus_sheet(output: Path) -> None:
    """Compare + and - quadratic refinements through their phase kernels."""
    vectors = ternary_vectors()
    q_plus = quadratic_phase(vectors, +1)
    q_minus = quadratic_phase(vectors, -1)

    # Pairwise phase kernels K_q(x,y)=Re(zeta^(q(x+y)-q(x)-q(y))).
    # Use every ninth vector on each axis for a readable 81x81 exact subgrid.
    selected = vectors[::9]
    panels = []
    for sign in (+1, -1):
        q = quadratic_phase(selected, sign)
        sums = (selected[:, None, :] + selected[None, :, :]) % P
        flat = sums.reshape(-1, N)
        qsum = quadratic_phase(flat, sign).reshape(len(selected), len(selected))
        polarization = (qsum - q[:, None] - q[None, :]) % P
        panels.append(np.real(ZETA**polarization))

    combined = np.concatenate(panels, axis=1)
    save_matrix(
        combined,
        "Extraspecial 3-group quadratic-refinement comparison",
        "Left and right use two quadratic refinements; entries are real phase kernels from their polarizations.",
        output / "extraspecial_plus_minus_phase_sheet.png",
        "sampled state y: plus-type panel | minus-type panel",
        "sampled state x",
        vmin=-0.5,
        vmax=1.0,
    )


def generator_invariant_dashboard(output: Path) -> None:
    vectors = ternary_vectors()
    generators = np.eye(N, dtype=int)
    generator_names = [f"e{j}" for j in range(N)]

    # Rows are states; columns are actual invariants attached to generator actions.
    fields = []
    names = []
    for name, gen in zip(generator_names, generators):
        comm = symplectic_pair(vectors, gen)
        fields.extend([
            comm,
            np.real(ZETA**comm),
            quadratic_phase((vectors + gen) % P, +1) - quadratic_phase(vectors, +1),
        ])
        names.extend([f"<{name},x>", f"Re chi_{name}", f"Delta q+_{name}"])

    matrix = np.stack(fields, axis=1)
    fig, ax = plt.subplots(figsize=(16, 10))
    image = ax.imshow(matrix, aspect="auto", interpolation="nearest")
    ax.set_title("Generator-to-invariant map on the full F3^6 carrier")
    ax.set_xlabel("generator-derived invariant")
    ax.set_ylabel("state x = 0,...,728")
    ax.set_xticks(np.arange(len(names)))
    ax.set_xticklabels(names, rotation=70, ha="right", fontsize=8)
    fig.colorbar(image, ax=ax, fraction=0.02, pad=0.015)
    fig.subplots_adjust(left=0.06, right=0.95, top=0.92, bottom=0.25)
    fig.savefig(output / "generator_to_invariant_dashboard.png", dpi=220, bbox_inches="tight")
    plt.close(fig)


def heisenberg_weyl_phase_portrait(output: Path) -> None:
    vectors = ternary_vectors()
    # Every state x and every modulation label b: phase zeta^{<b,x>}.
    phase = np.empty((H, H), dtype=float)
    for j, b in enumerate(vectors):
        phase[:, j] = np.angle(ZETA ** symplectic_pair(vectors, b))
    save_matrix(
        phase,
        "Full finite-Heisenberg/Weyl phase portrait",
        "All 729 states against all 729 modulation labels; value is arg(zeta^{<b,x>}).",
        output / "heisenberg_weyl_phase_portrait.png",
        "modulation label b in F3^6",
        "basis state x in F3^6",
        vmin=-np.pi,
        vmax=np.pi,
    )


def suzuki_12_plus_78_sheet(output: Path) -> None:
    vectors = ternary_vectors()
    multiplicity = np.arange(90)
    block = np.where(multiplicity < 12, 0, 1)
    q = quadratic_phase(vectors, +1)

    # Distinct but explicit invariant probes for the 12 and 78 columns.
    s0 = multiplicity % 3
    s1 = (multiplicity // 3) % 3
    s2 = (multiplicity // 9) % 3
    phase = (
        q[:, None]
        + vectors[:, 0, None] * s0[None, :]
        + vectors[:, 1, None] * s1[None, :]
        + block[None, :] * vectors[:, 2, None] * s2[None, :]
    ) % 3
    observable = np.real(ZETA**phase)

    fig, ax = plt.subplots(figsize=(14, 9))
    image = ax.imshow(observable, aspect="auto", interpolation="nearest", vmin=-0.5, vmax=1)
    ax.axvline(11.5, linewidth=1.5)
    ax.set_title("Heisenberg carrier coupled to the 12 + 78 multiplicity decomposition")
    ax.set_xlabel("multiplicity coordinate: 12-dimensional block | 78-dimensional block")
    ax.set_ylabel("Heisenberg state x in F3^6")
    fig.colorbar(image, ax=ax, fraction=0.027, pad=0.02)
    fig.tight_layout()
    fig.savefig(output / "heisenberg_times_12_plus_78.png", dpi=220, bbox_inches="tight")
    plt.close(fig)


def orbit_invariant_sheet(output: Path) -> None:
    vectors = ternary_vectors()
    index = {tuple(v): i for i, v in enumerate(vectors)}

    # A concrete symplectic-like affine action used as an executable model.
    def transform(v: np.ndarray) -> np.ndarray:
        return np.array([
            v[1], v[2], v[0] + v[3], v[4], v[5], -v[3]
        ], dtype=int) % P

    orbit_length = np.zeros(H, dtype=int)
    visited = np.zeros(H, dtype=bool)
    for start in range(H):
        if visited[start]:
            continue
        orbit = []
        current = start
        while not visited[current]:
            visited[current] = True
            orbit.append(current)
            current = index[tuple(transform(vectors[current]))]
        for item in orbit:
            orbit_length[item] = len(orbit)

    # Re-index F3^6 as F3^3 x F3^3 for a meaningful 27x27 sheet.
    sheet = orbit_length.reshape(27, 27)
    save_matrix(
        sheet,
        "Orbit-length invariant on F3^3 x F3^3",
        "Each cell is a state; values are orbit lengths under one explicit affine symplectic-model generator.",
        output / "orbit_length_sheet.png",
        "second Lagrangian coordinate",
        "first Lagrangian coordinate",
    )


def branching_sheet(input_json: Path, output: Path) -> None:
    if not input_json.exists():
        return
    payload = json.loads(input_json.read_text())
    constituents = payload.get("constituents", [])
    if not constituents:
        return

    # One cell per contributed dimension, packed by constituent and coloured by
    # irreducible-table position.  This is a decomposition function, not a bar chart.
    total = payload["reconstructed_degree"]
    width = 512
    height = (total + width - 1) // width
    sheet = np.full(width * height, np.nan)
    offset = 0
    for row in constituents:
        contribution = int(row["contribution"])
        sheet[offset:offset + contribution] = int(row["position"])
        offset += contribution
    sheet = sheet.reshape(height, width)
    save_matrix(
        sheet,
        "Actual CTblLib restriction of chi_196883 to MN3B",
        "Each cell is one dimension; colour is the MN3B irreducible-character position owning that contribution.",
        output / "mn3b_actual_restriction_sheet.png",
        "packed dimension coordinate",
        "packed dimension coordinate",
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--restriction-json", type=Path,
                        default=Path("build/monster_3b_normalizer_restriction.json"))
    parser.add_argument("--output", type=Path,
                        default=Path("build/monster_3b_dashboard"))
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    extraspecial_plus_minus_sheet(args.output)
    generator_invariant_dashboard(args.output)
    heisenberg_weyl_phase_portrait(args.output)
    suzuki_12_plus_78_sheet(args.output)
    orbit_invariant_sheet(args.output)
    branching_sheet(args.restriction_json, args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
