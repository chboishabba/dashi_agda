#!/usr/bin/env python3
"""Generate function-first Monster-3B/extraspecial dashboards.

The 729 Schrodinger basis states form X = F_3^6. Modulation labels belong to
X*, and the extraspecial quotient is X + X* = F_3^12. The Weyl phase uses the
perfect evaluation pairing <b,x>, not an artificial alternating form on X.

Every figure evaluates a mathematical function or invariant. The GAP-derived
panel is emitted only from a checked CTblLib certificate. The 12+78 coupling
remains explicitly model-level until actual MN3B matrices are imported.
"""

from __future__ import annotations

import argparse
import itertools
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


VECTORS = ternary_vectors()


def perfect_pair(x: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Evaluation X x X* -> F_3 under the standard coordinate duality."""
    return np.sum(x * b, axis=-1) % P


def coordinate_quadratic(vectors: np.ndarray) -> np.ndarray:
    """A declared coordinate probe, not the symplectic form on E/Z(E)."""
    return np.sum(vectors[..., :3] * vectors[..., 3:], axis=-1) % P


def save_matrix(
    data: np.ndarray,
    title: str,
    subtitle: str,
    path: Path,
    xlabel: str,
    ylabel: str,
    *,
    vmin=None,
    vmax=None,
    xticks: list[int] | None = None,
    xticklabels: list[str] | None = None,
) -> None:
    fig, ax = plt.subplots(figsize=(14, 9))
    image = ax.imshow(
        data,
        aspect="auto",
        interpolation="nearest",
        vmin=vmin,
        vmax=vmax,
    )
    ax.set_title(title, pad=12)
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)
    if xticks is not None:
        ax.set_xticks(xticks)
    if xticklabels is not None:
        ax.set_xticklabels(xticklabels, rotation=60, ha="right", fontsize=8)
    ax.text(
        0.5,
        -0.12,
        subtitle,
        transform=ax.transAxes,
        ha="center",
        va="top",
        wrap=True,
    )
    fig.colorbar(image, ax=ax, fraction=0.027, pad=0.02)
    fig.subplots_adjust(left=0.08, right=0.93, top=0.91, bottom=0.22)
    fig.savefig(path, dpi=220, bbox_inches="tight")
    plt.close(fig)


def extraspecial_plus_minus_sheet(output: Path) -> None:
    moments = np.linspace(0.0, 6.0, 721)
    rows = []
    labels = []
    for kind in ("+", "-"):
        for n in range(1, 7):
            degree_moment = 3.0 ** (2 * n) + 2.0 * 3.0 ** (n * moments)
            rows.append(np.log10(degree_moment))
            labels.append(f"{kind}, n={n}")
    matrix = np.stack(rows)
    fig, ax = plt.subplots(figsize=(15, 8))
    image = ax.imshow(
        matrix,
        aspect="auto",
        interpolation="nearest",
        extent=[moments[0], moments[-1], len(rows) - 0.5, -0.5],
    )
    ax.set_yticks(np.arange(len(labels)))
    ax.set_yticklabels(labels)
    ax.axhline(5.5, linewidth=1.2)
    ax.set_title("Extraspecial 3-group character-degree moment surface")
    ax.set_xlabel(r"moment s in M_n(s) = 3^(2n) + 2·3^(ns)")
    ax.set_ylabel("type and n for order 3^(1+2n)")
    ax.text(
        0.5,
        -0.1,
        "The + and - rows coincide exactly: type changes exponent and central-product geometry, not the irreducible degree multiset.",
        transform=ax.transAxes,
        ha="center",
        va="top",
    )
    fig.colorbar(image, ax=ax, fraction=0.027, pad=0.02, label="log10 M_n(s)")
    fig.subplots_adjust(left=0.12, right=0.93, top=0.91, bottom=0.17)
    fig.savefig(output / "extraspecial_plus_minus_phase_sheet.png", dpi=220, bbox_inches="tight")
    plt.close(fig)


def rref_two_planes() -> list[np.ndarray]:
    """Enumerate every two-plane in X=F_3^6 exactly once by RREF basis."""
    planes: list[np.ndarray] = []
    for first in range(N):
        for second in range(first + 1, N):
            free_first = [c for c in range(first + 1, N) if c != second]
            free_second = list(range(second + 1, N))
            for values in itertools.product(
                range(P), repeat=len(free_first) + len(free_second)
            ):
                basis = np.zeros((2, N), dtype=np.int64)
                basis[0, first] = 1
                basis[1, second] = 1
                cursor = 0
                for column in free_first:
                    basis[0, column] = values[cursor]
                    cursor += 1
                for column in free_second:
                    basis[1, column] = values[cursor]
                    cursor += 1
                planes.append(basis)
    if len(planes) != 11011:
        raise AssertionError("Gaussian binomial [6 choose 2]_3 must be 11011")
    return planes


def plucker_coordinates(basis: np.ndarray) -> tuple[int, ...]:
    values = []
    for i in range(N):
        for j in range(i + 1, N):
            minor = basis[0, i] * basis[1, j] - basis[0, j] * basis[1, i]
            values.append(int(minor % P))
    return tuple(values)


def nonzero_weight_histogram(basis: np.ndarray) -> tuple[int, ...]:
    states = [
        (a * basis[0] + b * basis[1]) % P
        for a in range(P)
        for b in range(P)
        if a != 0 or b != 0
    ]
    weights = [int(np.count_nonzero(state)) for state in states]
    return tuple(weights.count(weight) for weight in range(1, N + 1))


def generator_invariant_dashboard(output: Path) -> None:
    rows = []
    for basis in rref_two_planes():
        pivots = tuple(int(np.flatnonzero(row)[0]) for row in basis)
        plucker = plucker_coordinates(basis)
        weights = nonzero_weight_histogram(basis)
        support_size = int(np.count_nonzero(np.any(basis != 0, axis=0)))
        rows.append(plucker + weights + pivots + (support_size,))

    rows.sort()
    matrix = np.asarray(rows, dtype=float)
    plucker_names = [f"p{i}{j}" for i in range(N) for j in range(i + 1, N)]
    names = plucker_names + [f"weight={k}" for k in range(1, N + 1)] + [
        "pivot 1",
        "pivot 2",
        "support",
    ]
    save_matrix(
        matrix,
        "Plucker and restriction inputs for every two-plane in X=F3^6",
        "All 11,011 planes lie in one fixed Lagrangian and lift with the centre to rank-three elementary abelian subgroups. The Schrodinger restriction is 81 copies of Reg(F3^2); the varying fields are exact Grassmannian and coordinate invariants.",
        output / "generator_to_invariant_dashboard.png",
        "invariant coordinate",
        "RREF-indexed Lagrangian two-plane",
        xticks=list(range(len(names))),
        xticklabels=names,
    )

    certificate = {
        "fixed_lagrangian_two_plane_count": len(rows),
        "central_lift_order": 27,
        "central_lift_rank": 3,
        "translation_character_count": 9,
        "regular_character_multiplicity": 81,
        "represented_dimension": 729,
        "full_symplectic_two_plane_count": 5883904390,
        "full_isotropic_two_plane_count": 1961279320,
        "full_nonisotropic_two_plane_count": 3922625070,
    }
    (output / "elementary_abelian_two_plane_certificate.json").write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    )


def heisenberg_weyl_phase_portrait(output: Path) -> None:
    pairings = (VECTORS @ VECTORS.T) % P
    phase = np.angle(ZETA**pairings)
    save_matrix(
        phase,
        "Complete finite-Heisenberg/Weyl phase portrait",
        "All 729 states x in X are evaluated against all 729 modulation labels b in X* by arg(zeta^<b,x>).",
        output / "heisenberg_weyl_phase_portrait.png",
        "modulation label b in X*",
        "Schrodinger basis state x in X",
        vmin=-np.pi,
        vmax=np.pi,
    )


def suzuki_12_plus_78_sheet(output: Path) -> None:
    multiplicity = np.arange(90)
    block = np.where(multiplicity < 12, 0, 1)
    q = coordinate_quadratic(VECTORS)
    s0 = multiplicity % 3
    s1 = (multiplicity // 3) % 3
    s2 = (multiplicity // 9) % 3
    phase = (
        q[:, None]
        + VECTORS[:, 0, None] * s0[None, :]
        + VECTORS[:, 1, None] * s1[None, :]
        + block[None, :] * VECTORS[:, 2, None] * s2[None, :]
    ) % P
    observable = np.real(ZETA**phase)

    fig, ax = plt.subplots(figsize=(14, 9))
    image = ax.imshow(
        observable,
        aspect="auto",
        interpolation="nearest",
        vmin=-0.5,
        vmax=1.0,
    )
    ax.axvline(11.5, linewidth=1.5)
    ax.set_title("Explicit function model on H729 tensor (S12 direct-sum S78)")
    ax.set_xlabel("multiplicity coordinate: 12-dimensional block | 78-dimensional block")
    ax.set_ylabel("Schrodinger state x in X=F3^6")
    ax.text(
        0.5,
        -0.1,
        "The 729x90 carrier and 12|78 boundary are sourced dimensions; this displayed coordinate coupling is not labelled as a genuine MN3B matrix coefficient.",
        transform=ax.transAxes,
        ha="center",
        va="top",
    )
    fig.colorbar(image, ax=ax, fraction=0.027, pad=0.02)
    fig.subplots_adjust(left=0.08, right=0.93, top=0.91, bottom=0.17)
    fig.savefig(output / "heisenberg_times_12_plus_78.png", dpi=220, bbox_inches="tight")
    plt.close(fig)


def orbit_invariant_sheet(output: Path) -> None:
    index = {tuple(v): i for i, v in enumerate(VECTORS)}

    def transform(v: np.ndarray) -> np.ndarray:
        return np.array(
            [v[1], v[2], v[0] + v[3], v[4], v[5], -v[3]],
            dtype=np.int64,
        ) % P

    images = [index[tuple(transform(v))] for v in VECTORS]
    if len(set(images)) != H:
        raise AssertionError("orbit generator is not invertible")

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
            current = images[current]
        for item in orbit:
            orbit_length[item] = len(orbit)

    save_matrix(
        orbit_length.reshape(27, 27),
        "Orbit-length invariant on X = F3^3 x F3^3",
        "Each cell is one Schrodinger basis state; the value is its exact orbit length under the declared invertible finite-field generator.",
        output / "orbit_length_sheet.png",
        "second coordinate block",
        "first coordinate block",
    )


def branching_sheet(input_json: Path, output: Path) -> None:
    if not input_json.exists():
        return
    payload = json.loads(input_json.read_text())
    if payload.get("classwise_reconstruction") is not True:
        raise ValueError("restriction JSON lacks classwise reconstruction")
    constituents = payload.get("constituents", [])
    if not constituents:
        return

    total = int(payload["reconstructed_degree"])
    width = 512
    height = (total + width - 1) // width
    sheet = np.full(width * height, np.nan)
    offset = 0
    for row in constituents:
        contribution = int(row["contribution"])
        sheet[offset : offset + contribution] = int(row["position"])
        offset += contribution
    if offset != total:
        raise ValueError("constituent contributions do not fill the carrier")
    save_matrix(
        sheet.reshape(height, width),
        "Certified CTblLib restriction-label function chi_196883 restricted to MN3B",
        "Each domain point is one contributed dimension; the function value is the owning MN3B irreducible-table position.",
        output / "mn3b_actual_restriction_sheet.png",
        "packed dimension coordinate",
        "packed dimension coordinate",
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--restriction-json",
        type=Path,
        default=Path("build/monster_3b_normalizer_restriction.json"),
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("build/monster_3b_dashboard"),
    )
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
