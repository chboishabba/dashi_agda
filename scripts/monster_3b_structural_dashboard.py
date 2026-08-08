#!/usr/bin/env python3
"""Generate function-first Monster-3B/extraspecial representation dashboards.

Every figure is an evaluation of a mathematical function or invariant on a
specified finite carrier.  No magnitude-only bar charts are emitted.

The GAP-derived restriction panel is generated only when a checked CTblLib
certificate exists.  The Heisenberg and elementary-abelian panels are exact
finite-field computations.  The 12+78 panel remains explicitly model-level
until genuine MN3B matrices are imported.
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
SYMPLECTIC = np.zeros((N, N), dtype=np.int64)
SYMPLECTIC[:3, 3:] = np.eye(3, dtype=np.int64)
SYMPLECTIC[3:, :3] = -np.eye(3, dtype=np.int64)
SYMPLECTIC %= P


def symplectic_pair(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    """Standard alternating form on F_3^3 + F_3^3."""
    return np.einsum("...i,ij,...j->...", x, SYMPLECTIC, y) % P


def quadratic_phase(vectors: np.ndarray, variant: int) -> np.ndarray:
    """Two declared quadratic probes on F_3^6, used only as finite functions."""
    q = np.sum(vectors[..., :3] * vectors[..., 3:], axis=-1) % P
    if variant < 0:
        q = (q + vectors[..., 0] ** 2 + vectors[..., 3] ** 2) % P
    return q


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
        ax.set_xticklabels(xticklabels, rotation=55, ha="right")
    ax.text(
        0.5,
        -0.105,
        subtitle,
        transform=ax.transAxes,
        ha="center",
        va="top",
        wrap=True,
    )
    fig.colorbar(image, ax=ax, fraction=0.027, pad=0.02)
    fig.subplots_adjust(left=0.08, right=0.93, top=0.91, bottom=0.19)
    fig.savefig(path, dpi=220, bbox_inches="tight")
    plt.close(fig)


def extraspecial_plus_minus_sheet(output: Path) -> None:
    """Compare + and - types through the complete character-degree moment."""
    moments = np.linspace(0.0, 6.0, 721)
    rows = []
    labels = []
    for kind in ("+", "-"):
        for n in range(1, 7):
            # Both extraspecial types of order 3^(1+2n) have:
            #   3^(2n) linear characters and two nonlinear characters of degree 3^n.
            # M_n(s)=sum_chi chi(1)^s is therefore exact for real s.
            linear_term = 3.0 ** (2 * n)
            nonlinear_term = 2.0 * 3.0 ** (n * moments)
            rows.append(np.log10(linear_term + nonlinear_term))
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
        "The + and − rows coincide exactly: type changes central-product/exponent geometry, not the irreducible degree multiset.",
        transform=ax.transAxes,
        ha="center",
        va="top",
    )
    fig.colorbar(image, ax=ax, fraction=0.027, pad=0.02, label="log10 M_n(s)")
    fig.subplots_adjust(left=0.12, right=0.93, top=0.91, bottom=0.17)
    fig.savefig(output / "extraspecial_plus_minus_phase_sheet.png", dpi=220, bbox_inches="tight")
    plt.close(fig)


def rref_two_planes() -> list[np.ndarray]:
    """Enumerate every 2-plane in F_3^6 exactly once by its RREF basis."""
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


def generator_invariant_dashboard(output: Path) -> None:
    """Map all elementary-abelian 2-planes to restriction invariants."""
    rows = []
    for basis in rref_two_planes():
        pairing = int(symplectic_pair(basis[0], basis[1]))
        restriction_rank = 0 if pairing == 0 else 2
        states = np.array(
            [
                (a * basis[0] + b * basis[1]) % P
                for a in range(P)
                for b in range(P)
            ]
        )
        q_plus_zero = int(np.count_nonzero(quadratic_phase(states, +1) == 0))
        q_minus_zero = int(np.count_nonzero(quadratic_phase(states, -1) == 0))
        support = np.flatnonzero(np.any(basis != 0, axis=0))
        first_support = int(support[0])
        last_support = int(support[-1])
        generator_weight = int(np.count_nonzero(basis))
        # kappa1-proxy here means only the commutator-rank input that a genuine
        # Chern restriction calculation would consume; no cohomology class is claimed.
        kappa1_input = restriction_rank // 2
        rows.append(
            (
                restriction_rank,
                q_plus_zero,
                q_minus_zero,
                first_support,
                last_support,
                generator_weight,
                kappa1_input,
            )
        )

    # Sorting makes invariant strata visible without changing any values.
    rows.sort()
    matrix = np.array(rows, dtype=float)
    names = [
        "commutator rank",
        "Q+ zero count",
        "Q− zero count",
        "first support",
        "last support",
        "RREF weight",
        "kappa1 input",
    ]
    save_matrix(
        matrix,
        "Generator-to-invariant map for every elementary-abelian 2-plane in F3^6",
        "All 11,011 RREF-indexed 2-planes are sorted by their invariant tuple. kappa1 input is a commutator-rank proxy, not a claimed Chern class.",
        output / "generator_to_invariant_dashboard.png",
        "restriction invariant",
        "elementary-abelian 2-plane stratum",
        xticks=list(range(len(names))),
        xticklabels=names,
    )

    counts: dict[str, int] = {}
    rank_values = matrix[:, 0].astype(int)
    counts["two_plane_count"] = int(len(matrix))
    counts["isotropic_two_plane_count"] = int(np.count_nonzero(rank_values == 0))
    counts["symplectic_two_plane_count"] = int(np.count_nonzero(rank_values == 2))
    (output / "elementary_abelian_two_plane_certificate.json").write_text(
        json.dumps(counts, indent=2, sort_keys=True) + "\n"
    )


def heisenberg_weyl_phase_portrait(output: Path) -> None:
    """Evaluate every finite-Heisenberg character phase zeta^<b,x>."""
    pairings = np.einsum(
        "xi,ij,yj->xy", VECTORS, SYMPLECTIC, VECTORS
    ) % P
    phase = np.angle(ZETA**pairings)
    save_matrix(
        phase,
        "Complete finite-Heisenberg/Weyl phase portrait",
        "Every one of the 729 basis states x is evaluated against every modulation label b by arg(zeta^<x,b>).",
        output / "heisenberg_weyl_phase_portrait.png",
        "modulation label b in F3^6",
        "basis state x in F3^6",
        vmin=-np.pi,
        vmax=np.pi,
    )


def suzuki_12_plus_78_sheet(output: Path) -> None:
    """Display an explicit model coupling on H_729 tensor (12 direct-sum 78)."""
    multiplicity = np.arange(90)
    block = np.where(multiplicity < 12, 0, 1)
    q = quadratic_phase(VECTORS, +1)
    s0 = multiplicity % 3
    s1 = (multiplicity // 3) % 3
    s2 = (multiplicity // 9) % 3
    phase = (
        q[:, None]
        + VECTORS[:, 0, None] * s0[None, :]
        + VECTORS[:, 1, None] * s1[None, :]
        + block[None, :] * VECTORS[:, 2, None] * s2[None, :]
    ) % 3
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
    ax.set_title("Explicit Weyl-function model on H729 tensor (S12 direct-sum S78)")
    ax.set_xlabel("multiplicity coordinate: 12-dimensional block | 78-dimensional block")
    ax.set_ylabel("Heisenberg state x in F3^6")
    ax.text(
        0.5,
        -0.09,
        "The 729x90 carrier and 12|78 boundary are sourced dimensions; the displayed coupling remains a model until genuine MN3B matrices are imported.",
        transform=ax.transAxes,
        ha="center",
        va="top",
    )
    fig.colorbar(image, ax=ax, fraction=0.027, pad=0.02)
    fig.subplots_adjust(left=0.08, right=0.93, top=0.91, bottom=0.15)
    fig.savefig(output / "heisenberg_times_12_plus_78.png", dpi=220, bbox_inches="tight")
    plt.close(fig)


def orbit_invariant_sheet(output: Path) -> None:
    """Compute orbit lengths under an explicit invertible finite-field map."""
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

    sheet = orbit_length.reshape(27, 27)
    save_matrix(
        sheet,
        "Orbit-length invariant on F3^3 x F3^3",
        "Each cell is one Heisenberg state; the value is its exact orbit length under the declared invertible finite-field generator.",
        output / "orbit_length_sheet.png",
        "second Lagrangian coordinate",
        "first Lagrangian coordinate",
    )


def branching_sheet(input_json: Path, output: Path) -> None:
    """Render the certified restriction as a constituent-label function."""
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
    sheet = sheet.reshape(height, width)
    save_matrix(
        sheet,
        "Certified CTblLib restriction label function chi_196883 restricted to MN3B",
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
