#!/usr/bin/env python3
"""Gravity Vladimirov/Kozyrev frame diagnostic.

This is a non-promoting carrier-side gravity diagnostic.  It compares three
objects:

1. the exact p-adic Kozyrev basis, whose Gram matrix is the identity;
2. the Archimedean digit-image Haar/Kozyrev contrast modes, which retain an
   identity Gram on a finite p-ary grid;
3. naive radial shell indicators, which nest and therefore fail uniform frame
   control.

The script does not derive a physical mass source, Schwarzschild metric,
Newton's constant, PPN parameters, or higher-curvature coefficients.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import numpy as np


DEFAULT_OUTPUT_JSON = Path("scripts/data/outputs/gr_vladimirov_frame_diagnostic.json")
DEFAULT_OUTPUT_CSV = Path("scripts/data/outputs/gr_vladimirov_frame_diagnostic.csv")


@dataclass(frozen=True)
class FrameRow:
    model: str
    p: int
    max_level: int
    atom_count: int
    grid_size: int
    alpha: float
    frame_lower_A: float
    frame_upper_B: float
    max_offdiag_mu: float
    condition_number: float
    vladimirov_lambda_min: float
    vladimirov_lambda_max: float
    pawotg_sigma: float
    pawotg_series: float
    naive_parent_child_overlap: float
    promotion_status: str


def normalized(v: np.ndarray) -> np.ndarray:
    norm = float(np.linalg.norm(v))
    if norm == 0.0:
        raise ValueError("zero vector cannot be normalized")
    return v / norm


def gram_stats(atoms: np.ndarray) -> tuple[float, float, float, float]:
    gram = atoms @ atoms.T
    eigvals = np.linalg.eigvalsh(gram)
    offdiag = gram - np.eye(gram.shape[0])
    max_mu = float(np.max(np.abs(offdiag))) if gram.shape[0] else 0.0
    lower = float(np.min(eigvals)) if eigvals.size else 0.0
    upper = float(np.max(eigvals)) if eigvals.size else 0.0
    if lower <= 1e-14:
        condition = math.inf
    else:
        condition = upper / lower
    return lower, upper, max_mu, condition


def orthonormal_child_contrasts(p: int) -> np.ndarray:
    """Return an orthonormal basis for vectors in R^p with zero child-sum."""

    eye = np.eye(p)
    ones = np.ones((p, 1)) / math.sqrt(p)
    projection = eye - ones @ ones.T
    q, r = np.linalg.qr(projection)
    # QR includes one near-zero direction.  Keep vectors with nonzero image.
    keep: list[np.ndarray] = []
    for idx in range(q.shape[1]):
      candidate = q[:, idx]
      residual = projection @ candidate
      if np.linalg.norm(residual) > 1e-10:
          keep.append(normalized(residual))
    return np.array(keep[: p - 1])


def haar_kozyrev_digit_atoms(p: int, max_level: int) -> np.ndarray:
    """Finite Archimedean digit-image Haar/Kozyrev contrast atoms.

    The grid has p^max_level equal cells.  For every p-ary node above the
    finest level, add p-1 zero-mean contrasts across its children.
    """

    grid_size = p**max_level
    contrasts = orthonormal_child_contrasts(p)
    atoms: list[np.ndarray] = []
    for level in range(max_level):
        node_count = p**level
        child_width = p ** (max_level - level - 1)
        for node in range(node_count):
            start = node * p * child_width
            for contrast in contrasts:
                atom = np.zeros(grid_size)
                for child in range(p):
                    lo = start + child * child_width
                    hi = lo + child_width
                    atom[lo:hi] = contrast[child] / math.sqrt(child_width)
                atoms.append(normalized(atom))
    return np.vstack(atoms)


def nested_radial_shell_atoms(p: int, max_level: int) -> np.ndarray:
    """Naive nested radial shell indicators [0, p^-j]."""

    grid_size = p**max_level
    atoms: list[np.ndarray] = []
    for level in range(max_level + 1):
        width = p ** (max_level - level)
        atom = np.zeros(grid_size)
        atom[:width] = 1.0 / math.sqrt(width)
        atoms.append(atom)
    return np.vstack(atoms)


def pawotg_series(p: int, sigma: float, terms: int = 200) -> float:
    total = 0.0
    logp = math.log(p)
    for depth in range(1, terms + 1):
        term = (p**depth) * math.exp(-((logp**2) * (depth**2)) / (4.0 * sigma**2))
        total += term
        if term < 1e-16:
            break
    return total


def lambda_range(p: int, alpha: float, max_level: int) -> tuple[float, float]:
    values = [p ** (-alpha * level) for level in range(max_level + 1)]
    return min(values), max(values)


def row_for_model(model: str, p: int, max_level: int, alpha: float, sigma: float) -> FrameRow:
    grid_size = p**max_level
    if model == "padic_kozyrev_exact":
        atom_count = p**max_level - 1
        lower = upper = condition = 1.0
        mu = 0.0
    elif model == "archimedean_digit_haar_kozyrev":
        atoms = haar_kozyrev_digit_atoms(p, max_level)
        lower, upper, mu, condition = gram_stats(atoms)
        atom_count = atoms.shape[0]
    elif model == "naive_radial_shell_nested":
        atoms = nested_radial_shell_atoms(p, max_level)
        lower, upper, mu, condition = gram_stats(atoms)
        atom_count = atoms.shape[0]
    else:
        raise ValueError(f"unknown model {model}")

    lam_min, lam_max = lambda_range(p, alpha, max_level)
    return FrameRow(
        model=model,
        p=p,
        max_level=max_level,
        atom_count=atom_count,
        grid_size=grid_size,
        alpha=alpha,
        frame_lower_A=lower,
        frame_upper_B=upper,
        max_offdiag_mu=mu,
        condition_number=condition,
        vladimirov_lambda_min=lam_min,
        vladimirov_lambda_max=lam_max,
        pawotg_sigma=sigma,
        pawotg_series=pawotg_series(p, sigma),
        naive_parent_child_overlap=p ** (-0.5),
        promotion_status="NO_PROMOTION",
    )


def write_csv(path: Path, rows: list[FrameRow]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(asdict(rows[0]).keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(asdict(row))


def write_json(path: Path, rows: list[FrameRow]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "status": "NON_PROMOTING_DIAGNOSTIC",
        "interpretation": {
            "carrier_positive_result": (
                "Vladimirov D^alpha has Kozyrev eigenfunctions; finite "
                "p-adic and digit-image Haar/Kozyrev contrast Grams are identity."
            ),
            "failed_object": (
                "Naive radial shell indicators nest under the Archimedean image "
                "and do not provide a uniform lower frame bound."
            ),
            "blocked_prediction": (
                "Schwarzschild matching and precision gravity remain blocked on "
                "W4 mass/stress-energy calibration and discrete-to-smooth Ricci."
            ),
        },
        "rows": [asdict(row) for row in rows],
    }
    path.write_text(json.dumps(payload, indent=2) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--p", type=int, default=3)
    parser.add_argument("--max-level", type=int, default=5)
    parser.add_argument("--alpha", type=float, default=2.0)
    parser.add_argument("--sigma", type=float, default=1.0 / math.sqrt(12.0))
    parser.add_argument("--json-out", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--csv-out", type=Path, default=DEFAULT_OUTPUT_CSV)
    args = parser.parse_args()

    if args.p < 2:
        raise SystemExit("--p must be at least 2")
    if args.max_level < 1:
        raise SystemExit("--max-level must be at least 1")

    rows = [
        row_for_model("padic_kozyrev_exact", args.p, args.max_level, args.alpha, args.sigma),
        row_for_model("archimedean_digit_haar_kozyrev", args.p, args.max_level, args.alpha, args.sigma),
        row_for_model("naive_radial_shell_nested", args.p, args.max_level, args.alpha, args.sigma),
    ]
    write_json(args.json_out, rows)
    write_csv(args.csv_out, rows)

    for row in rows:
        print(
            row.model,
            f"A={row.frame_lower_A:.6g}",
            f"B={row.frame_upper_B:.6g}",
            f"mu={row.max_offdiag_mu:.6g}",
            f"cond={row.condition_number:.6g}",
            f"pawotg={row.pawotg_series:.6g}",
        )


if __name__ == "__main__":
    main()
