#!/usr/bin/env python3
"""Finite BT-tree spectral-gap harness.

This script is a numerical receipt, not a proof.  It builds finite balls in a
(p+1)-regular tree, constructs combinatorial or normalized graph Laplacians
under explicit boundary conventions, and reports the first nonzero eigenvalue
when dense numpy diagonalization is available.

Boundary conventions:
  induced
      Use the finite induced ball. Boundary leaves have finite-ball degree 1.
      This is the usual Neumann-like finite graph convention and always has a
      zero constant mode.

  full-degree
      Keep only ball vertices but put the full (p+1)-regular degree on every
      diagonal. Boundary leaves therefore pay for missing exterior neighbors.
      This is a Dirichlet/killing-style truncation. The constant mode is no
      longer zero; the lowest eigenvalue approximates the infinite-tree bottom.

  induced-root-anchored
      Build the induced finite-ball Laplacian, then take the principal minor
      deleting the root. This pins the root value to zero while preserving the
      induced finite-ball edge degrees on the remaining vertices.

  full-degree-root-anchored
      Build the full-degree/killing Laplacian, then take the principal minor
      deleting the root. This combines exterior killing with a pinned root.

For a (p+1)-regular infinite tree, the expected full-degree combinatorial
bottom is (p+1) - 2*sqrt(p), and the normalized bottom is
1 - 2*sqrt(p)/(p+1).
"""

from __future__ import annotations

import argparse
import json
import math
from collections import deque
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

try:
    import numpy as np
except ImportError:  # pragma: no cover - exercised only in minimal envs.
    np = None  # type: ignore[assignment]


DEFAULT_PS = (2, 3, 5)
DEFAULT_DEPTHS = (2, 3, 4, 5, 6, 7)
DEFAULT_BOUNDARIES = (
    "induced",
    "full-degree",
    "induced-root-anchored",
    "full-degree-root-anchored",
)
DEFAULT_LAPLACIANS = ("combinatorial", "normalized")
DEFAULT_MAX_NODES = 2500
DEFAULT_OUT = Path("outputs/ym_bt_tree_spectral_gap_harness_summary.json")
PRESERVE_RATIO_THRESHOLD = 0.50
COLLAPSE_RATIO_THRESHOLD = 0.10


@dataclass(frozen=True)
class TreeBall:
    p: int
    depth: int
    regular_degree: int
    vertex_count: int
    edge_count: int
    shell_sizes: tuple[int, ...]
    edges: tuple[tuple[int, int], ...]


@dataclass(frozen=True)
class GapRow:
    p: int
    depth: int
    vertex_count: int
    matrix_size: int
    edge_count: int
    boundary: str
    laplacian: str
    eigenvalue_index_used: int
    zero_mode_expected: bool
    smallest_eigenvalue: float | None
    first_nonzero_eigenvalue: float | None
    infinite_tree_reference: float | None
    ratio_to_reference: float | None
    status: str


@dataclass(frozen=True)
class ConventionSummary:
    p: int
    boundary: str
    laplacian: str
    sample_count: int
    deepest_depth: int | None
    deepest_gap: float | None
    deepest_ratio_to_reference: float | None
    trend_slope_last: float | None
    classification: str
    rationale: str


def parse_int_list(raw: str) -> tuple[int, ...]:
    values = tuple(int(part.strip()) for part in raw.split(",") if part.strip())
    if not values:
        raise argparse.ArgumentTypeError("expected at least one integer")
    return values


def parse_str_list(raw: str) -> tuple[str, ...]:
    values = tuple(part.strip() for part in raw.split(",") if part.strip())
    if not values:
        raise argparse.ArgumentTypeError("expected at least one value")
    return values


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--p", dest="ps", type=parse_int_list, default=DEFAULT_PS)
    parser.add_argument("--depths", type=parse_int_list, default=DEFAULT_DEPTHS)
    parser.add_argument("--boundary", type=parse_str_list, default=DEFAULT_BOUNDARIES)
    parser.add_argument("--laplacian", type=parse_str_list, default=DEFAULT_LAPLACIANS)
    parser.add_argument("--max-nodes", type=int, default=DEFAULT_MAX_NODES)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--json", action="store_true", help="print full JSON summary")
    return parser.parse_args()


def build_tree_ball(p: int, depth: int) -> TreeBall:
    if p < 1:
        raise ValueError("p must be >= 1")
    if depth < 0:
        raise ValueError("depth must be >= 0")

    regular_degree = p + 1
    edges: list[tuple[int, int]] = []
    shell_sizes = [1]
    next_vertex = 1
    queue: deque[tuple[int, int]] = deque([(0, 0)])

    while queue:
        vertex, level = queue.popleft()
        if level == depth:
            continue
        child_count = regular_degree if level == 0 else p
        shell_count = 0
        for _ in range(child_count):
            child = next_vertex
            next_vertex += 1
            edges.append((vertex, child))
            queue.append((child, level + 1))
            shell_count += 1
        if level + 1 == len(shell_sizes):
            shell_sizes.append(0)
        shell_sizes[level + 1] += shell_count

    return TreeBall(
        p=p,
        depth=depth,
        regular_degree=regular_degree,
        vertex_count=next_vertex,
        edge_count=len(edges),
        shell_sizes=tuple(shell_sizes),
        edges=tuple(edges),
    )


def base_boundary(boundary: str) -> str:
    if boundary.startswith("induced"):
        return "induced"
    if boundary.startswith("full-degree"):
        return "full-degree"
    raise ValueError(f"unknown boundary convention: {boundary}")


def root_anchored(boundary: str) -> bool:
    return boundary.endswith("-root-anchored")


def degree_vector(ball: TreeBall, boundary: str) -> "np.ndarray":
    degrees = np.zeros(ball.vertex_count, dtype=float)
    for u, v in ball.edges:
        degrees[u] += 1.0
        degrees[v] += 1.0
    base = base_boundary(boundary)
    if base == "induced":
        return degrees
    if base == "full-degree":
        return np.full(ball.vertex_count, float(ball.regular_degree), dtype=float)
    raise ValueError(f"unknown boundary convention: {boundary}")


def laplacian_matrix(ball: TreeBall, boundary: str, laplacian: str) -> "np.ndarray":
    degrees = degree_vector(ball, boundary)
    adjacency = np.zeros((ball.vertex_count, ball.vertex_count), dtype=float)
    for u, v in ball.edges:
        adjacency[u, v] = 1.0
        adjacency[v, u] = 1.0

    if laplacian == "combinatorial":
        matrix = np.diag(degrees) - adjacency
        return matrix[1:, 1:] if root_anchored(boundary) else matrix

    if laplacian == "normalized":
        inv_sqrt = np.zeros_like(degrees)
        nonzero = degrees > 0
        inv_sqrt[nonzero] = 1.0 / np.sqrt(degrees[nonzero])
        matrix = np.eye(ball.vertex_count) - (inv_sqrt[:, None] * adjacency * inv_sqrt[None, :])
        return matrix[1:, 1:] if root_anchored(boundary) else matrix

    raise ValueError(f"unknown laplacian kind: {laplacian}")


def infinite_tree_reference(p: int, laplacian: str) -> float:
    q = p + 1
    if laplacian == "combinatorial":
        return q - 2.0 * math.sqrt(p)
    if laplacian == "normalized":
        return 1.0 - (2.0 * math.sqrt(p) / q)
    raise ValueError(f"unknown laplacian kind: {laplacian}")


def first_nonzero(eigenvalues: Iterable[float], tolerance: float = 1e-9) -> tuple[int, float | None]:
    for index, value in enumerate(eigenvalues):
        if value > tolerance:
            return index, float(value)
    return -1, None


def spectral_value_for_convention(eigenvalues: "np.ndarray", zero_mode_expected: bool) -> tuple[int, float | None]:
    if zero_mode_expected:
        return first_nonzero(eigenvalues)
    if len(eigenvalues) == 0:
        return -1, None
    return 0, float(eigenvalues[0])


def compute_gap(ball: TreeBall, boundary: str, laplacian: str) -> GapRow:
    if np is None:
        return GapRow(
            p=ball.p,
            depth=ball.depth,
            vertex_count=ball.vertex_count,
            matrix_size=0,
            edge_count=ball.edge_count,
            boundary=boundary,
            laplacian=laplacian,
            eigenvalue_index_used=-1,
            zero_mode_expected=boundary == "induced",
            smallest_eigenvalue=None,
            first_nonzero_eigenvalue=None,
            infinite_tree_reference=infinite_tree_reference(ball.p, laplacian),
            ratio_to_reference=None,
            status="skipped: numpy unavailable",
        )

    matrix = laplacian_matrix(ball, boundary, laplacian)
    eigenvalues = np.linalg.eigvalsh(matrix)
    eigenvalues.sort()
    zero_mode_expected = boundary == "induced"
    index, gap = spectral_value_for_convention(eigenvalues, zero_mode_expected)
    reference = infinite_tree_reference(ball.p, laplacian)
    ratio = None if gap is None or reference == 0.0 else gap / reference
    return GapRow(
        p=ball.p,
        depth=ball.depth,
        vertex_count=ball.vertex_count,
        matrix_size=int(matrix.shape[0]),
        edge_count=ball.edge_count,
        boundary=boundary,
        laplacian=laplacian,
        eigenvalue_index_used=index,
        zero_mode_expected=zero_mode_expected,
        smallest_eigenvalue=float(eigenvalues[0]),
        first_nonzero_eigenvalue=gap,
        infinite_tree_reference=reference,
        ratio_to_reference=ratio,
        status="computed",
    )


def classify_conventions(rows: list[GapRow]) -> list[ConventionSummary]:
    grouped: dict[tuple[int, str, str], list[GapRow]] = {}
    for row in rows:
        if row.status != "computed":
            continue
        grouped.setdefault((row.p, row.boundary, row.laplacian), []).append(row)

    summaries: list[ConventionSummary] = []
    for (p, boundary, laplacian), group in sorted(grouped.items()):
        ordered = sorted(group, key=lambda row: row.depth)
        deepest = ordered[-1] if ordered else None
        ratios = [row.ratio_to_reference for row in ordered if row.ratio_to_reference is not None]
        gaps = [row.first_nonzero_eigenvalue for row in ordered if row.first_nonzero_eigenvalue is not None]
        trend_slope = None
        if len(ratios) >= 2:
            trend_slope = ratios[-1] - ratios[-2]

        classification = "insufficient-data"
        rationale = "No computed finite-depth spectral rows were available."
        if deepest is not None and deepest.ratio_to_reference is not None and deepest.first_nonzero_eigenvalue is not None:
            deepest_ratio = deepest.ratio_to_reference
            if deepest_ratio >= PRESERVE_RATIO_THRESHOLD:
                classification = "apparent-nonamenable-gap-preserved"
                rationale = (
                    f"Deepest ratio {deepest_ratio:.3g} is at least "
                    f"{PRESERVE_RATIO_THRESHOLD:.3g} of the infinite-tree reference."
                )
            elif deepest_ratio <= COLLAPSE_RATIO_THRESHOLD:
                classification = "apparent-gap-collapse"
                rationale = (
                    f"Deepest ratio {deepest_ratio:.3g} is at most "
                    f"{COLLAPSE_RATIO_THRESHOLD:.3g} of the infinite-tree reference."
                )
            else:
                classification = "borderline-or-finite-size-sensitive"
                rationale = (
                    f"Deepest ratio {deepest_ratio:.3g} lies between collapse and "
                    "preservation thresholds."
                )

            if len(gaps) >= 3 and gaps[-1] < gaps[-2] < gaps[-3] and classification != "apparent-gap-collapse":
                rationale += " Last three gaps decrease monotonically, so deeper truncations should be checked."

        summaries.append(
            ConventionSummary(
                p=p,
                boundary=boundary,
                laplacian=laplacian,
                sample_count=len(ordered),
                deepest_depth=None if deepest is None else deepest.depth,
                deepest_gap=None if deepest is None else deepest.first_nonzero_eigenvalue,
                deepest_ratio_to_reference=None if deepest is None else deepest.ratio_to_reference,
                trend_slope_last=trend_slope,
                classification=classification,
                rationale=rationale,
            )
        )
    return summaries


def build_summary(rows: list[GapRow], skipped: list[dict[str, object]]) -> dict[str, object]:
    convention_summaries = classify_conventions(rows)
    classification_counts: dict[str, int] = {}
    for item in convention_summaries:
        classification_counts[item.classification] = classification_counts.get(item.classification, 0) + 1

    return {
        "control": {
            "O": "YM finite BT spectral-gap numerical harness.",
            "R": "Compare finite-ball regular-tree Laplacian gaps across p/depth/laplacian and boundary conventions.",
            "C": "scripts/ym_bt_tree_spectral_gap_harness.py",
            "S": "Numerical finite-volume probe only; not a YM Hamiltonian proof.",
            "L": "finite balls -> boundary convention -> eigenvalues -> preservation/collapse classification",
            "P": "Sweep induced, full-degree, and root-anchored principal-minor conventions to isolate boundary artifacts.",
            "G": "No Clay/YM promotion; output is diagnostic evidence only.",
            "F": "Does not construct gauge quotient, holonomy action, OS transfer, or continuum limit.",
        },
        "classification_thresholds": {
            "preserve_ratio_to_reference_min": PRESERVE_RATIO_THRESHOLD,
            "collapse_ratio_to_reference_max": COLLAPSE_RATIO_THRESHOLD,
        },
        "classification_counts": classification_counts,
        "convention_summaries": [asdict(item) for item in convention_summaries],
        "rows": [asdict(row) for row in rows],
        "skipped": skipped,
    }


def print_table(rows: list[GapRow], skipped: list[dict[str, object]]) -> None:
    print("YM finite BT tree spectral-gap harness")
    print("boundary=induced keeps finite-ball leaf degree 1; boundary=full-degree charges missing exterior edges")
    print("root-anchored variants use the principal minor deleting the root after the selected boundary convention")
    if np is None:
        print("numpy unavailable: eigenvalue computations skipped")
    if skipped:
        print(f"skipped cases: {len(skipped)} due to max-node cap")
    print()
    header = (
        "p depth nodes boundary    laplacian      lambda_min    lambda_first>0  "
        "inf_ref      ratio"
    )
    print(header)
    print("-" * len(header))
    for row in rows:
        lam0 = "NA" if row.smallest_eigenvalue is None else f"{row.smallest_eigenvalue: .6g}"
        gap = "NA" if row.first_nonzero_eigenvalue is None else f"{row.first_nonzero_eigenvalue: .6g}"
        ref = "NA" if row.infinite_tree_reference is None else f"{row.infinite_tree_reference: .6g}"
        ratio = "NA" if row.ratio_to_reference is None else f"{row.ratio_to_reference: .6g}"
        print(
            f"{row.p:<2} {row.depth:<5} {row.vertex_count:<5} "
            f"{row.boundary:<11} {row.laplacian:<14} {lam0:>11} {gap:>16} "
            f"{ref:>11} {ratio:>10}"
        )

    summaries = classify_conventions(rows)
    if summaries:
        print()
        print("classification by convention")
        print("p boundary                   laplacian      deepest ratio     class")
        print("-" * 82)
        for item in summaries:
            ratio = "NA" if item.deepest_ratio_to_reference is None else f"{item.deepest_ratio_to_reference:.6g}"
            print(
                f"{item.p:<2} {item.boundary:<26} {item.laplacian:<14} "
                f"{ratio:>13}     {item.classification}"
            )


def main() -> int:
    args = parse_args()
    allowed_boundaries = {
        "induced",
        "full-degree",
        "induced-root-anchored",
        "full-degree-root-anchored",
    }
    allowed_laplacians = {"combinatorial", "normalized"}
    bad_boundaries = set(args.boundary) - allowed_boundaries
    bad_laplacians = set(args.laplacian) - allowed_laplacians
    if bad_boundaries:
        raise SystemExit(f"unknown boundary convention(s): {sorted(bad_boundaries)}")
    if bad_laplacians:
        raise SystemExit(f"unknown laplacian kind(s): {sorted(bad_laplacians)}")

    rows: list[GapRow] = []
    skipped: list[dict[str, object]] = []
    for p in args.ps:
        for depth in args.depths:
            ball = build_tree_ball(p, depth)
            if ball.vertex_count > args.max_nodes:
                skipped.append(
                    {
                        "p": p,
                        "depth": depth,
                        "vertex_count": ball.vertex_count,
                        "reason": f"vertex count exceeds max_nodes={args.max_nodes}",
                    }
                )
                continue
            for boundary in args.boundary:
                for laplacian in args.laplacian:
                    rows.append(compute_gap(ball, boundary, laplacian))

    summary = build_summary(rows, skipped)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print_table(rows, skipped)
        print()
        print(f"wrote summary: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
