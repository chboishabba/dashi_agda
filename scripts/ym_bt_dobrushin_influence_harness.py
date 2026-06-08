#!/usr/bin/env python3
"""Toy Dobrushin influence harness for BT-tree vs hypercubic YM transfer lanes.

This is a numerical proxy only.  It does not model Yang-Mills measure
construction, gauge quotient reflection positivity, Wilson action comparison,
or Dobrushin-Shlosman complete analyticity.  It records the simplest
nearest-neighbor compact-spin style bound

    row_sum <= degree * tanh(beta * coupling)

on finite regular trees and compares it with a 4D hypercubic nearest-neighbor
degree of 8.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


DEFAULT_P_VALUES = (2, 3, 5, 7, 11)
DEFAULT_BETA_VALUES = (
    0.01,
    0.025,
    0.05,
    0.075,
    0.10,
    0.125,
    0.15,
    0.20,
    0.25,
    0.30,
    0.40,
    0.50,
    0.75,
    1.00,
)
DEFAULT_DEPTH = 4
DEFAULT_COUPLING = 1.0
HYPERCUBIC_4D_DEGREE = 8


@dataclass(frozen=True)
class GraphSummary:
    name: str
    degree: int
    depth: int | None
    vertex_count: int | None
    edge_count: int | None
    critical_beta: float


@dataclass(frozen=True)
class InfluenceRow:
    graph: str
    beta: float
    coupling: float
    influence_per_edge: float
    max_degree: int
    max_row_sum: float
    plausible_uniqueness_proxy: bool
    margin_to_one: float


@dataclass(frozen=True)
class HarnessSummary:
    status: str
    caveat: str
    coupling: float
    depth: int
    graph_summaries: list[GraphSummary]
    rows: list[InfluenceRow]
    regimes: dict[str, object]


def parse_csv_floats(raw: str) -> tuple[float, ...]:
    values = tuple(float(item.strip()) for item in raw.split(",") if item.strip())
    if not values:
        raise argparse.ArgumentTypeError("expected at least one numeric value")
    return values


def parse_csv_ints(raw: str) -> tuple[int, ...]:
    values = tuple(int(item.strip()) for item in raw.split(",") if item.strip())
    if not values:
        raise argparse.ArgumentTypeError("expected at least one integer value")
    return values


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--p-values",
        type=parse_csv_ints,
        default=DEFAULT_P_VALUES,
        help="Comma-separated BT primes/branch parameters; degree is p+1.",
    )
    parser.add_argument(
        "--betas",
        type=parse_csv_floats,
        default=DEFAULT_BETA_VALUES,
        help="Comma-separated beta values to scan.",
    )
    parser.add_argument(
        "--coupling",
        type=float,
        default=DEFAULT_COUPLING,
        help="Toy nearest-neighbor coupling multiplier J.",
    )
    parser.add_argument(
        "--depth",
        type=int,
        default=DEFAULT_DEPTH,
        help="Finite rooted regular-tree depth used for vertex/edge counts.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Optional JSON output path.  If omitted, only stdout is written.",
    )
    return parser.parse_args()


def finite_regular_tree_counts(degree: int, depth: int) -> tuple[int, int]:
    """Return vertex/edge counts for a rooted finite degree-regular tree ball."""
    if depth < 0:
        raise ValueError("depth must be nonnegative")
    if degree < 1:
        raise ValueError("degree must be positive")
    if depth == 0:
        return 1, 0
    if degree == 1:
        return 2, 1

    vertices = 1
    frontier = degree
    for _level in range(1, depth + 1):
        vertices += frontier
        frontier *= degree - 1
    return vertices, vertices - 1


def critical_beta(degree: int, coupling: float) -> float:
    if coupling <= 0:
        raise ValueError("coupling must be positive")
    return math.atanh(1.0 / degree) / coupling


def row_sum(beta: float, coupling: float, degree: int) -> InfluenceRow:
    influence = math.tanh(beta * coupling)
    total = degree * influence
    return InfluenceRow(
        graph="",
        beta=beta,
        coupling=coupling,
        influence_per_edge=influence,
        max_degree=degree,
        max_row_sum=total,
        plausible_uniqueness_proxy=total < 1.0,
        margin_to_one=1.0 - total,
    )


def with_graph(row: InfluenceRow, graph: str) -> InfluenceRow:
    return InfluenceRow(
        graph=graph,
        beta=row.beta,
        coupling=row.coupling,
        influence_per_edge=row.influence_per_edge,
        max_degree=row.max_degree,
        max_row_sum=row.max_row_sum,
        plausible_uniqueness_proxy=row.plausible_uniqueness_proxy,
        margin_to_one=row.margin_to_one,
    )


def graph_summaries(p_values: Iterable[int], depth: int, coupling: float) -> list[GraphSummary]:
    summaries: list[GraphSummary] = []
    for p in p_values:
        degree = p + 1
        vertices, edges = finite_regular_tree_counts(degree, depth)
        summaries.append(
            GraphSummary(
                name=f"BT_tree_p{p}_degree{degree}",
                degree=degree,
                depth=depth,
                vertex_count=vertices,
                edge_count=edges,
                critical_beta=critical_beta(degree, coupling),
            )
        )
    summaries.append(
        GraphSummary(
            name="hypercubic_4d_degree8",
            degree=HYPERCUBIC_4D_DEGREE,
            depth=None,
            vertex_count=None,
            edge_count=None,
            critical_beta=critical_beta(HYPERCUBIC_4D_DEGREE, coupling),
        )
    )
    return summaries


def build_summary(args: argparse.Namespace) -> HarnessSummary:
    if args.depth < 0:
        raise ValueError("--depth must be nonnegative")
    if args.coupling <= 0:
        raise ValueError("--coupling must be positive")

    summaries = graph_summaries(args.p_values, args.depth, args.coupling)
    rows: list[InfluenceRow] = []
    for graph in summaries:
        for beta in args.betas:
            rows.append(with_graph(row_sum(beta, args.coupling, graph.degree), graph.name))

    safe_betas_by_graph: dict[str, list[float]] = {}
    first_unsafe_by_graph: dict[str, float | None] = {}
    for graph in summaries:
        graph_rows = [row for row in rows if row.graph == graph.name]
        safe = [row.beta for row in graph_rows if row.plausible_uniqueness_proxy]
        unsafe = [row.beta for row in graph_rows if not row.plausible_uniqueness_proxy]
        safe_betas_by_graph[graph.name] = safe
        first_unsafe_by_graph[graph.name] = min(unsafe) if unsafe else None

    bt_vs_hypercubic: list[dict[str, object]] = []
    hyper = next(graph for graph in summaries if graph.name == "hypercubic_4d_degree8")
    for graph in summaries:
        if graph.name == hyper.name:
            continue
        bt_vs_hypercubic.append(
            {
                "bt_graph": graph.name,
                "bt_degree": graph.degree,
                "hypercubic_degree": hyper.degree,
                "bt_critical_beta": graph.critical_beta,
                "hypercubic_critical_beta": hyper.critical_beta,
                "bt_has_larger_proxy_window_than_hypercubic": (
                    graph.critical_beta > hyper.critical_beta
                ),
            }
        )

    return HarnessSummary(
        status="toy_proxy_only_no_proof_claim",
        caveat=(
            "Dobrushin row sums below 1 are a nearest-neighbor uniqueness proxy "
            "for this scalar compact-spin bound only; they do not prove BT-to-OS "
            "transfer, complete analyticity, reflection positivity, or YM mass gap."
        ),
        coupling=args.coupling,
        depth=args.depth,
        graph_summaries=summaries,
        rows=rows,
        regimes={
            "safe_betas_by_graph": safe_betas_by_graph,
            "first_unsafe_beta_by_graph": first_unsafe_by_graph,
            "bt_vs_hypercubic": bt_vs_hypercubic,
        },
    )


def to_jsonable(summary: HarnessSummary) -> dict[str, object]:
    return {
        "status": summary.status,
        "caveat": summary.caveat,
        "coupling": summary.coupling,
        "depth": summary.depth,
        "graph_summaries": [asdict(item) for item in summary.graph_summaries],
        "rows": [asdict(item) for item in summary.rows],
        "regimes": summary.regimes,
    }


def print_text_summary(summary: HarnessSummary) -> None:
    print("YM BT Dobrushin/tree influence toy harness")
    print(f"status: {summary.status}")
    print(f"caveat: {summary.caveat}")
    print(f"coupling: {summary.coupling}")
    print(f"finite tree depth for counts: {summary.depth}")
    print()
    print("critical beta thresholds for degree * tanh(beta * coupling) < 1:")
    for graph in summary.graph_summaries:
        counts = (
            f", vertices={graph.vertex_count}, edges={graph.edge_count}"
            if graph.vertex_count is not None
            else ""
        )
        print(
            f"  {graph.name}: degree={graph.degree}, "
            f"beta_crit={graph.critical_beta:.9f}{counts}"
        )
    print()
    print("scan rows:")
    for row in summary.rows:
        status = "safe_proxy" if row.plausible_uniqueness_proxy else "unsafe_proxy"
        print(
            f"  {row.graph} beta={row.beta:.6f}: "
            f"edge={row.influence_per_edge:.9f}, "
            f"row_sum={row.max_row_sum:.9f}, "
            f"margin={row.margin_to_one:.9f}, {status}"
        )
    print()
    print("BT vs hypercubic degree-8 proxy comparison:")
    for item in summary.regimes["bt_vs_hypercubic"]:
        verdict = (
            "wider_than_hypercubic"
            if item["bt_has_larger_proxy_window_than_hypercubic"]
            else "not_wider_than_hypercubic"
        )
        print(
            f"  {item['bt_graph']}: degree {item['bt_degree']} vs 8, "
            f"beta_crit={item['bt_critical_beta']:.9f} vs "
            f"{item['hypercubic_critical_beta']:.9f}: {verdict}"
        )


def main() -> int:
    args = parse_args()
    summary = build_summary(args)
    print_text_summary(summary)
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(to_jsonable(summary), indent=2, sort_keys=True) + "\n")
        print()
        print(f"wrote_json: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
