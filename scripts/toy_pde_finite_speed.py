#!/usr/bin/env python3
"""Toy finite-speed and MDL sanity check for the DASHI closure seam."""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass


def compact_bump(x: float, half_width: float) -> float:
    if abs(x) >= half_width:
        return 0.0
    z = x / half_width
    return math.exp(-1.0 / max(1e-12, 1.0 - z * z))


def support_radius(xs: list[float], values: list[float], tol: float) -> float:
    active = [abs(x) for x, value in zip(xs, values) if abs(value) > tol]
    return max(active, default=0.0)


@dataclass
class Snapshot:
    step: int
    time: float
    support_radius: float
    cone_bound: float
    excess: float


def hyperbolic_run(nx: int, nt: int, length: float, c: float, tol: float) -> list[Snapshot]:
    dx = 2.0 * length / (nx - 1)
    dt = 0.9 * dx / c
    xs = [-length + i * dx for i in range(nx)]
    phi0 = [compact_bump(x, half_width=0.5) for x in xs]
    lap0 = [0.0] * nx
    for i in range(1, nx - 1):
        lap0[i] = (phi0[i + 1] - 2.0 * phi0[i] + phi0[i - 1]) / (dx * dx)
    phi1 = phi0[:]
    for i in range(1, nx - 1):
        phi1[i] = phi0[i] + 0.5 * (c * dt) ** 2 * lap0[i]
    prev = phi0
    curr = phi1
    out: list[Snapshot] = []
    for n in range(1, nt + 1):
        nxt = curr[:]
        for i in range(1, nx - 1):
            lap = (curr[i + 1] - 2.0 * curr[i] + curr[i - 1]) / (dx * dx)
            nxt[i] = 2.0 * curr[i] - prev[i] + (c * dt) ** 2 * lap
        t = n * dt
        radius = support_radius(xs, curr, tol)
        cone = 0.5 + c * t
        out.append(Snapshot(n, t, radius, cone, radius - cone))
        prev, curr = curr, nxt
    return out


def elliptic_run(nx: int, nt: int, length: float, diffusion: float, tol: float) -> list[Snapshot]:
    dx = 2.0 * length / (nx - 1)
    dt = 0.4 * dx * dx / diffusion
    xs = [-length + i * dx for i in range(nx)]
    curr = [compact_bump(x, half_width=0.5) for x in xs]
    out: list[Snapshot] = []
    for n in range(1, nt + 1):
        nxt = curr[:]
        for i in range(1, nx - 1):
            lap = (curr[i + 1] - 2.0 * curr[i] + curr[i - 1]) / (dx * dx)
            nxt[i] = curr[i] + diffusion * dt * lap
        t = n * dt
        radius = support_radius(xs, curr, tol)
        out.append(Snapshot(n, t, radius, 0.5, radius - 0.5))
        curr = nxt
    return out


def print_summary(label: str, snapshots: list[Snapshot]) -> None:
    final = snapshots[-1]
    max_excess = max(s.excess for s in snapshots)
    print(
        f"{label}: final_t={final.time:.4f} final_radius={final.support_radius:.4f} "
        f"cone_bound={final.cone_bound:.4f} max_excess={max_excess:.4e}"
    )


def write_csv(path: str, label: str, snapshots: list[Snapshot]) -> None:
    with open(path, "w", newline="", encoding="utf-8") as fh:
        writer = csv.writer(fh)
        writer.writerow(["regime", "step", "time", "support_radius", "cone_bound", "excess"])
        for s in snapshots:
            writer.writerow([label, s.step, s.time, s.support_radius, s.cone_bound, s.excess])


def mdl_table() -> str:
    rows = [
        ("A", "Lorentzian principal symbol", 4, 0, "baseline"),
        ("B", "Euclidean surrogate + anisotropy repairs", 7, 2, "preferred frame / tail leakage"),
        ("C", "Lorentzian + subcritical quadratic forcing", 5, 0, "baseline + one forcing gate"),
    ]
    header = "model,description,param_count,symmetry_break_penalty,fit_note"
    body = "\n".join(",".join(map(str, row)) for row in rows)
    return f"{header}\n{body}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--nx", type=int, default=401)
    parser.add_argument("--nt", type=int, default=120)
    parser.add_argument("--length", type=float, default=8.0)
    parser.add_argument("--c", type=float, default=1.0)
    parser.add_argument("--diffusion", type=float, default=0.25)
    parser.add_argument("--tol", type=float, default=1e-4)
    parser.add_argument("--csv", type=str, default="")
    args = parser.parse_args()

    hyper = hyperbolic_run(args.nx, args.nt, args.length, args.c, args.tol)
    elliptic = elliptic_run(args.nx, args.nt, args.length, args.diffusion, args.tol)

    print_summary("hyperbolic", hyper)
    print_summary("elliptic", elliptic)
    print()
    print("mdl_heuristic_table")
    print(mdl_table())

    if args.csv:
        write_csv(args.csv, "hyperbolic", hyper)


if __name__ == "__main__":
    main()
