#!/usr/bin/env python3
"""Coordinate-aware plots for the finite 243/27 phase carriers.

Unlike a row-major or orbit-block circle, the layout exposes the state product:

  Core243      = F3^3_base x F3^2_phase
  AxisBoundary = F3_axis x F3^2_phase

The repo action fixes the base coordinate and acts on the phase pair.  The
visual coordinates therefore encode owned state coordinates rather than a
layout heuristic.
"""
from __future__ import annotations

import argparse
import json
import math
from itertools import product
from pathlib import Path

import matplotlib.pyplot as plt

F3 = (0, 1, 2)


def c3_core(x):
    k, u, v, p, q = x
    return (k, u, v, (p + 1) % 3, (q + 1) % 3)


def invert_core(x):
    k, u, v, p, q = x
    return (k, u, v, (-p) % 3, (-q) % 3)


def c3_boundary(x):
    m, p, q = x
    return (m, (p + 1) % 3, (q + 1) % 3)


def invert_boundary(x):
    m, p, q = x
    return (m, (-p) % 3, (-q) % 3)


def base_index(k, u, v):
    return 9 * k + 3 * u + v


def render(states, actions, pos, output, title, node_size=10, alpha=0.2):
    fig, ax = plt.subplots(figsize=(10, 10))
    for action in actions:
        for state in states:
            target = action(state)
            x0, y0 = pos[state]
            x1, y1 = pos[target]
            ax.annotate(
                "",
                xy=(x1, y1),
                xytext=(x0, y0),
                arrowprops={"arrowstyle": "->", "lw": 0.32, "alpha": alpha},
            )
    ax.scatter([pos[s][0] for s in states], [pos[s][1] for s in states], s=node_size, zorder=3)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.set_title(title)
    fig.savefig(output, dpi=240, bbox_inches="tight")
    plt.close(fig)


def build(output_dir: Path):
    output_dir.mkdir(parents=True, exist_ok=True)
    core = list(product(F3, repeat=5))
    boundary = list(product(F3, repeat=3))

    radii = {0: 3.3, 1: 4.7, 2: 6.1}
    sector = 2 * math.pi / 27
    core_pos = {}
    for state in core:
        k, u, v, p, q = state
        theta = math.pi / 2 - 2 * math.pi * base_index(k, u, v) / 27 + (q - 1) * 0.22 * sector
        core_pos[state] = (radii[p] * math.cos(theta), radii[p] * math.sin(theta))

    render(
        core,
        (c3_core, invert_core),
        core_pos,
        output_dir / "core243_phase_coordinates.png",
        "Core243: angle=(k,u,v), radius=p, angular offset=q",
        9,
        0.19,
    )

    # Observer quotient: forget q, retaining 27 base fibres x 3 p-radii.
    skeleton = list(product(F3, F3, F3, F3))
    skeleton_pos = {}
    for state in skeleton:
        k, u, v, p = state
        theta = math.pi / 2 - 2 * math.pi * base_index(k, u, v) / 27
        skeleton_pos[state] = (radii[p] * math.cos(theta), radii[p] * math.sin(theta))

    def c3_skeleton(x):
        k, u, v, p = x
        return (k, u, v, (p + 1) % 3)

    def inv_skeleton(x):
        k, u, v, p = x
        return (k, u, v, (-p) % 3)

    render(
        skeleton,
        (c3_skeleton, inv_skeleton),
        skeleton_pos,
        output_dir / "core243_q_quotient_81.png",
        "Core243 q-quotient: 27 base sectors x 3 phase radii",
        18,
        0.28,
    )

    boundary_pos = {}
    for state in boundary:
        m, p, q = state
        theta = math.pi / 2 - 2 * math.pi * m / 3 + (q - 1) * 0.12
        radius = {0: 7.4, 1: 8.25, 2: 9.1}[p]
        boundary_pos[state] = (radius * math.cos(theta), radius * math.sin(theta))

    render(
        boundary,
        (c3_boundary, invert_boundary),
        boundary_pos,
        output_dir / "axis_boundary27_phase_coordinates.png",
        "AxisBoundary27: angle=m, radius=p, angular offset=q",
        30,
        0.3,
    )

    receipt = {
        "core243_states": len(core),
        "core243_q_quotient_states": len(skeleton),
        "axis_boundary_states": len(boundary),
        "core_coordinate_meaning": {"angle": "(k,u,v)", "radius": "p", "offset": "q"},
        "boundary_coordinate_meaning": {"angle": "m", "radius": "p", "offset": "q"},
    }
    (output_dir / "phase_coordinate_graph_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--output-dir", default="phase_coordinate_graphs")
    args = p.parse_args()
    print(json.dumps(build(Path(args.output_dir)), indent=2))


if __name__ == "__main__":
    main()
