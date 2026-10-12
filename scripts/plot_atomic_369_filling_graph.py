#!/usr/bin/env python3
"""Render the exact early structural atomic filling graph and observer quotients.

The structural path follows the already-owned Madelung prefix

  1s^2 | 2s^2 2p^6 | 3s^2 3p^6

through the historical closure coordinates 2, 10, 18.  This is a structural
filling graph.  It is not a claim that the Madelung order is an exception-free
interacting many-electron ground-state theorem.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import matplotlib.pyplot as plt

BLOCKS = (("1s", 2), ("2s", 2), ("2p", 6), ("3s", 2), ("3p", 6))
CLOSURES = {2: "He-like", 10: "Ne-like", 18: "Ar-like"}


def block_for_electron(electron: int) -> str:
    if electron == 0:
        return "vacuum"
    total = 0
    for name, cap in BLOCKS:
        total += cap
        if electron <= total:
            return name
    raise ValueError(electron)


def circle_positions(n: int, radius: float = 1.0):
    return {
        i: (
            radius * math.cos(math.pi / 2 - 2 * math.pi * i / n),
            radius * math.sin(math.pi / 2 - 2 * math.pi * i / n),
        )
        for i in range(n)
    }


def render(output: Path) -> dict:
    states = list(range(19))
    pos = circle_positions(len(states), 5.0)
    fig, ax = plt.subplots(figsize=(10, 10))

    for n in range(18):
        x0, y0 = pos[n]
        x1, y1 = pos[n + 1]
        ax.annotate(
            "",
            xy=(x1, y1),
            xytext=(x0, y0),
            arrowprops={"arrowstyle": "->", "lw": 0.9, "alpha": 0.55},
        )

    ax.scatter([pos[n][0] for n in states], [pos[n][1] for n in states], s=42, zorder=3)
    for n in states:
        x, y = pos[n]
        label = f"C{n}"
        if n in CLOSURES:
            label += f"\n{CLOSURES[n]}"
        ax.text(1.11 * x, 1.11 * y, label, fontsize=7, ha="center", va="center")

    # Put the subshell observer in the centre instead of inventing more radii.
    observer = " | ".join(f"{name}^{cap}" for name, cap in BLOCKS)
    ax.text(0, 0, observer, ha="center", va="center", fontsize=11)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.set_title("Early structural atomic filling graph: C_N -> C_{N+1}")
    fig.savefig(output, dpi=240, bbox_inches="tight")
    plt.close(fig)

    cumulative = []
    total = 0
    for _, cap in BLOCKS:
        total += cap
        cumulative.append(total)

    return {
        "states": len(states),
        "directed_edges": 18,
        "block_capacities": [cap for _, cap in BLOCKS],
        "block_end_counts": cumulative,
        "closure_counts": sorted(CLOSURES),
        "epistemic_boundary": (
            "exact structural Madelung filling observer through Ar-like closure; "
            "not an interacting-ground-state or measured-spectrum theorem"
        ),
    }


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--output", default="atomic_369_filling_graph.png")
    p.add_argument("--receipt")
    args = p.parse_args()
    result = render(Path(args.output))
    if args.receipt:
        Path(args.receipt).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
