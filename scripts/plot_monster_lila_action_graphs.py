#!/usr/bin/env python3
"""Render the repo-native finite Monster/LILA actions on fixed lattices.

No force-directed layout is used: node positions are deterministic row-major
coordinates, so visual differences come from the action and/or declared state
ordering rather than from a graph-layout optimizer.

Consumes the exact T5/E8 constructors already checked by
check_t5_e8_c10_bridge.py and the repo-native X6 translation law from
Monster3BFiniteHeisenbergGeneratorsExact.agda.
"""

from pathlib import Path
import argparse
import csv
import itertools
import json
import math

import matplotlib.pyplot as plt

import check_t5_e8_c10_bridge as audit


def row_major(states, cols):
    return {s: (i % cols, -(i // cols)) for i, s in enumerate(states)}


def render(states, actions, cols, output, title, positions=None, alpha=.15):
    states = list(states)
    pos = positions or row_major(states, cols)
    fig, ax = plt.subplots(figsize=(10, 10))
    for action in actions:
        for s in states:
            t = action(s)
            x0, y0 = pos[s]
            x1, y1 = pos[t]
            ax.annotate(
                "", xy=(x1, y1), xytext=(x0, y0),
                arrowprops={"arrowstyle": "->", "lw": .25, "alpha": alpha},
            )
    ax.scatter([pos[s][0] for s in states], [pos[s][1] for s in states], s=5)
    ax.set_aspect("equal", adjustable="box")
    ax.axis("off")
    ax.set_title(title)
    fig.savefig(output, dpi=220, bbox_inches="tight")
    plt.close(fig)


def write_edges(states, actions, names, path):
    states = list(states)
    index = {s: i for i, s in enumerate(states)}
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["source", "target", "action"])
        for action, name in zip(actions, names):
            for s in states:
                w.writerow([index[s], index[action(s)], name])


def displacement_count(states, actions, cols, positions=None):
    states = list(states)
    pos = positions or row_major(states, cols)
    ds = set()
    for action in actions:
        for s in states:
            t = action(s)
            x0, y0 = pos[s]
            x1, y1 = pos[t]
            ds.add((x1 - x0, y1 - y0))
    return len(ds)


def x6_states():
    return list(itertools.product(range(3), repeat=6))


def translate(axis, sign=1):
    def action(x):
        y = list(x)
        y[axis] = (y[axis] + sign) % 3
        return tuple(y)
    return action


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--outdir", default="outputs/monster_lila_action_graphs")
    args = p.parse_args()
    out = Path(args.outdir)
    out.mkdir(parents=True, exist_ok=True)

    ts = audit.t5_relative()
    roots = [tuple(audit.Fraction(x) for x in r) for r in audit.e8_roots()]
    cperm = {r: audit.cox(r) for r in roots}

    def cpow(r, n):
        y = r
        for _ in range(n):
            y = cperm[y]
        return y

    c6perm = {r: cpow(r, 6) for r in roots}
    c6 = lambda r: c6perm[r]
    g10e = lambda r: audit.neg(c6(r))
    matching = audit.build_equivariant_bijection(ts, roots, g10e)

    render(ts, [audit.rot5, audit.neg], 16, out / "t5_c5_negation.png",
           "T5 relative 240: rotation + negation", alpha=.22)

    roots_sorted = sorted(roots)
    render(roots_sorted, [c6, audit.neg], 16, out / "e8_c6_negation_native.png",
           "E8 roots 240: Coxeter c^6 + root negation", alpha=.22)

    tpos = row_major(ts, 16)
    epos = {matching[t]: tpos[t] for t in ts}
    render(roots, [c6, audit.neg], 16, out / "e8_c6_negation_on_t5_lattice.png",
           "E8 action transported through T5/E8 intertwiner", epos, alpha=.22)

    reflections = [lambda r, a=a: audit.reflect(r, a) for a in audit.SIMPLE]
    render(roots_sorted, reflections, 16, out / "e8_weyl_simple_reflections.png",
           "E8 roots: eight simple reflections", alpha=.055)

    xs = x6_states()
    plus = [translate(i, 1) for i in range(6)]
    minus = [translate(i, -1) for i in range(6)]
    render(xs, plus, 27, out / "monster3b_x6_six_translations.png",
           "Monster 3B X6 = F3^6: six translations", alpha=.08)
    render(xs, plus + minus, 27, out / "monster3b_x6_12_translations.png",
           "Monster 3B X6: +/- six translation generators", alpha=.035)

    write_edges(ts, [audit.rot5, audit.neg], ["rot5", "neg"], out / "t5_edges.csv")
    write_edges(roots_sorted, [c6, audit.neg] + reflections,
                ["coxeter6", "neg"] + [f"simple_reflection_{i+1}" for i in range(8)],
                out / "e8_edges.csv")
    write_edges(xs, plus + minus,
                [f"translate_{i}_plus" for i in range(6)] + [f"translate_{i}_minus" for i in range(6)],
                out / "monster3b_x6_edges.csv")

    transported_ok = all(
        matching[audit.rot5(t)] == c6(matching[t]) and
        matching[audit.neg(t)] == audit.neg(matching[t])
        for t in ts
    )
    metadata = {
        "t5": {"nodes": 240, "edges": 480, "c5_orbits": 48, "c10_orbits": 24,
               "unique_lattice_displacements": displacement_count(ts, [audit.rot5, audit.neg], 16)},
        "e8_c6_negation": {"nodes": 240, "edges": 480,
                           "transported_action_matches_t5": transported_ok},
        "e8_weyl": {"nodes": 240, "generators": 8, "edges": 1920,
                     "unique_lattice_displacements": displacement_count(roots_sorted, reflections, 16)},
        "monster3b_x6": {"nodes": 729, "plus_edges": 4374, "signed_edges": 8748,
                          "plus_unique_lattice_displacements": displacement_count(xs, plus, 27),
                          "signed_unique_lattice_displacements": displacement_count(xs, plus + minus, 27)},
    }
    (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
