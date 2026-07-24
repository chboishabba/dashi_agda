#!/usr/bin/env python3
"""Bounded scout search for the constant-free ternary elementary operator.

The search is deliberately non-promoting.  It evaluates ternary trees on a fixed
set of complex samples, deduplicates by numerical signatures, and emits the best
candidates for 1, exp(x), log(x), x-y, and EML(x,y).  Exact promotion requires a
side-condition-aware Agda RewriteCertificate.
"""

from __future__ import annotations

import argparse
import cmath
import dataclasses
import json
import math
from pathlib import Path
from typing import Callable, Iterable, Sequence


@dataclasses.dataclass(frozen=True)
class Tree:
    label: str | None = None
    children: tuple["Tree", "Tree", "Tree"] | None = None

    @property
    def depth(self) -> int:
        if self.children is None:
            return 0
        return 1 + max(child.depth for child in self.children)

    @property
    def nodes(self) -> int:
        if self.children is None:
            return 1
        return 1 + sum(child.nodes for child in self.children)

    def render(self) -> str:
        if self.children is None:
            assert self.label is not None
            return self.label
        a, b, c = self.children
        return f"T({a.render()},{b.render()},{c.render()})"


def ternary(x: complex, y: complex, z: complex, eps: float) -> complex:
    lx = cmath.log(x)
    if abs(lx) <= eps or abs(cmath.exp(y)) <= eps:
        raise ValueError("inadmissible denominator")
    return (cmath.exp(x) / lx) * (cmath.log(z) / cmath.exp(y))


def evaluate(tree: Tree, env: dict[str, complex], eps: float) -> complex:
    if tree.children is None:
        assert tree.label is not None
        return env[tree.label]
    a, b, c = tree.children
    return ternary(evaluate(a, env, eps), evaluate(b, env, eps), evaluate(c, env, eps), eps)


def safe_signature(
    tree: Tree,
    samples: Sequence[dict[str, complex]],
    eps: float,
    digits: int,
) -> tuple[tuple[float, float], ...] | None:
    values: list[tuple[float, float]] = []
    try:
        for env in samples:
            value = evaluate(tree, env, eps)
            if not (math.isfinite(value.real) and math.isfinite(value.imag)):
                return None
            values.append((round(value.real, digits), round(value.imag, digits)))
    except (ValueError, OverflowError, ZeroDivisionError):
        return None
    return tuple(values)


def target_values(
    target: str,
    samples: Sequence[dict[str, complex]],
) -> list[complex]:
    if target == "one":
        return [1.0 + 0.0j for _ in samples]
    if target == "exp":
        return [cmath.exp(env["x"]) for env in samples]
    if target == "log":
        return [cmath.log(env["x"]) for env in samples]
    if target == "sub":
        return [env["x"] - env["y"] for env in samples]
    if target == "eml":
        return [cmath.exp(env["x"]) - cmath.log(env["y"]) for env in samples]
    raise ValueError(f"unknown target: {target}")


def max_error(
    tree: Tree,
    target: str,
    samples: Sequence[dict[str, complex]],
    eps: float,
) -> float:
    wanted = target_values(target, samples)
    try:
        got = [evaluate(tree, env, eps) for env in samples]
    except (ValueError, OverflowError, ZeroDivisionError):
        return math.inf
    return max(abs(a - b) for a, b in zip(got, wanted, strict=True))


def canonical_samples() -> list[dict[str, complex]]:
    # Avoid x=1 and the principal branch cut while retaining mixed signs and
    # nonzero imaginary parts.  These are scout points, not a proof domain.
    return [
        {"x": 2.0 + 0.2j, "y": 3.0 - 0.1j, "w": 1.7 + 0.3j},
        {"x": 0.6 + 0.4j, "y": 1.8 + 0.5j, "w": 2.4 - 0.2j},
        {"x": -0.7 + 0.8j, "y": 2.2 + 0.6j, "w": 0.9 + 0.7j},
        {"x": 1.3 - 0.6j, "y": -0.8 + 1.1j, "w": 2.8 + 0.4j},
    ]


def enumerate_beam(
    max_depth: int,
    beam_width: int,
    samples: Sequence[dict[str, complex]],
    eps: float,
    signature_digits: int,
) -> list[Tree]:
    leaves = [Tree(label=name) for name in ("x", "y", "w")]
    all_trees = list(leaves)
    frontier = list(leaves)
    seen: dict[tuple[tuple[float, float], ...], Tree] = {}

    for tree in leaves:
        sig = safe_signature(tree, samples, eps, signature_digits)
        if sig is not None:
            seen[sig] = tree

    for _depth in range(1, max_depth + 1):
        pool = all_trees[-beam_width:]
        generated: list[Tree] = []
        for a in frontier:
            for b in pool:
                for c in pool:
                    tree = Tree(children=(a, b, c))
                    sig = safe_signature(tree, samples, eps, signature_digits)
                    if sig is None:
                        continue
                    incumbent = seen.get(sig)
                    if incumbent is None or (tree.nodes, tree.depth) < (incumbent.nodes, incumbent.depth):
                        seen[sig] = tree
                        generated.append(tree)
        generated.sort(key=lambda t: (t.nodes, t.render()))
        frontier = generated[:beam_width]
        if not frontier:
            break
        all_trees.extend(frontier)
    return list(seen.values())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, default=2)
    parser.add_argument("--beam-width", type=int, default=80)
    parser.add_argument("--top-k", type=int, default=10)
    parser.add_argument("--eps", type=float, default=1e-12)
    parser.add_argument("--signature-digits", type=int, default=10)
    parser.add_argument("--out", type=Path, default=Path("ternary_elementary_scout.json"))
    args = parser.parse_args()

    samples = canonical_samples()
    trees = enumerate_beam(
        max_depth=args.max_depth,
        beam_width=args.beam_width,
        samples=samples,
        eps=args.eps,
        signature_digits=args.signature_digits,
    )

    report: dict[str, object] = {
        "status": "scoutOnly",
        "operator": "T(x,y,z)=(exp(x)/log(x))*(log(z)/exp(y))",
        "max_depth": args.max_depth,
        "beam_width": args.beam_width,
        "sample_count": len(samples),
        "candidate_count": len(trees),
        "targets": {},
        "promotion_rule": "Numerical agreement is not a proof; require an Agda RewriteCertificate with discharged side conditions.",
    }

    targets: dict[str, list[dict[str, object]]] = {}
    for target in ("one", "exp", "log", "sub", "eml"):
        ranked = sorted(
            ((max_error(tree, target, samples, args.eps), tree) for tree in trees),
            key=lambda pair: (pair[0], pair[1].nodes, pair[1].render()),
        )[: args.top_k]
        targets[target] = [
            {
                "tree": tree.render(),
                "max_error": error,
                "depth": tree.depth,
                "nodes": tree.nodes,
                "status": "symbolicCandidate" if error <= 1e-9 else "scoutOnly",
            }
            for error, tree in ranked
        ]
    report["targets"] = targets

    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[ok] wrote {args.out} with {len(trees)} deduplicated scout trees")
    for target, rows in targets.items():
        best = rows[0]
        print(f"[{target}] error={best['max_error']:.3e} depth={best['depth']} tree={best['tree']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
