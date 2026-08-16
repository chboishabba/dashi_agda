#!/usr/bin/env python3
"""Static dependency-cut audit for the DASHI Agda closure graph.

This is deliberately a *compiler engineering* tool, not a proof oracle.  It
finds expensive-looking transitive import cones and candidate compiled theorem
boundaries from repository source alone.  It never changes theorem authority.

Typical use:

  python scripts/ns_agda_dependency_cut_audit.py \
    --root DASHI.Physics.Closure.NSTriadKNABCInhabitationRound58Exact \
    --top 30

Optional measured RSS can be supplied repeatedly:

  --rss DASHI.Physics.Closure.Foo=15800

where the value is MiB.  Measured RSS dominates the static heuristic when
ranking candidate cuts.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, MutableMapping, Sequence, Set, Tuple

REPO = Path(__file__).resolve().parents[1]
AGDA_ROOTS = (REPO / "DASHI",)

IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.']+)", re.MULTILINE)
SOLVE_RE = re.compile(r"\bsolve\b")
SUBST_RE = re.compile(r"\bsubst(?:₂)?\b")
REWRITE_RE = re.compile(r"\brewrite\b")
ABSTRACT_RE = re.compile(r"^\s*abstract\s*$", re.MULTILINE)
RECORD_RE = re.compile(r"^\s*record\s+[A-Za-z0-9_']+", re.MULTILINE)
WITH_RE = re.compile(r"\bwith\b")
PUBLIC_RE = re.compile(r"\bpublic\b")
TOP_DECL_RE = re.compile(r"^[A-Za-z0-9_'.-]+\s*:\s*$", re.MULTILINE)


def module_from_path(path: Path) -> str:
    return ".".join(path.relative_to(REPO).with_suffix("").parts)


def path_from_module(module: str) -> Path:
    return REPO.joinpath(*module.split(".")).with_suffix(".agda")


def local_modules() -> Dict[str, Path]:
    out: Dict[str, Path] = {}
    for root in AGDA_ROOTS:
        if not root.exists():
            continue
        for path in root.rglob("*.agda"):
            out[module_from_path(path)] = path
    return out


@dataclass(frozen=True)
class Metrics:
    module: str
    path: str
    lines: int
    bytes: int
    imports: int
    solve: int
    subst: int
    rewrite: int
    abstract: int
    records: int
    with_count: int
    public_count: int
    top_decls: int
    local_weight: int
    transitive_modules: int = 0
    transitive_weight: int = 0
    reverse_users: int = 0
    measured_rss_mib: float = 0.0
    cut_score: float = 0.0


def static_weight(text: str) -> int:
    # Heuristic only.  `solve`, dependent transport and rewrite chains have been
    # the observed high-RSS failure modes in this cone, so weight them heavily.
    lines = text.count("\n") + 1
    return (
        lines
        + 45 * len(SOLVE_RE.findall(text))
        + 28 * len(SUBST_RE.findall(text))
        + 18 * len(REWRITE_RE.findall(text))
        + 12 * len(WITH_RE.findall(text))
        + 8 * len(RECORD_RE.findall(text))
    )


def parse_graph(modules: Mapping[str, Path]) -> Tuple[Dict[str, Set[str]], Dict[str, str]]:
    graph: Dict[str, Set[str]] = {m: set() for m in modules}
    texts: Dict[str, str] = {}
    for module, path in modules.items():
        text = path.read_text(encoding="utf-8")
        texts[module] = text
        for dep in IMPORT_RE.findall(text):
            if dep in modules:
                graph[module].add(dep)
    return graph, texts


def reachable(graph: Mapping[str, Set[str]], root: str) -> Set[str]:
    seen: Set[str] = set()
    stack = [root]
    while stack:
        node = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        stack.extend(graph.get(node, ()))
    return seen


def closure(graph: Mapping[str, Set[str]], node: str, memo: MutableMapping[str, Set[str]]) -> Set[str]:
    if node in memo:
        return memo[node]
    # Cycle-safe DFS; Agda module imports should be acyclic, but fail gently.
    result: Set[str] = {node}
    memo[node] = result
    for dep in graph.get(node, ()):
        result |= closure(graph, dep, memo)
    memo[node] = result
    return result


def reverse_graph(graph: Mapping[str, Set[str]]) -> Dict[str, Set[str]]:
    rev: Dict[str, Set[str]] = {m: set() for m in graph}
    for src, deps in graph.items():
        for dep in deps:
            rev.setdefault(dep, set()).add(src)
    return rev


def dominators(graph: Mapping[str, Set[str]], root: str, nodes: Set[str]) -> Dict[str, Set[str]]:
    """Classic iterative dominators on root -> import edges."""
    preds = reverse_graph(graph)
    dom: Dict[str, Set[str]] = {n: set(nodes) for n in nodes}
    dom[root] = {root}
    changed = True
    while changed:
        changed = False
        for n in nodes:
            if n == root:
                continue
            ps = [p for p in preds.get(n, ()) if p in nodes]
            if not ps:
                new = {n}
            else:
                inter = set(nodes)
                for p in ps:
                    inter &= dom[p]
                new = {n} | inter
            if new != dom[n]:
                dom[n] = new
                changed = True
    return dom


def parse_rss(values: Sequence[str]) -> Dict[str, float]:
    out: Dict[str, float] = {}
    for value in values:
        if "=" not in value:
            raise SystemExit(f"bad --rss value {value!r}; expected MODULE=MiB")
        module, raw = value.split("=", 1)
        out[module] = float(raw)
    return out


def build_metrics(
    graph: Mapping[str, Set[str]],
    texts: Mapping[str, str],
    modules: Mapping[str, Path],
    root: str,
    rss: Mapping[str, float],
) -> List[Metrics]:
    nodes = reachable(graph, root)
    rev = reverse_graph(graph)
    memo: Dict[str, Set[str]] = {}
    local_weights = {m: static_weight(texts[m]) for m in nodes}
    dom = dominators(graph, root, nodes)

    rows: List[Metrics] = []
    for m in nodes:
        text = texts[m]
        cone = closure(graph, m, memo) & nodes
        transitive_weight = sum(local_weights[n] for n in cone)
        measured = rss.get(m, 0.0)
        # A candidate cut is attractive when a narrow module dominates a large
        # transitive proof cone or has measured RSS.  Penalise wide local APIs
        # very mildly; this is a ranking hint, not a correctness criterion.
        api = max(1, len(TOP_DECL_RE.findall(text)))
        measured_bonus = measured * 1000.0
        score = (transitive_weight + measured_bonus) / (api ** 0.5)
        rows.append(Metrics(
            module=m,
            path=str(modules[m].relative_to(REPO)),
            lines=text.count("\n") + 1,
            bytes=len(text.encode("utf-8")),
            imports=len(graph.get(m, ())),
            solve=len(SOLVE_RE.findall(text)),
            subst=len(SUBST_RE.findall(text)),
            rewrite=len(REWRITE_RE.findall(text)),
            abstract=len(ABSTRACT_RE.findall(text)),
            records=len(RECORD_RE.findall(text)),
            with_count=len(WITH_RE.findall(text)),
            public_count=len(PUBLIC_RE.findall(text)),
            top_decls=len(TOP_DECL_RE.findall(text)),
            local_weight=local_weights[m],
            transitive_modules=len(cone),
            transitive_weight=transitive_weight,
            reverse_users=len(rev.get(m, ()) & nodes),
            measured_rss_mib=measured,
            cut_score=score,
        ))
    return sorted(rows, key=lambda x: x.cut_score, reverse=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--root",
        default="DASHI.Physics.Closure.NSTriadKNABCInhabitationRound58Exact",
        help="root Agda module",
    )
    parser.add_argument("--top", type=int, default=30)
    parser.add_argument("--rss", action="append", default=[], metavar="MODULE=MiB")
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--show-dominators",
        action="store_true",
        help="also print high-weight dominators of the root import cone",
    )
    args = parser.parse_args()

    modules = local_modules()
    if args.root not in modules:
        raise SystemExit(f"root module not found: {args.root}")
    graph, texts = parse_graph(modules)
    rss = parse_rss(args.rss)
    rows = build_metrics(graph, texts, modules, args.root, rss)

    if args.json:
        print(json.dumps({"root": args.root, "rows": [asdict(r) for r in rows]}, indent=2))
        return

    print(f"root: {args.root}")
    print(f"reachable local modules: {len(rows)}")
    print()
    header = (
        "rank  score       rssMiB  cone  weight    local  solve subst rw  users  module"
    )
    print(header)
    print("-" * len(header))
    for i, row in enumerate(rows[: args.top], 1):
        print(
            f"{i:>4}  {row.cut_score:>10.1f}  {row.measured_rss_mib:>7.1f}"
            f"  {row.transitive_modules:>4}  {row.transitive_weight:>7}"
            f"  {row.local_weight:>6}  {row.solve:>5} {row.subst:>5}"
            f" {row.rewrite:>2}  {row.reverse_users:>5}  {row.module}"
        )

    if args.show_dominators:
        nodes = reachable(graph, args.root)
        dom = dominators(graph, args.root, nodes)
        dominated_count = {
            candidate: sum(candidate in ds for ds in dom.values()) for candidate in nodes
        }
        by_module = {r.module: r for r in rows}
        ranked = sorted(
            nodes,
            key=lambda m: dominated_count[m] * by_module[m].transitive_weight,
            reverse=True,
        )
        print("\nroot-cone dominators (candidate compiled cuts):")
        for m in ranked[: args.top]:
            r = by_module[m]
            print(
                f"{dominated_count[m]:>4} dominated  cone={r.transitive_modules:>4}"
                f" weight={r.transitive_weight:>8}  {m}"
            )


if __name__ == "__main__":
    main()
