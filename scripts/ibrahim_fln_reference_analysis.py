#!/usr/bin/env python3
"""Revision-scoped reference FLN census; not an Ibrahim historical reproduction.

Method attribution: Mark Ibrahim, Christopher M. Danforth, Peter Sheridan Dodds,
"Connecting every bit of knowledge: The structure of Wikipedia's First Link
Network", Journal of Computational Science 19 (2017), 21-30.
DOI: 10.1016/j.jocs.2016.12.001.

The exact single-visit count used here is a DASHI reference definition and is
NOT claimed to equal the paper-era traversal-funnel algorithm. Its output
must not pay original parser/dump provenance or the video's modern counts.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
import hashlib
import json
from pathlib import Path
import re
from typing import Any, Mapping

METHOD_DOI = "10.1016/j.jocs.2016.12.001"
SCHEMA = "dashi.ibrahim.fln.reference_census.v1"
REQUIRED_MANIFEST = (
    "source_author", "source_title", "canonical_url", "source_role",
    "version_or_revision", "parser_policy", "link_selection_policy",
    "expected_sha256", "claim_scope", "qid_status", "dewey_status",
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def check_manifest(path: Path, data_path: Path) -> dict[str, Any]:
    manifest = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(manifest, dict):
        raise ValueError("manifest must be an object")
    for key in REQUIRED_MANIFEST:
        if not isinstance(manifest.get(key), str) or not manifest[key].strip():
            raise ValueError(f"missing manifest provenance field: {key}")
    if not re.fullmatch(r"[a-fA-F0-9]{64}", manifest["expected_sha256"]):
        raise ValueError("expected_sha256 must be a full SHA-256 digest")
    actual = sha256_file(data_path)
    if actual.lower() != manifest["expected_sha256"].lower():
        raise ValueError("input graph hash mismatch: do not infer same-object identity")
    manifest["verified_local_graph_sha256"] = actual
    return manifest


def checked_graph(payload: Any) -> dict[str, str | None]:
    if not isinstance(payload, dict):
        raise ValueError("FLN input must be a JSON object: article -> first-link or null")
    graph: dict[str, str | None] = {}
    for source, dest in payload.items():
        if not isinstance(source, str) or not source:
            raise ValueError("non-string/empty source title")
        if dest is not None and (not isinstance(dest, str) or not dest):
            raise ValueError(f"invalid destination for {source!r}")
        graph[source] = dest
    return graph


def _canonical_cycle(cycle: list[str]) -> tuple[str, ...]:
    if not cycle:
        raise ValueError("a cycle must have positive period")
    position = min(range(len(cycle)), key=lambda i: cycle[i])
    return tuple(cycle[position:] + cycle[:position])


def terminal_census(
    graph: Mapping[str, str | None],
) -> tuple[dict[str, tuple[str, tuple[str, ...]]], Counter]:
    """Iterative path compression: one terminal object per known source."""
    resolved: dict[str, tuple[str, tuple[str, ...]]] = {}
    for start in graph:
        if start in resolved:
            continue
        path: list[str] = []
        positions: dict[str, int] = {}
        current = start
        while True:
            if current in resolved:
                terminal = resolved[current]
                break
            if current not in graph:
                # An absent link target is a missing corpus node, NOT a dead end.
                terminal = ("unresolved_target", (current,))
                break
            if current in positions:
                terminal = ("cycle", _canonical_cycle(path[positions[current]:]))
                break
            positions[current] = len(path)
            path.append(current)
            dest = graph[current]
            if dest is None:
                terminal = ("dead_end", (current,))
                break
            current = dest
        for node in path:
            resolved[node] = terminal
    return resolved, Counter(resolved.values())


def single_visit_funnels(
    graph: Mapping[str, str | None],
    terminal: Mapping[str, tuple[str, tuple[str, ...]]],
    basins: Counter,
) -> dict[str, int]:
    """Counts distinct starts whose first-link orbit visits each article.

    Incoming arborescences are processed by Kahn peeling. Every cycle vertex
    receives the size of its terminal basin, counting each starting article
    once, even if the walk would otherwise loop forever.
    """
    indegree = dict.fromkeys(graph, 0)
    flow = dict.fromkeys(graph, 1)
    for target in graph.values():
        if target in indegree:
            indegree[target] += 1
    queue = deque(node for node, degree in indegree.items() if degree == 0)
    while queue:
        node = queue.popleft()
        target = graph[node]
        if target in indegree:
            flow[target] += flow[node]
            indegree[target] -= 1
            if indegree[target] == 0:
                queue.append(target)
    for node, degree in indegree.items():
        if degree > 0:
            outcome = terminal[node]
            if outcome[0] != "cycle":
                raise AssertionError("unpeeled vertex must belong to a cycle")
            flow[node] = basins[outcome]
    return flow


def reverse_edited_closure(
    graph: Mapping[str, str | None], changed: set[str],
) -> set[str]:
    predecessors: dict[str, list[str]] = defaultdict(list)
    for source, dest in graph.items():
        if dest in graph:
            predecessors[dest].append(source)
    closure = set(changed)
    queue = deque(changed)
    while queue:
        for source in predecessors[queue.popleft()]:
            if source not in closure:
                closure.add(source)
                queue.append(source)
    return closure


def compare_same_carrier(
    old: Mapping[str, str | None], new: Mapping[str, str | None],
) -> dict[str, Any]:
    if set(old) != set(new):
        raise ValueError("different page carriers require a typed identity-transport receipt")
    old_terminal, _ = terminal_census(old)
    new_terminal, _ = terminal_census(new)
    changed = {node for node in old if old[node] != new[node]}
    may_change = reverse_edited_closure(old, changed)
    actually_changed = {n for n in old if old_terminal[n] != new_terminal[n]}
    if not actually_changed <= may_change:
        raise AssertionError("revision sensitivity theorem violated")
    return {
        "edge_changes": len(changed),
        "old_reverse_reachable_bound": len(may_change),
        "actually_changed_terminal_outcomes": len(actually_changed),
        "outside_bound_unaffected": True,
        "page_identity_transport_required": False,
        "mathematical_scope": "same source node carrier and exact equality of destinations",
    }


def summarise(graph: Mapping[str, str | None], *, top: int) -> dict[str, Any]:
    terminal, basins = terminal_census(graph)
    flows = single_visit_funnels(graph, terminal, basins)
    if len(terminal) != len(graph) or sum(basins.values()) != len(graph):
        raise AssertionError("terminal partition was not exhaustive")
    ordered_basins = sorted(
        basins.items(), key=lambda x: (-x[1], x[0][0], x[0][1])
    )
    return {
        "article_count": len(graph),
        "cycle_count": sum(kind == "cycle" for (kind, _), _ in basins.items()),
        "dead_end_count": sum(kind == "dead_end" for (kind, _), _ in basins.items()),
        "unresolved_target_count": sum(
            kind == "unresolved_target" for (kind, _), _ in basins.items()
        ),
        "basins": [
            {
                "kind": outcome[0], "terminal_nodes": list(outcome[1]),
                "starting_articles": size, "exact_share": f"{size}/{len(graph)}",
            }
            for outcome, size in ordered_basins[:top]
        ],
        "top_single_visit_funnels": [
            {"article": node, "distinct_starts_visiting": amount}
            for node, amount in sorted(flows.items(), key=lambda x: (-x[1], x[0]))[:top]
        ],
        "counting_rule": "one visit per starting article per target vertex",
        "historical_traversal_funnel_algorithm_parity_paid": False,
        "corpus_to_historical_dump_identity_paid": False,
        "wikipedia_parser_equivalence_paid": False,
        "wikidata_alignment_or_semantic_truth_paid": False,
        "cultural_causality_paid": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--compare", type=Path)
    parser.add_argument("--compare-manifest", type=Path)
    parser.add_argument("--top", type=int, default=20)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.top < 1:
        parser.error("--top must be positive")
    if bool(args.compare) != bool(args.compare_manifest):
        parser.error("--compare and --compare-manifest must be supplied together")
    source = check_manifest(args.manifest, args.input)
    graph = checked_graph(json.loads(args.input.read_text(encoding="utf-8")))
    report: dict[str, Any] = {
        "schema": SCHEMA,
        "method_source_doi": METHOD_DOI,
        "method_role": "source calibration, not algorithm-equivalence certification",
        "reference_executable_sha256": sha256_file(Path(__file__)),
        "input_attribution": source,
        "result": summarise(graph, top=args.top),
    }
    if args.compare:
        other_source = check_manifest(args.compare_manifest, args.compare)
        newer = checked_graph(json.loads(args.compare.read_text(encoding="utf-8")))
        report["other_attribution"] = other_source
        report["revision_comparison"] = compare_same_carrier(graph, newer)
    result = json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2)
    if args.output:
        args.output.write_text(result + "\n", encoding="utf-8")
    else:
        print(result)


if __name__ == "__main__":
    main()
