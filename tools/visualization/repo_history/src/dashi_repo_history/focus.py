from __future__ import annotations

from dataclasses import dataclass
from typing import Any


DEFAULT_SEMANTIC_RELATIONS = frozenset(
    {
        "type-depends",
        "body-depends",
        "value-flows",
        "argument-to",
        "calls",
        "constructs",
        "binds",
        "pattern-matches",
        "local-to",
        "field-of",
        "constructor-of",
        "instantiates",
        "rewrites-with",
        "depends",
    }
)


@dataclass(frozen=True)
class FocusLayer:
    direction: str
    depth: int
    node_ids: tuple[str, ...]


@dataclass(frozen=True)
class FocusResult:
    root_id: str
    node_ids: frozenset[str]
    edge_ids: frozenset[str]
    layers: tuple[tuple[str, ...], ...]
    layer_specs: tuple[FocusLayer, ...]

    def graph(self, graph_data: dict[str, Any]) -> dict[str, Any]:
        return {
            "nodes": [
                node
                for node in graph_data.get("nodes", [])
                if node["symbol_id"] in self.node_ids
            ],
            "edges": [
                edge
                for edge in graph_data.get("edges", [])
                if edge["relation_id"] in self.edge_ids
                and edge["source"] in self.node_ids
                and edge["target"] in self.node_ids
            ],
        }


def resolve_symbol(
    graph_data: dict[str, Any],
    selector: str,
) -> dict[str, Any]:
    by_id = {
        node["symbol_id"]: node
        for node in graph_data.get("nodes", [])
    }
    if selector in by_id:
        return by_id[selector]

    if "::" in selector:
        module, label = selector.rsplit("::", 1)
        qualified = [
            node
            for node in graph_data.get("nodes", [])
            if node.get("module") == module
            and node.get("label") == label
        ]
        if len(qualified) == 1:
            return qualified[0]
        if not qualified:
            raise KeyError(
                f"no semantic symbol matches {selector!r}"
            )
        candidates = ", ".join(
            f"{node.get('module')}::{node.get('label')}"
            f"[{node.get('symbol_id')[:8]}]"
            for node in qualified[:12]
        )
        raise ValueError(
            f"ambiguous scoped semantic symbol {selector!r}: "
            f"{candidates}"
        )

    exact = [
        node
        for node in graph_data.get("nodes", [])
        if node.get("label") == selector
    ]
    if len(exact) == 1:
        return exact[0]
    if not exact:
        raise KeyError(f"no semantic symbol matches {selector!r}")

    candidates = ", ".join(
        f"{node.get('module')}::{node.get('label')}[{node.get('symbol_id')[:8]}]"
        for node in exact[:12]
    )
    raise ValueError(
        f"ambiguous semantic symbol {selector!r}: {candidates}"
    )


def focus_symbol(
    graph_data: dict[str, Any],
    selector: str,
    *,
    upstream_depth: int = 2,
    downstream_depth: int = 0,
    relation_kinds: frozenset[str] = DEFAULT_SEMANTIC_RELATIONS,
) -> FocusResult:
    root = resolve_symbol(graph_data, selector)
    root_id = root["symbol_id"]

    edges = [
        edge
        for edge in graph_data.get("edges", [])
        if edge.get("kind") in relation_kinds
    ]
    incoming: dict[str, list[dict[str, Any]]] = {}
    outgoing: dict[str, list[dict[str, Any]]] = {}
    for edge in edges:
        incoming.setdefault(edge["target"], []).append(edge)
        outgoing.setdefault(edge["source"], []).append(edge)

    node_ids = {root_id}
    edge_ids: set[str] = set()
    layer_map: dict[int, set[str]] = {0: {root_id}}

    def walk(
        *,
        adjacency: dict[str, list[dict[str, Any]]],
        next_node_key: str,
        max_depth: int,
        direction_sign: int,
    ) -> None:
        frontier = {root_id}
        visited_at: dict[str, int] = {root_id: 0}

        for depth in range(1, max_depth + 1):
            next_frontier: set[str] = set()
            for current in frontier:
                for edge in adjacency.get(current, []):
                    other = edge[next_node_key]
                    edge_ids.add(edge["relation_id"])
                    node_ids.add(other)
                    signed_depth = direction_sign * depth
                    layer_map.setdefault(signed_depth, set()).add(other)

                    old_depth = visited_at.get(other)
                    if old_depth is None or depth < old_depth:
                        visited_at[other] = depth
                        next_frontier.add(other)
            frontier = next_frontier
            if not frontier:
                break

    walk(
        adjacency=incoming,
        next_node_key="source",
        max_depth=max(0, upstream_depth),
        direction_sign=-1,
    )
    walk(
        adjacency=outgoing,
        next_node_key="target",
        max_depth=max(0, downstream_depth),
        direction_sign=1,
    )

    # Keep all semantic relations among selected nodes, not only traversal-tree
    # edges. This exposes cross-links without expanding the node set.
    for edge in edges:
        if edge["source"] in node_ids and edge["target"] in node_ids:
            edge_ids.add(edge["relation_id"])

    ordered_depths = [0]
    ordered_depths.extend(
        depth
        for depth in range(-1, -upstream_depth - 1, -1)
        if depth in layer_map
    )
    ordered_depths.extend(
        depth
        for depth in range(1, downstream_depth + 1)
        if depth in layer_map
    )
    layers = tuple(
        tuple(sorted(layer_map[depth]))
        for depth in ordered_depths
    )
    layer_specs = tuple(
        FocusLayer(
            direction=(
                "root"
                if depth == 0
                else "upstream"
                if depth < 0
                else "downstream"
            ),
            depth=abs(depth),
            node_ids=tuple(sorted(layer_map[depth])),
        )
        for depth in ordered_depths
    )

    return FocusResult(
        root_id=root_id,
        node_ids=frozenset(node_ids),
        edge_ids=frozenset(edge_ids),
        layers=layers,
        layer_specs=layer_specs,
    )
