from __future__ import annotations

from dataclasses import dataclass
from math import ceil, sqrt
from typing import Iterable

import networkx as nx


Point = tuple[float, float]


@dataclass(frozen=True)
class LayoutConfig:
    seed: int = 17
    iterations: int = 80
    old_position_weight: float = 0.82
    scale_x: float = 5.4
    scale_y: float = 3.0
    spring_node_limit: int = 180
    spring_edge_limit: int = 600


class PersistentLayout:
    """Preserve the viewer's mental map while admitting new graph structure.

    The semantic graph owns identity.  Layout only supplies positions.  Existing
    nodes are biased toward their previous positions; new nodes begin near the
    centroid of already-positioned neighbours before a bounded spring solve.
    """

    def __init__(self, config: LayoutConfig | None = None) -> None:
        self.config = config or LayoutConfig()
        self.positions: dict[str, Point] = {}

    def transfer_identity(self, old_id: str, new_id: str) -> None:
        """Seed a supported refactor successor at the predecessor's position."""

        if old_id in self.positions and new_id not in self.positions:
            self.positions[new_id] = self.positions[old_id]

    def _bounded_large_layout(
        self,
        graph: nx.DiGraph,
        nodes: list[str],
        previous: dict[str, Point],
    ) -> dict[str, Point]:
        """Deterministic fallback that avoids force-layout blowups."""

        solved: dict[str, Point] = dict(previous)
        new_nodes = [node for node in sorted(nodes) if node not in solved]

        # Precompute adjacency once so placement stays O(V + E) apart from
        # small deterministic sorting costs.
        neighbours: dict[str, list[str]] = {}
        for node in nodes:
            neighbours[node] = sorted(
                set(graph.predecessors(node))
                | set(graph.successors(node))
            )

        # First pass: anchor new nodes near already-positioned semantic context.
        deferred: list[str] = []
        for index, node in enumerate(new_nodes):
            anchored = [
                other
                for other in neighbours[node]
                if other in solved
            ]
            if not anchored:
                deferred.append(node)
                continue

            x = sum(solved[other][0] for other in anchored) / len(anchored)
            y = sum(solved[other][1] for other in anchored) / len(anchored)

            # Tiny deterministic offset prevents exact overlap when several
            # new nodes share the same anchor centroid.
            offset = ((index % 7) - 3) * 0.025
            solved[node] = (x + offset, y - offset)

        # Remaining components have no anchor in the existing mental map.
        # Place them on a normalized deterministic grid instead of invoking an
        # expensive force solve.
        count = len(deferred)
        if count:
            columns = max(1, ceil(sqrt(count)))
            rows = max(1, ceil(count / columns))

            for index, node in enumerate(deferred):
                col = index % columns
                row = index // columns
                x = (
                    0.0
                    if columns == 1
                    else -1.0 + 2.0 * col / (columns - 1)
                )
                y = (
                    0.0
                    if rows == 1
                    else 1.0 - 2.0 * row / (rows - 1)
                )
                solved[node] = (x, y)

        return solved

    def solve(
        self,
        nodes: Iterable[str],
        edges: Iterable[tuple[str, str]],
    ) -> dict[str, Point]:
        nodes = list(dict.fromkeys(nodes))
        graph = nx.DiGraph()
        graph.add_nodes_from(nodes)
        graph.add_edges_from(edges)

        if not nodes:
            self.positions = {}
            return {}

        previous = {n: self.positions[n] for n in nodes if n in self.positions}
        initial: dict[str, Point] = dict(previous)

        for node in nodes:
            if node in initial:
                continue
            neighbours = [
                other
                for other in set(graph.predecessors(node)) | set(graph.successors(node))
                if other in initial
            ]
            if neighbours:
                x = sum(initial[n][0] for n in neighbours) / len(neighbours)
                y = sum(initial[n][1] for n in neighbours) / len(neighbours)
                initial[node] = (x, y)

        if (
            len(nodes) > self.config.spring_node_limit
            or graph.number_of_edges() > self.config.spring_edge_limit
        ):
            solved = self._bounded_large_layout(
                graph,
                nodes,
                previous,
            )
        else:
            raw = nx.spring_layout(
                graph,
                pos=initial or None,
                seed=self.config.seed,
                iterations=self.config.iterations,
                scale=1.0,
            )

            weight = self.config.old_position_weight
            solved = {}
            for node in nodes:
                x, y = float(raw[node][0]), float(raw[node][1])
                if node in previous:
                    px, py = previous[node]
                    x = weight * px + (1.0 - weight) * x
                    y = weight * py + (1.0 - weight) * y
                solved[node] = (x, y)

        self.positions = solved
        return solved

    def manim_layout(self) -> dict[str, list[float]]:
        return {
            node: [
                point[0] * self.config.scale_x,
                point[1] * self.config.scale_y,
                0.0,
            ]
            for node, point in self.positions.items()
        }
