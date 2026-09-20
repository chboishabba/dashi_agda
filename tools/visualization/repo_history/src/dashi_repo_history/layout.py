from __future__ import annotations

from dataclasses import dataclass
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


class PersistentLayout:
    """Preserve the viewer's mental map while admitting new graph structure.

    The semantic graph owns identity.  Layout only supplies positions.  Existing
    nodes are biased toward their previous positions; new nodes begin near the
    centroid of already-positioned neighbours before a bounded spring solve.
    """

    def __init__(self, config: LayoutConfig | None = None) -> None:
        self.config = config or LayoutConfig()
        self.positions: dict[str, Point] = {}

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

        raw = nx.spring_layout(
            graph,
            pos=initial or None,
            seed=self.config.seed,
            iterations=self.config.iterations,
            scale=1.0,
        )

        weight = self.config.old_position_weight
        solved: dict[str, Point] = {}
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
