from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterable

from .layout import PersistentLayout
from .research_film import ProgrammeRegion, programme_key


Point3 = list[float]


@dataclass
class ResearchAtlasLayout:
    """Persistent semantic geometry partitioned into research territories."""

    regions: dict[str, ProgrammeRegion]

    def __post_init__(self) -> None:
        self.local_layouts: dict[str, PersistentLayout] = {}
        self.node_programmes: dict[str, str] = {}
        self.positions: dict[str, Point3] = {}

    def _layout_for(self, programme: str) -> PersistentLayout:
        if programme not in self.local_layouts:
            self.local_layouts[programme] = PersistentLayout()
        return self.local_layouts[programme]

    def solve(
        self,
        graph_data: dict[str, Any],
    ) -> dict[str, Point3]:
        nodes = {
            node["symbol_id"]: node
            for node in graph_data.get("nodes", [])
        }
        edges = [
            (edge["source"], edge["target"])
            for edge in graph_data.get("edges", [])
            if edge["source"] != edge["target"]
        ]

        programme_nodes: dict[str, list[str]] = {}
        for node_id, node in nodes.items():
            programme = programme_key(
                str(node.get("module", "")),
                str(node.get("label", "")),
            )
            self.node_programmes[node_id] = programme
            programme_nodes.setdefault(programme, []).append(node_id)

        edge_set = set(edges)
        solved: dict[str, Point3] = {}
        for programme, node_ids in sorted(programme_nodes.items()):
            node_set = set(node_ids)
            local_edges = [
                edge
                for edge in edge_set
                if edge[0] in node_set and edge[1] in node_set
            ]
            local = self._layout_for(programme)
            local.solve(node_ids, local_edges)
            local_positions = local.manim_layout()

            region = self.regions.get(programme)
            offset_x = region.x if region else 0.0
            offset_y = region.y if region else 0.0
            for node_id, position in local_positions.items():
                solved[node_id] = [
                    position[0] + offset_x,
                    position[1] + offset_y,
                    position[2],
                ]

        self.positions = solved
        return dict(solved)

    def transfer_identity(
        self,
        old_id: str,
        new_id: str,
    ) -> None:
        programme = self.node_programmes.get(old_id)
        if programme is None:
            return
        local = self.local_layouts.get(programme)
        if local is not None:
            local.transfer_identity(old_id, new_id)
        if old_id in self.positions and new_id not in self.positions:
            self.positions[new_id] = list(self.positions[old_id])

    def focus_positions(
        self,
        node_ids: Iterable[str],
    ) -> list[Point3]:
        return [
            self.positions[node_id]
            for node_id in node_ids
            if node_id in self.positions
        ]
