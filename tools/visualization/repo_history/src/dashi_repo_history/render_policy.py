from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from manim import DOWN, Dot, Text, VGroup


@dataclass(frozen=True)
class AnimationPolicy:
    commit_node_seconds: float = 0.08
    commit_edge_seconds: float = 0.08
    semantic_step_seconds: float = 0.35
    semantic_highlight_seconds: float = 0.08
    merge_seconds: float = 1.6


@dataclass(frozen=True)
class LabelPolicy:
    label_all_below: int = 70
    label_top_level_below: int = 220
    font_size: int = 10
    binder_font_size: int = 8

    def show_label(self, node: dict[str, Any], total_nodes: int) -> bool:
        if total_nodes <= self.label_all_below:
            return True
        if node.get("kind") == "binder":
            return False
        return total_nodes <= self.label_top_level_below


@dataclass(frozen=True)
class NodePolicy:
    module_radius: float = 0.085
    binder_radius: float = 0.035
    default_radius: float = 0.055

    def radius(self, node: dict[str, Any]) -> float:
        kind = node.get("kind")
        if kind == "module":
            return self.module_radius
        if kind == "binder":
            return self.binder_radius
        return self.default_radius


@dataclass(frozen=True)
class ManimRenderPolicy:
    animation: AnimationPolicy = AnimationPolicy()
    labels: LabelPolicy = LabelPolicy()
    nodes: NodePolicy = NodePolicy()

    def vertex_mobject(
        self,
        node: dict[str, Any],
        *,
        total_nodes: int,
    ):
        dot = Dot(radius=self.nodes.radius(node))
        if not self.labels.show_label(node, total_nodes):
            return dot

        font_size = (
            self.labels.binder_font_size
            if node.get("kind") == "binder"
            else self.labels.font_size
        )
        label = Text(
            str(node.get("label", "")),
            font_size=font_size,
        ).next_to(dot, DOWN, buff=0.025)
        return VGroup(dot, label)
