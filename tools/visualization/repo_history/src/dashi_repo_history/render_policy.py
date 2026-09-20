from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from manim import DOWN, LEFT, Dot, Text, VGroup


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
class EdgePolicy:
    """Visual-only priority for semantic relation classes."""

    priority: tuple[str, ...] = (
        "constructs",
        "calls",
        "pattern-matches",
        "constructor-of",
        "field-of",
        "argument-to",
        "value-flows",
        "binds",
        "body-depends",
        "type-depends",
        "opens",
        "imports",
        "contains",
        "depends",
    )

    stroke_widths: tuple[tuple[str, float], ...] = (
        ("constructs", 4.0),
        ("calls", 3.2),
        ("pattern-matches", 2.8),
        ("constructor-of", 2.6),
        ("field-of", 2.4),
        ("argument-to", 2.5),
        ("value-flows", 2.2),
        ("binds", 1.9),
        ("body-depends", 1.7),
        ("type-depends", 1.25),
        ("opens", 1.05),
        ("imports", 0.9),
        ("contains", 0.75),
        ("depends", 1.0),
    )

    def dominant_kind(self, kinds: set[str]) -> str:
        for kind in self.priority:
            if kind in kinds:
                return kind
        return "depends"

    def stroke_width(self, kinds: set[str]) -> float:
        dominant = self.dominant_kind(kinds)
        return dict(self.stroke_widths).get(dominant, 1.0)

    def legend_entries(self, present_kinds: set[str]) -> list[tuple[str, float]]:
        entries: list[tuple[str, float]] = []
        for kind in self.priority:
            if kind in present_kinds:
                entries.append((kind, self.stroke_width({kind})))
        return entries

    def edge_config(self, kinds: set[str]) -> dict[str, Any]:
        dominant = self.dominant_kind(kinds)
        width = self.stroke_width(kinds)
        tip_length = 0.16
        if dominant in {"constructs", "calls"}:
            tip_length = 0.22
        elif dominant in {"contains", "imports", "opens"}:
            tip_length = 0.11
        return {
            "stroke_width": width,
            "tip_config": {"tip_length": tip_length},
        }


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
    edges: EdgePolicy = EdgePolicy()

    def legend_mobject(self, present_kinds: set[str]):
        entries = self.edges.legend_entries(present_kinds)
        if not entries:
            return VGroup()
        rows = [
            Text(
                f"{'━' * max(1, round(width))}  {kind}",
                font_size=11,
            )
            for kind, width in entries
        ]
        return VGroup(*rows).arrange(
            DOWN,
            aligned_edge=LEFT,
            buff=0.035,
        )

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
