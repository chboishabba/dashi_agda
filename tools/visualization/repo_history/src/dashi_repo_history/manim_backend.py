from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

import networkx as nx
from manim import (
    Create,
    DiGraph,
    Dot,
    FadeIn,
    FadeOut,
    GrowFromCenter,
    Indicate,
    MovingCameraScene,
    ReplacementTransform,
    Text,
    UP,
    VGroup,
)

from .layout import PersistentLayout
from .merge_attribution import attribute_merge


def _history_layout(commits: list[dict[str, Any]]) -> dict[str, list[float]]:
    """Deterministic left-to-right lane layout preserving forks and merges."""

    children: dict[str, list[str]] = {}
    by_sha = {c["commit"]: c for c in commits}
    for commit in commits:
        for parent in commit["parents"]:
            if parent in by_sha:
                children.setdefault(parent, []).append(commit["commit"])

    lane: dict[str, int] = {}
    next_lane = 1
    positions: dict[str, list[float]] = {}

    for index, commit in enumerate(commits):
        sha = commit["commit"]
        parents = [p for p in commit["parents"] if p in lane]
        if not parents:
            current_lane = 0
        else:
            primary = parents[0]
            current_lane = lane[primary]

            siblings = children.get(primary, [])
            if len(siblings) > 1 and siblings.index(sha) > 0:
                current_lane = next_lane
                next_lane += 1

            # Merge nodes return to the first-parent lane.  The other parent
            # edges visibly converge onto that lane.
            if len(parents) > 1:
                current_lane = lane[parents[0]]

        lane[sha] = current_lane
        positions[sha] = [index * 0.55, -current_lane * 0.75, 0.0]

    if positions:
        xs = [p[0] for p in positions.values()]
        centre = (min(xs) + max(xs)) / 2
        for value in positions.values():
            value[0] -= centre

    return positions


def _visual_edges(graph_data: dict[str, Any]) -> list[tuple[str, str]]:
    """Project typed semantic relations to Manim's simple DiGraph edge set.

    The semantic JSON retains every relation_id/kind.  Manim DiGraph is simple
    rather than multi-edge, so only the geometric source/target pair is
    projected here; no semantic relation is deleted from the authority data.
    """

    return sorted(
        {
            (edge["source"], edge["target"])
            for edge in graph_data["edges"]
            if edge["source"] != edge["target"]
        }
    )


def _snapshot_maps(data: dict[str, Any]):
    snapshots = {
        snapshot["commit"]: snapshot
        for snapshot in data.get("snapshots", [])
    }
    commits = {
        commit["commit"]: commit
        for commit in data.get("commits", [])
    }
    return commits, snapshots


class HistoryGraphView:
    def __init__(self, commits: list[dict[str, Any]]) -> None:
        self.commits = commits
        self.positions = _history_layout(commits)
        self.graph = DiGraph([], [], layout={})

    def add_commit(self, scene: MovingCameraScene, commit: dict[str, Any]) -> None:
        sha = commit["commit"]
        position = self.positions[sha]
        shape = commit.get("shape", "linear")

        vertex_mobject = Dot(radius=0.055 if shape != "merge" else 0.08)
        added = self.graph.add_vertices(
            sha,
            positions={sha: position},
            vertex_mobjects={sha: vertex_mobject},
        )
        scene.play(GrowFromCenter(added), run_time=0.08)

        for parent in commit["parents"]:
            if parent not in self.graph.vertices:
                continue
            edge = self.graph.add_edges((parent, sha))
            scene.play(Create(edge), run_time=0.08)

        if commit.get("refs"):
            label = Text(
                " · ".join(commit["refs"]),
                font_size=15,
            ).next_to(self.graph.vertices[sha], UP, buff=0.08)
            scene.play(FadeIn(label), run_time=0.12)


class SemanticGraphView:
    """Manim adapter for renderer-neutral semantic graphs."""

    def __init__(self) -> None:
        self.layout = PersistentLayout()
        self.graph = DiGraph([], [], layout={})
        self.current_nodes: set[str] = set()
        self.current_edges: set[tuple[str, str]] = set()

    def build(self, graph_data: dict[str, Any]) -> DiGraph:
        nodes = [n["symbol_id"] for n in graph_data["nodes"]]
        edges = _visual_edges(graph_data)
        self.layout.solve(nodes, edges)
        self.graph = DiGraph(
            nodes,
            edges,
            layout=self.layout.manim_layout(),
        )
        self.current_nodes = set(nodes)
        self.current_edges = set(edges)
        return self.graph

    def apply_snapshot(
        self,
        scene: MovingCameraScene,
        graph_data: dict[str, Any],
        *,
        run_time: float = 0.35,
    ) -> None:
        target_nodes = {n["symbol_id"] for n in graph_data["nodes"]}
        target_edges = set(_visual_edges(graph_data))

        removed_edges = sorted(self.current_edges - target_edges)
        removed_nodes = sorted(self.current_nodes - target_nodes)
        added_nodes = sorted(target_nodes - self.current_nodes)
        added_edges = sorted(target_edges - self.current_edges)

        edge_fades = [
            FadeOut(self.graph.edges[edge])
            for edge in removed_edges
            if edge in self.graph.edges
        ]
        if edge_fades:
            scene.play(*edge_fades, run_time=run_time / 2)
        if removed_edges:
            self.graph.remove_edges(*removed_edges)

        node_fades = [
            FadeOut(self.graph.vertices[node])
            for node in removed_nodes
            if node in self.graph.vertices
        ]
        if node_fades:
            scene.play(*node_fades, run_time=run_time / 2)
        if removed_nodes:
            self.graph.remove_vertices(*removed_nodes)

        self.layout.solve(target_nodes, target_edges)
        target_layout = self.layout.manim_layout()

        if added_nodes:
            new_vertices = self.graph.add_vertices(
                *added_nodes,
                positions={node: target_layout[node] for node in added_nodes},
            )
            scene.play(GrowFromCenter(new_vertices), run_time=run_time)

        if added_edges:
            new_edges = self.graph.add_edges(*added_edges)
            scene.play(Create(new_edges), run_time=run_time)

        if target_nodes:
            scene.play(
                self.graph.animate.change_layout(target_layout),
                run_time=run_time,
            )

        for node in added_nodes[:12]:
            if node in self.graph.vertices:
                scene.play(
                    Indicate(self.graph.vertices[node], scale_factor=1.35),
                    run_time=0.08,
                )

        self.current_nodes = target_nodes
        self.current_edges = target_edges


def _changed_graph(
    snapshot: dict[str, Any],
    node_ids: set[str],
    edge_ids: set[str],
) -> dict[str, Any]:
    edges_by_id = {
        edge["relation_id"]: edge
        for edge in snapshot["graph"]["edges"]
    }

    selected_edges = [
        edges_by_id[edge_id]
        for edge_id in edge_ids
        if edge_id in edges_by_id
    ]

    expanded_nodes = set(node_ids)
    for edge in selected_edges:
        expanded_nodes.add(edge["source"])
        expanded_nodes.add(edge["target"])

    selected_nodes = [
        node
        for node in snapshot["graph"]["nodes"]
        if node["symbol_id"] in expanded_nodes
    ]
    return {
        "nodes": selected_nodes,
        "edges": selected_edges,
    }


class RepositoryHistoryScene(MovingCameraScene):
    """Animate branch/fork/merge topology derived directly from Git parents."""

    def construct(self) -> None:
        path = os.environ.get("DASHI_REPO_HISTORY_JSON")
        if not path:
            self.add(Text("Set DASHI_REPO_HISTORY_JSON", font_size=28))
            return

        data = json.loads(Path(path).read_text(encoding="utf-8"))
        commits = data["commits"]

        title = Text(
            "dashi_agda — branch / merge evolution",
            font_size=30,
        ).to_edge(UP)
        self.play(FadeIn(title))

        history = HistoryGraphView(commits)
        self.add(history.graph)

        for commit in commits:
            history.add_commit(self, commit)

        if commits and history.graph.width > 0:
            self.play(
                self.camera.frame.animate.move_to(history.graph).set(
                    width=max(12, history.graph.width + 1.5)
                ),
                run_time=1.0,
            )
        self.wait(2)


class SemanticSnapshotScene(MovingCameraScene):
    """Render one Tree-sitter-derived semantic symbol graph."""

    def construct(self) -> None:
        path = os.environ.get("DASHI_REPO_HISTORY_JSON")
        snapshot_index = int(os.environ.get("DASHI_REPO_SNAPSHOT_INDEX", "-1"))
        if not path:
            self.add(Text("Set DASHI_REPO_HISTORY_JSON", font_size=28))
            return

        data = json.loads(Path(path).read_text(encoding="utf-8"))
        snapshots = data.get("snapshots", [])
        if not snapshots:
            self.add(Text("No semantic snapshots", font_size=28))
            return

        snapshot = snapshots[snapshot_index]
        graph = SemanticGraphView().build(snapshot["graph"])
        title = Text(
            f"semantic graph · {snapshot['commit'][:10]}",
            font_size=28,
        ).to_edge(UP)
        self.play(FadeIn(title), Create(graph), run_time=2.0)
        if graph.width > 0:
            self.play(
                self.camera.frame.animate.move_to(graph).set(
                    width=max(12, graph.width + 1.5)
                ),
                run_time=1.0,
            )
        self.wait(2)


class SemanticHistoryScene(MovingCameraScene):
    """Incrementally animate semantic snapshots with persistent layout."""

    def construct(self) -> None:
        path = os.environ.get("DASHI_REPO_HISTORY_JSON")
        if not path:
            self.add(Text("Set DASHI_REPO_HISTORY_JSON", font_size=28))
            return

        data = json.loads(Path(path).read_text(encoding="utf-8"))
        snapshots = data.get("snapshots", [])
        if not snapshots:
            self.add(Text("No semantic snapshots", font_size=28))
            return

        title = Text(
            "dashi_agda — semantic evolution",
            font_size=30,
        ).to_edge(UP)
        stamp = Text("", font_size=17).next_to(title, UP * -1, buff=0.12)
        self.play(FadeIn(title), FadeIn(stamp))

        view = SemanticGraphView()
        first = snapshots[0]
        graph = view.build(first["graph"])
        self.add(graph)

        first_stamp = Text(
            first["commit"][:10],
            font_size=17,
        ).next_to(title, UP * -1, buff=0.12)
        self.play(ReplacementTransform(stamp, first_stamp), Create(graph), run_time=1.0)
        stamp = first_stamp

        for snapshot in snapshots[1:]:
            new_stamp = Text(
                snapshot["commit"][:10],
                font_size=17,
            ).next_to(title, UP * -1, buff=0.12)
            self.play(ReplacementTransform(stamp, new_stamp), run_time=0.12)
            stamp = new_stamp
            view.apply_snapshot(self, snapshot["graph"])

        self.wait(2)


class SemanticMergeScene(MovingCameraScene):
    """Show actual parent semantic contributions converging at a Git merge."""

    def construct(self) -> None:
        path = os.environ.get("DASHI_REPO_HISTORY_JSON")
        merge_index = int(os.environ.get("DASHI_REPO_MERGE_INDEX", "0"))
        if not path:
            self.add(Text("Set DASHI_REPO_HISTORY_JSON", font_size=28))
            return

        data = json.loads(Path(path).read_text(encoding="utf-8"))
        commits, snapshots = _snapshot_maps(data)
        merge_commits = [
            commit
            for commit in data.get("commits", [])
            if len(commit.get("parents", [])) >= 2
            and commit["commit"] in snapshots
            and all(parent in snapshots for parent in commit["parents"][:2])
        ]
        if not merge_commits:
            self.add(Text("No merge with semantic parent snapshots", font_size=26))
            return

        merge_commit = merge_commits[merge_index]
        attribution = attribute_merge(
            merge_commit=merge_commit,
            snapshots_by_commit=snapshots,
        )
        left, right = attribution.parents[:2]
        merge_sha = attribution.merge_commit

        changed_nodes = (
            set(attribution.parent_only_nodes[left])
            | set(attribution.parent_only_nodes[right])
            | set(attribution.introduced_nodes)
            | set(attribution.removed_nodes[left])
            | set(attribution.removed_nodes[right])
        )
        changed_edges = (
            set(attribution.parent_only_edges[left])
            | set(attribution.parent_only_edges[right])
            | set(attribution.introduced_edges)
            | set(attribution.removed_edges[left])
            | set(attribution.removed_edges[right])
        )

        left_data = _changed_graph(snapshots[left], changed_nodes, changed_edges)
        right_data = _changed_graph(snapshots[right], changed_nodes, changed_edges)
        merge_data = _changed_graph(snapshots[merge_sha], changed_nodes, changed_edges)

        left_graph = SemanticGraphView().build(left_data)
        right_graph = SemanticGraphView().build(right_data)
        merged_graph = SemanticGraphView().build(merge_data)

        left_group = VGroup(
            Text(f"parent A · {left[:9]}", font_size=18),
            left_graph,
        ).arrange(UP * -1, buff=0.2)
        right_group = VGroup(
            Text(f"parent B · {right[:9]}", font_size=18),
            right_graph,
        ).arrange(UP * -1, buff=0.2)
        parents = VGroup(left_group, right_group).arrange(buff=1.0)
        parents.scale_to_fit_width(12.0)

        title = Text(
            f"semantic merge · {merge_sha[:10]}",
            font_size=30,
        ).to_edge(UP)
        self.play(FadeIn(title), FadeIn(parents), run_time=1.0)

        merged_group = VGroup(
            Text(
                "merged semantic graph"
                f"   +{len(attribution.introduced_nodes)} merge-only nodes",
                font_size=18,
            ),
            merged_graph,
        ).arrange(UP * -1, buff=0.2)
        merged_group.scale_to_fit_width(11.0)

        self.play(
            ReplacementTransform(parents, merged_group),
            run_time=1.6,
        )
        self.wait(2)
