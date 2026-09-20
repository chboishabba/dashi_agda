from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

import networkx as nx
from manim import Create, DiGraph, Dot, FadeIn, GrowFromCenter, MovingCameraScene, Text, UP


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
    """Manim adapter for the renderer-neutral semantic graph."""

    def build(
        self,
        graph_data: dict[str, Any],
        *,
        seed: int = 17,
    ) -> DiGraph:
        nodes = [n["symbol_id"] for n in graph_data["nodes"]]
        edges = [(e["source"], e["target"]) for e in graph_data["edges"]]
        nx_graph = nx.DiGraph()
        nx_graph.add_nodes_from(nodes)
        nx_graph.add_edges_from(edges)
        raw_layout = nx.spring_layout(nx_graph, seed=seed)
        layout = {
            node: [float(x) * 5.4, float(y) * 3.0, 0.0]
            for node, (x, y) in raw_layout.items()
        }
        return DiGraph(nodes, edges, layout=layout)


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
