from __future__ import annotations

import json
from math import hypot
import os
from pathlib import Path
from typing import Any

import networkx as nx
from manim import (
    Create,
    DiGraph,
    Dot,
    DOWN,
    LEFT,
    RIGHT,
    FadeIn,
    FadeOut,
    GrowFromCenter,
    Indicate,
    Line,
    MovingCameraScene,
    ReplacementTransform,
    Text,
    TransformFromCopy,
    UP,
    VGroup,
)

from dashi_repo_history.compact_history import load_history_file
from dashi_repo_history.history_axis import format_timestamp_date, temporal_history_layout
from dashi_repo_history.identity import supported_transfers
from dashi_repo_history.layout import PersistentLayout
from dashi_repo_history.merge_attribution import attribute_merge
from dashi_repo_history.render_policy import ManimRenderPolicy
from dashi_repo_history.research_film import compile_research_film
from dashi_repo_history.research_layout import ResearchAtlasLayout
from dashi_repo_history.scene_program import (
    compile_branch_episode_program,
    compile_first_parent_program,
    compile_merge_episode_program,
    compile_symbol_focus_program,
    compile_temporal_symbol_program,
)


def _history_axis_mobject(layout_data):
    if not layout_data.positions or not layout_data.ticks:
        return VGroup()

    xs = [position[0] for position in layout_data.positions.values()]
    axis_x = min(xs) - 1.15
    ys = [tick.y for tick in layout_data.ticks]
    axis = Line(
        [axis_x, min(ys), 0.0],
        [axis_x, max(ys), 0.0],
    )

    parts = [axis]
    for tick in layout_data.ticks:
        mark = Line(
            [axis_x - 0.08, tick.y, 0.0],
            [axis_x + 0.08, tick.y, 0.0],
        )
        label = Text(
            tick.label,
            font_size=13,
        ).next_to(mark, LEFT, buff=0.08)
        parts.extend([mark, label])

    caption = Text(
        "date (UTC)",
        font_size=13,
    ).next_to(axis, UP, buff=0.12)
    parts.append(caption)
    return VGroup(*parts)


def _visual_edge_projection(
    graph_data: dict[str, Any],
) -> tuple[
    list[tuple[str, str]],
    dict[tuple[str, str], set[str]],
]:
    """Project typed relations to endpoint pairs plus retained kind sets."""

    kinds: dict[tuple[str, str], set[str]] = {}
    for relation in graph_data["edges"]:
        source = relation["source"]
        target = relation["target"]
        if source == target:
            continue
        edge = (source, target)
        kinds.setdefault(edge, set()).add(relation["kind"])
    return sorted(kinds), kinds


def _visual_edges(graph_data: dict[str, Any]) -> list[tuple[str, str]]:
    return _visual_edge_projection(graph_data)[0]


def _relation_kinds(*graphs: dict[str, Any]) -> set[str]:
    kinds: set[str] = set()
    for graph in graphs:
        for edge in graph.get("edges", []):
            kinds.add(edge["kind"])
    return kinds


def _legend(
    policy: ManimRenderPolicy,
    kinds: set[str],
):
    legend = policy.legend_mobject(kinds)
    if len(legend) > 0:
        legend.to_corner(DOWN + LEFT, buff=0.18)
        legend.set_z_index(20)
    return legend


def _commit_date(
    commits: dict[str, dict[str, Any]],
    commit: str,
) -> str:
    record = commits.get(commit)
    if record is None:
        return "date unknown"
    return format_timestamp_date(record.get("timestamp"))


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


def _first_parent_lineage(
    data: dict[str, Any],
    *,
    target_commit: str | None = None,
) -> list[dict[str, Any]]:
    commits, snapshots = _snapshot_maps(data)
    if not snapshots:
        return []

    if target_commit is None:
        ordered = [
            commit["commit"]
            for commit in data.get("commits", [])
            if commit["commit"] in snapshots
        ]
        if not ordered:
            return []
        target_commit = ordered[-1]

    lineage: list[str] = []
    seen: set[str] = set()
    current = target_commit
    while current in commits and current in snapshots and current not in seen:
        seen.add(current)
        lineage.append(current)
        parents = [
            parent
            for parent in commits[current].get("parents", [])
            if parent in snapshots
        ]
        if not parents:
            break
        current = parents[0]

    lineage.reverse()
    return [snapshots[sha] for sha in lineage]


class HistoryGraphView:
    def __init__(self, commits: list[dict[str, Any]]) -> None:
        self.commits = commits
        self.temporal_layout = temporal_history_layout(commits)
        self.positions = {
            sha: list(position)
            for sha, position in self.temporal_layout.positions.items()
        }
        self.axis = _history_axis_mobject(self.temporal_layout)
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

    def __init__(
        self,
        policy: ManimRenderPolicy | None = None,
        *,
        viewport_scale: float = 1.0,
        viewport_shift: tuple[float, float, float] = (0.0, 0.0, 0.0),
    ) -> None:
        self.layout = PersistentLayout()
        self.policy = policy or ManimRenderPolicy()
        self.viewport_scale = viewport_scale
        self.viewport_shift = viewport_shift
        self.graph = DiGraph([], [], layout={})
        self.current_nodes: set[str] = set()
        self.current_edges: set[tuple[str, str]] = set()
        self.current_edge_kinds: dict[tuple[str, str], set[str]] = {}
        self.current_graph_data: dict[str, Any] = {"nodes": [], "edges": []}

    def _viewport_layout(
        self,
        layout: dict[str, list[float]],
    ) -> dict[str, list[float]]:
        sx, sy, sz = self.viewport_shift
        scale = self.viewport_scale
        return {
            node: [
                position[0] * scale + sx,
                position[1] * scale + sy,
                position[2] * scale + sz,
            ]
            for node, position in layout.items()
        }

    def build(self, graph_data: dict[str, Any]) -> DiGraph:
        nodes = [n["symbol_id"] for n in graph_data["nodes"]]
        edges, edge_kinds = _visual_edge_projection(graph_data)
        self.layout.solve(nodes, edges)
        node_data = {
            node["symbol_id"]: node
            for node in graph_data["nodes"]
        }
        vertex_mobjects = {
            node_id: self.policy.vertex_mobject(
                node_data[node_id],
                total_nodes=len(nodes),
            )
            for node_id in nodes
        }
        self.graph = DiGraph(
            nodes,
            edges,
            layout=self._viewport_layout(self.layout.manim_layout()),
            vertex_mobjects=vertex_mobjects,
            edge_config={
                edge: self.policy.edges.edge_config(edge_kinds[edge])
                for edge in edges
            },
        )
        self.current_nodes = set(nodes)
        self.current_edges = set(edges)
        self.current_edge_kinds = edge_kinds
        self.current_graph_data = graph_data
        return self.graph

    def apply_snapshot(
        self,
        scene: MovingCameraScene,
        graph_data: dict[str, Any],
        *,
        run_time: float = 0.35,
    ) -> None:
        target_nodes = {n["symbol_id"] for n in graph_data["nodes"]}
        projected_edges, target_edge_kinds = _visual_edge_projection(graph_data)
        target_edges = set(projected_edges)

        for old_id, new_id in supported_transfers(
            self.current_graph_data,
            graph_data,
        ).items():
            self.layout.transfer_identity(old_id, new_id)

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
        target_layout = self._viewport_layout(
            self.layout.manim_layout()
        )

        if added_nodes:
            node_data = {
                node["symbol_id"]: node
                for node in graph_data["nodes"]
            }
            new_vertices = self.graph.add_vertices(
                *added_nodes,
                positions={node: target_layout[node] for node in added_nodes},
                vertex_mobjects={
                    node: self.policy.vertex_mobject(
                        node_data[node],
                        total_nodes=len(target_nodes),
                    )
                    for node in added_nodes
                },
            )
            scene.play(GrowFromCenter(new_vertices), run_time=run_time)

        if added_edges:
            new_edges = self.graph.add_edges(
                *added_edges,
                edge_config={
                    edge: self.policy.edges.edge_config(
                        target_edge_kinds[edge]
                    )
                    for edge in added_edges
                },
            )
            scene.play(Create(new_edges), run_time=run_time)

        restyled_edges = [
            edge
            for edge in sorted(self.current_edges & target_edges)
            if self.current_edge_kinds.get(edge, set())
            != target_edge_kinds.get(edge, set())
            and edge in self.graph.edges
        ]
        if restyled_edges:
            old_mobjects = [
                self.graph.edges[edge]
                for edge in restyled_edges
            ]
            scene.play(
                *[FadeOut(mobject) for mobject in old_mobjects],
                run_time=run_time / 3,
            )
            self.graph.remove_edges(*restyled_edges)
            refreshed = self.graph.add_edges(
                *restyled_edges,
                edge_config={
                    edge: self.policy.edges.edge_config(
                        target_edge_kinds[edge]
                    )
                    for edge in restyled_edges
                },
            )
            scene.play(
                Create(refreshed),
                run_time=run_time / 3,
            )

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
        self.current_edge_kinds = target_edge_kinds
        self.current_graph_data = graph_data


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


def _episode_focus(
    program,
    snapshots: dict[str, dict[str, Any]],
    *,
    max_context_nodes: int = 320,
    max_context_edges: int = 1000,
) -> tuple[set[str], set[str]]:
    """Changed semantic objects plus one-hop relation context."""

    node_ids: set[str] = set()
    edge_ids: set[str] = set()
    relevant_commits: set[str] = set()

    for command in program:
        payload = command.payload
        if command.kind == "show-fork-snapshot":
            relevant_commits.add(payload["commit"])
        elif command.kind == "advance-branch":
            relevant_commits.add(payload["parent"])
            relevant_commits.add(payload["commit"])
            delta = payload["delta"]
            node_ids.update(delta.get("added_nodes", []))
            node_ids.update(delta.get("removed_nodes", []))
            edge_ids.update(delta.get("added_edges", []))
            edge_ids.update(delta.get("removed_edges", []))
        elif command.kind == "show-parent-delta":
            relevant_commits.add(payload["parent"])
            relevant_commits.add(payload["merge"])
            delta = payload["delta"]
            node_ids.update(delta.get("added_nodes", []))
            node_ids.update(delta.get("removed_nodes", []))
            edge_ids.update(delta.get("added_edges", []))
            edge_ids.update(delta.get("removed_edges", []))
        elif command.kind == "show-snapshot":
            relevant_commits.add(payload["commit"])

    # Edge-only changes pull their endpoints into the focus set.
    for commit in relevant_commits:
        snapshot = snapshots.get(commit)
        if snapshot is None:
            continue
        for edge in snapshot["graph"]["edges"]:
            if edge["relation_id"] in edge_ids:
                node_ids.add(edge["source"])
                node_ids.add(edge["target"])

    # One-hop context makes a new theorem/function legible without expanding the
    # entire repository graph. Changed objects are mandatory; explanatory halo
    # edges/nodes are admitted only while deterministic presentation budgets
    # remain.
    context_candidates: list[dict[str, Any]] = []
    for commit in sorted(relevant_commits):
        snapshot = snapshots.get(commit)
        if snapshot is None:
            continue
        for edge in snapshot["graph"]["edges"]:
            if edge["source"] in node_ids or edge["target"] in node_ids:
                context_candidates.append(edge)

    for edge in sorted(
        {
            edge["relation_id"]: edge
            for edge in context_candidates
        }.values(),
        key=lambda item: (
            item["kind"],
            item["source"],
            item["target"],
            item["relation_id"],
        ),
    ):
        source = edge["source"]
        target = edge["target"]
        new_nodes = {
            node
            for node in (source, target)
            if node not in node_ids
        }

        if edge["relation_id"] not in edge_ids:
            if len(edge_ids) >= max_context_edges:
                continue
        if len(node_ids) + len(new_nodes) > max_context_nodes:
            continue

        edge_ids.add(edge["relation_id"])
        node_ids.update(new_nodes)

    return node_ids, edge_ids


def _induced_focus_graph(
    graph_data: dict[str, Any],
    node_ids: set[str],
    allowed_edge_ids: set[str],
) -> dict[str, Any]:
    return {
        "nodes": [
            node
            for node in graph_data.get("nodes", [])
            if node["symbol_id"] in node_ids
        ],
        "edges": [
            edge
            for edge in graph_data.get("edges", [])
            if edge["relation_id"] in allowed_edge_ids
            and edge["source"] in node_ids
            and edge["target"] in node_ids
        ],
    }


class SemanticSymbolScene(MovingCameraScene):
    """Interpret a rooted semantic focus scene program."""

    def construct(self) -> None:
        path = os.environ.get("DASHI_REPO_HISTORY_JSON")
        selector = os.environ.get("DASHI_REPO_SYMBOL")
        snapshot_index = int(
            os.environ.get("DASHI_REPO_SNAPSHOT_INDEX", "-1")
        )
        upstream_depth = int(
            os.environ.get("DASHI_REPO_UPSTREAM_DEPTH", "2")
        )
        downstream_depth = int(
            os.environ.get("DASHI_REPO_DOWNSTREAM_DEPTH", "0")
        )
        max_focus_nodes = int(
            os.environ.get("DASHI_REPO_MAX_FOCUS_NODES", "250")
        )
        max_focus_edges = int(
            os.environ.get("DASHI_REPO_MAX_FOCUS_EDGES", "800")
        )

        if not path:
            self.add(Text("Set DASHI_REPO_HISTORY_JSON", font_size=28))
            return
        if not selector:
            self.add(Text("Set DASHI_REPO_SYMBOL", font_size=28))
            return

        data = load_history_file(path)
        snapshots = data.get("snapshots", [])
        if not snapshots:
            self.add(Text("No semantic snapshots", font_size=28))
            return

        snapshot = snapshots[snapshot_index]
        graph_data = snapshot["graph"]
        try:
            program = compile_symbol_focus_program(
                graph_data,
                selector,
                upstream_depth=upstream_depth,
                downstream_depth=downstream_depth,
                max_nodes=max_focus_nodes,
                max_edges=max_focus_edges,
            )
        except (KeyError, ValueError) as error:
            self.add(
                Text(str(error), font_size=20).scale_to_fit_width(12.0)
            )
            return
        if not program:
            self.add(Text("No semantic focus program", font_size=26))
            return

        root_id = program[0].payload["root_id"]
        nodes_by_id = {
            node["symbol_id"]: node
            for node in graph_data.get("nodes", [])
        }
        root = nodes_by_id[root_id]
        settle = next(
            command.payload
            for command in reversed(program)
            if command.kind == "settle-focus"
        )
        allowed_edges = set(settle["edge_ids"])

        truncation_badge = VGroup()
        if settle.get("truncated"):
            truncation_badge = Text(
                "context truncated · "
                f"-{settle.get('omitted_nodes', 0)} nodes · "
                f"-{settle.get('omitted_edges', 0)} edges",
                font_size=13,
            ).to_corner(DOWN + RIGHT, buff=0.18)
            truncation_badge.set_z_index(20)

        policy = ManimRenderPolicy()
        full_focus = _induced_focus_graph(
            graph_data,
            set(settle["node_ids"]),
            allowed_edges,
        )
        legend = _legend(
            policy,
            _relation_kinds(full_focus),
        )

        scope_suffix = (
            f" · scope {str(root.get('scope'))[:12]}"
            if root.get("scope")
            else ""
        )
        title = Text(
            f"{root.get('label')} · {root.get('module')}{scope_suffix}",
            font_size=28,
        ).to_edge(UP)
        subtitle = Text(
            f"semantic focus · {snapshot['commit'][:10]}",
            font_size=16,
        ).next_to(title, DOWN, buff=0.10)

        revealed: set[str] = set(program[0].payload["node_ids"])
        view = SemanticGraphView(policy)
        current_graph = _induced_focus_graph(
            graph_data,
            revealed,
            allowed_edges,
        )
        graph = view.build(current_graph)

        self.play(
            FadeIn(title),
            FadeIn(subtitle),
            FadeIn(legend),
            FadeIn(truncation_badge),
            Create(graph),
            run_time=1.0,
        )

        if root_id in view.graph.vertices:
            self.play(
                Indicate(
                    view.graph.vertices[root_id],
                    scale_factor=1.45,
                ),
                run_time=0.35,
            )

        for command in program:
            if command.kind != "expand-focus-layer":
                continue
            payload = command.payload
            revealed.update(payload["node_ids"])
            next_graph = _induced_focus_graph(
                graph_data,
                revealed,
                allowed_edges,
            )
            direction = (
                "dependencies"
                if payload["direction"] == "upstream"
                else "consumers"
            )
            depth_label = Text(
                f"{direction} · depth {payload['depth']}",
                font_size=14,
            ).next_to(subtitle, DOWN, buff=0.08)
            self.play(FadeIn(depth_label), run_time=0.10)
            view.apply_snapshot(
                self,
                next_graph,
                run_time=0.45,
            )
            self.play(FadeOut(depth_label), run_time=0.10)

        if view.graph.width > 0:
            self.play(
                self.camera.frame.animate.move_to(view.graph).set(
                    width=max(8, view.graph.width + 2.0)
                ),
                run_time=0.8,
            )
        self.wait(2)


class SemanticSymbolHistoryScene(MovingCameraScene):
    """Interpret a temporal rooted semantic focus program."""

    def construct(self) -> None:
        path = os.environ.get("DASHI_REPO_HISTORY_JSON")
        selector = os.environ.get("DASHI_REPO_SYMBOL")
        target_commit = os.environ.get("DASHI_REPO_TARGET_COMMIT")
        upstream_depth = int(
            os.environ.get("DASHI_REPO_UPSTREAM_DEPTH", "2")
        )
        downstream_depth = int(
            os.environ.get("DASHI_REPO_DOWNSTREAM_DEPTH", "0")
        )
        max_focus_nodes = int(
            os.environ.get("DASHI_REPO_MAX_FOCUS_NODES", "250")
        )
        max_focus_edges = int(
            os.environ.get("DASHI_REPO_MAX_FOCUS_EDGES", "800")
        )

        if not path:
            self.add(Text("Set DASHI_REPO_HISTORY_JSON", font_size=28))
            return
        if not selector:
            self.add(Text("Set DASHI_REPO_SYMBOL", font_size=28))
            return

        data = load_history_file(path)
        try:
            program = compile_temporal_symbol_program(
                data,
                selector,
                target_commit=target_commit,
                upstream_depth=upstream_depth,
                downstream_depth=downstream_depth,
                max_nodes=max_focus_nodes,
                max_edges=max_focus_edges,
            )
        except (KeyError, ValueError) as error:
            self.add(
                Text(str(error), font_size=20).scale_to_fit_width(12.0)
            )
            return

        if not program:
            self.add(Text("No temporal semantic focus program", font_size=26))
            return

        snapshots = {
            snapshot["commit"]: snapshot
            for snapshot in data.get("snapshots", [])
        }
        commits = {
            commit["commit"]: commit
            for commit in data.get("commits", [])
        }
        frame_graphs: list[dict[str, Any]] = []
        for command in program:
            payload = command.payload
            snapshot = snapshots[payload["commit"]]
            frame_graphs.append(
                _induced_focus_graph(
                    snapshot["graph"],
                    set(payload["node_ids"]),
                    set(payload["edge_ids"]),
                )
            )

        policy = ManimRenderPolicy()
        first_payload = program[0].payload
        truncation_badge = VGroup()
        if first_payload.get("truncated"):
            truncation_badge = Text(
                "context truncated · "
                f"-{first_payload.get('omitted_nodes', 0)} nodes · "
                f"-{first_payload.get('omitted_edges', 0)} edges",
                font_size=13,
            ).to_corner(DOWN + RIGHT, buff=0.18)
            truncation_badge.set_z_index(20)

        legend = _legend(
            policy,
            _relation_kinds(*frame_graphs),
        )

        first = program[0].payload
        title = Text(
            f"{first['root_label']} · {first['root_module']}",
            font_size=28,
        ).to_edge(UP)
        stamp = Text(
            f"{first['commit'][:10]} · {_commit_date(commits, first['commit'])} · "
            f"{first['identity_evidence'].replace('-', ' ')}",
            font_size=15,
        ).next_to(title, DOWN, buff=0.10)

        view = SemanticGraphView(policy)
        graph = view.build(frame_graphs[0])
        self.play(
            FadeIn(title),
            FadeIn(stamp),
            FadeIn(legend),
            FadeIn(truncation_badge),
            Create(graph),
            run_time=1.0,
        )
        if first["root_id"] in view.graph.vertices:
            self.play(
                Indicate(
                    view.graph.vertices[first["root_id"]],
                    scale_factor=1.45,
                ),
                run_time=0.30,
            )

        for command, graph_data in zip(program[1:], frame_graphs[1:]):
            payload = command.payload
            new_title = Text(
                f"{payload['root_label']} · {payload['root_module']}",
                font_size=28,
            ).to_edge(UP)
            evidence = payload["identity_evidence"].replace("-", " ")
            new_stamp = Text(
                f"{payload['commit'][:10]} · "
                f"{_commit_date(commits, payload['commit'])} · "
                f"identity: {evidence}",
                font_size=15,
            ).next_to(new_title, DOWN, buff=0.10)

            self.play(
                ReplacementTransform(title, new_title),
                ReplacementTransform(stamp, new_stamp),
                run_time=0.20,
            )
            title = new_title
            stamp = new_stamp

            view.apply_snapshot(
                self,
                graph_data,
                run_time=0.50,
            )

            if payload["root_id"] in view.graph.vertices:
                self.play(
                    Indicate(
                        view.graph.vertices[payload["root_id"]],
                        scale_factor=1.35,
                    ),
                    run_time=0.20,
                )

        if view.graph.width > 0:
            self.play(
                self.camera.frame.animate.move_to(view.graph).set(
                    width=max(8, view.graph.width + 2.0)
                ),
                run_time=0.8,
            )
        self.wait(2)


class RepositoryHistoryScene(MovingCameraScene):
    """Animate branch/fork/merge topology derived directly from Git parents."""

    def construct(self) -> None:
        path = os.environ.get("DASHI_REPO_HISTORY_JSON")
        if not path:
            self.add(Text("Set DASHI_REPO_HISTORY_JSON", font_size=28))
            return

        data = load_history_file(path)
        commits = data["commits"]

        title = Text(
            "dashi_agda — branch / merge evolution",
            font_size=30,
        ).to_edge(UP)
        self.play(FadeIn(title))

        history = HistoryGraphView(commits)
        self.add(history.graph)
        if len(history.axis) > 0:
            self.play(FadeIn(history.axis), run_time=0.5)

        for commit in commits:
            history.add_commit(self, commit)

        if commits and history.graph.width > 0:
            framed = VGroup(history.graph, history.axis)
            self.play(
                self.camera.frame.animate.move_to(framed).set(
                    width=max(12, framed.width + 1.5)
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

        data = load_history_file(path)
        snapshots = data.get("snapshots", [])
        if not snapshots:
            self.add(Text("No semantic snapshots", font_size=28))
            return

        snapshot = snapshots[snapshot_index]
        commits, _snapshot_lookup = _snapshot_maps(data)
        policy = ManimRenderPolicy()
        graph = SemanticGraphView(policy).build(snapshot["graph"])
        legend = _legend(
            policy,
            _relation_kinds(snapshot["graph"]),
        )
        title = Text(
            f"semantic graph · {snapshot['commit'][:10]} · "
            f"{_commit_date(commits, snapshot['commit'])}",
            font_size=28,
        ).to_edge(UP)
        self.play(FadeIn(title), Create(graph), FadeIn(legend), run_time=2.0)
        if graph.width > 0:
            self.play(
                self.camera.frame.animate.move_to(graph).set(
                    width=max(12, graph.width + 1.5)
                ),
                run_time=1.0,
            )
        self.wait(2)


class SemanticHistoryScene(MovingCameraScene):
    """Interpret a renderer-neutral first-parent semantic scene program."""

    def construct(self) -> None:
        path = os.environ.get("DASHI_REPO_HISTORY_JSON")
        if not path:
            self.add(Text("Set DASHI_REPO_HISTORY_JSON", font_size=28))
            return

        data = load_history_file(path)
        target_commit = os.environ.get("DASHI_REPO_TARGET_COMMIT")
        program = compile_first_parent_program(
            data,
            target_commit=target_commit,
        )
        if not program:
            self.add(Text("No semantic scene program", font_size=28))
            return

        commits, snapshots = _snapshot_maps(data)
        title = Text(
            "dashi_agda — semantic evolution",
            font_size=30,
        ).to_edge(UP)
        stamp = Text("", font_size=17).next_to(title, DOWN, buff=0.12)
        self.play(FadeIn(title), FadeIn(stamp))

        policy = ManimRenderPolicy()
        view = SemanticGraphView(policy)
        history_kinds = _relation_kinds(
            *[snapshot["graph"] for snapshot in snapshots]
        )
        legend = _legend(policy, history_kinds)
        self.play(FadeIn(legend), run_time=0.25)

        pending_commit: str | None = None
        graph_created = False

        for command in program:
            kind = command.kind
            payload = command.payload

            if kind == "show-snapshot":
                commit = payload["commit"]
                snapshot = snapshots.get(commit)
                if snapshot is None:
                    continue
                graph = view.build(snapshot["graph"])
                next_stamp = Text(
                    f"{commit[:10]} · {_commit_date(commits, commit)}",
                    font_size=17,
                ).next_to(title, DOWN, buff=0.12)
                self.play(
                    ReplacementTransform(stamp, next_stamp),
                    Create(graph),
                    run_time=1.0,
                )
                stamp = next_stamp
                graph_created = True
                continue

            if kind == "advance-commit":
                pending_commit = payload["commit"]
                next_stamp = Text(
                    f"{pending_commit[:10]} · "
                    f"{_commit_date(commits, pending_commit)}",
                    font_size=17,
                ).next_to(title, DOWN, buff=0.12)
                self.play(
                    ReplacementTransform(stamp, next_stamp),
                    run_time=0.12,
                )
                stamp = next_stamp
                continue

            # add/remove node/edge commands are retained in the program as exact
            # semantic evidence.  The Manim backend batches them at settle-layout
            # so related changes animate coherently and layout moves only once.
            if kind in {
                "add-node",
                "remove-node",
                "add-edge",
                "remove-edge",
            }:
                continue

            if kind == "settle-layout" and pending_commit is not None:
                snapshot = snapshots.get(pending_commit)
                if snapshot is not None:
                    if graph_created:
                        view.apply_snapshot(self, snapshot["graph"])
                    else:
                        graph = view.build(snapshot["graph"])
                        self.play(Create(graph), run_time=1.0)
                        graph_created = True
                pending_commit = None

        self.wait(2)


class SemanticBranchEpisodeScene(MovingCameraScene):
    """Animate one real fork -> two semantic branch paths -> merge episode."""

    def construct(self) -> None:
        path = os.environ.get("DASHI_REPO_HISTORY_JSON")
        episode_index = int(os.environ.get("DASHI_REPO_EPISODE_INDEX", "0"))
        if not path:
            self.add(Text("Set DASHI_REPO_HISTORY_JSON", font_size=28))
            return

        data = load_history_file(path)
        program = compile_branch_episode_program(
            data,
            episode_index=episode_index,
        )
        if not program:
            self.add(
                Text(
                    "No complete semantic branch episode; extract with --episode-context",
                    font_size=24,
                )
            )
            return

        commits, snapshots = _snapshot_maps(data)
        fork_command = next(
            command
            for command in program
            if command.kind == "show-fork-snapshot"
        )
        convergence = next(
            command.payload
            for command in program
            if command.kind == "converge-parents"
        )

        fork = fork_command.payload["commit"]
        left_tip = convergence["left"]
        right_tip = convergence["right"]
        merge_sha = convergence["merge"]

        focus_nodes, focus_edges = _episode_focus(
            program,
            snapshots,
        )

        policy = ManimRenderPolicy()

        def focused(commit: str) -> dict[str, Any]:
            return _changed_graph(
                snapshots[commit],
                focus_nodes,
                focus_edges,
            )

        title = Text(
            f"semantic branch episode · fork {fork[:9]} → merge {merge_sha[:9]}",
            font_size=28,
        ).to_edge(UP)
        self.play(FadeIn(title))

        focused_graphs = [
            focused(commit)
            for commit in snapshots
            if commit == fork
            or commit == merge_sha
            or any(
                command.kind == "advance-branch"
                and command.payload["commit"] == commit
                for command in program
            )
        ]
        legend = _legend(
            policy,
            _relation_kinds(*focused_graphs),
        )
        self.play(FadeIn(legend), run_time=0.25)

        fork_view = SemanticGraphView(
            policy,
            viewport_scale=0.66,
            viewport_shift=(0.0, -0.15, 0.0),
        )
        fork_graph = fork_view.build(focused(fork))
        fork_label = Text(
            f"fork · {fork[:10]} · {_commit_date(commits, fork)}",
            font_size=18,
        ).next_to(title, DOWN, buff=0.12)
        self.play(FadeIn(fork_label), Create(fork_graph), run_time=1.1)

        left_view = SemanticGraphView(
            policy,
            viewport_scale=0.40,
            viewport_shift=(-3.35, -0.25, 0.0),
        )
        right_view = SemanticGraphView(
            policy,
            viewport_scale=0.40,
            viewport_shift=(3.35, -0.25, 0.0),
        )
        left_graph = left_view.build(focused(fork))
        right_graph = right_view.build(focused(fork))

        left_label = Text(
            f"branch A · {fork[:9]} · {_commit_date(commits, fork)}",
            font_size=16,
        ).move_to(LEFT * 3.35 + UP * 2.15)
        right_label = Text(
            f"branch B · {fork[:9]} · {_commit_date(commits, fork)}",
            font_size=16,
        ).move_to(RIGHT * 3.35 + UP * 2.15)

        self.play(
            TransformFromCopy(fork_graph, left_graph),
            TransformFromCopy(fork_graph, right_graph),
            run_time=1.0,
        )
        self.play(
            FadeOut(fork_graph),
            FadeOut(fork_label),
            FadeIn(left_label),
            FadeIn(right_label),
            run_time=0.35,
        )

        labels = {
            "left": left_label,
            "right": right_label,
        }
        views = {
            "left": left_view,
            "right": right_view,
        }

        for command in program:
            if command.kind != "advance-branch":
                continue

            side = command.payload["side"]
            commit = command.payload["commit"]
            view = views[side]
            old_label = labels[side]
            new_label = Text(
                f"branch {'A' if side == 'left' else 'B'} · "
                f"{commit[:9]} · {_commit_date(commits, commit)}",
                font_size=16,
            ).move_to(
                (LEFT if side == "left" else RIGHT) * 3.35
                + UP * 2.15
            )

            self.play(
                ReplacementTransform(old_label, new_label),
                run_time=0.12,
            )
            labels[side] = new_label
            view.apply_snapshot(
                self,
                focused(commit),
                run_time=0.30,
            )

        merge_commit = commits[merge_sha]
        attribution = attribute_merge(
            merge_commit=merge_commit,
            snapshots_by_commit=snapshots,
        )
        merge_view = SemanticGraphView(
            policy,
            viewport_scale=0.66,
            viewport_shift=(0.0, -0.15, 0.0),
        )
        merge_graph = merge_view.build(focused(merge_sha))
        merge_label = Text(
            f"merge · {merge_sha[:10]} · {_commit_date(commits, merge_sha)}",
            font_size=18,
        ).next_to(title, DOWN, buff=0.12)

        parents = VGroup(
            left_view.graph,
            right_view.graph,
        )
        self.play(
            FadeOut(labels["left"]),
            FadeOut(labels["right"]),
            ReplacementTransform(parents, merge_graph),
            FadeIn(merge_label),
            run_time=1.5,
        )

        merge_only = [
            node_id
            for node_id in attribution.introduced_nodes
            if node_id in merge_view.graph.vertices
        ]
        for node_id in merge_only[:16]:
            self.play(
                Indicate(
                    merge_view.graph.vertices[node_id],
                    scale_factor=1.35,
                ),
                run_time=0.10,
            )

        self.wait(2)


class SemanticMergeScene(MovingCameraScene):
    """Interpret an explicit branch-episode convergence scene program."""

    def construct(self) -> None:
        path = os.environ.get("DASHI_REPO_HISTORY_JSON")
        episode_index = int(os.environ.get("DASHI_REPO_EPISODE_INDEX", "0"))
        if not path:
            self.add(Text("Set DASHI_REPO_HISTORY_JSON", font_size=28))
            return

        data = load_history_file(path)
        program = compile_merge_episode_program(
            data,
            episode_index=episode_index,
        )
        if not program:
            self.add(Text("No semantic merge scene program", font_size=26))
            return

        commits, snapshots = _snapshot_maps(data)
        fork_payload = next(
            command.payload
            for command in program
            if command.kind == "show-fork"
        )
        convergence = next(
            command.payload
            for command in program
            if command.kind == "converge-parents"
        )

        left = convergence["left"]
        right = convergence["right"]
        merge_sha = convergence["merge"]
        merge_commit = commits[merge_sha]

        attribution = attribute_merge(
            merge_commit=merge_commit,
            snapshots_by_commit=snapshots,
        )

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

        left_data = _changed_graph(
            snapshots[left],
            changed_nodes,
            changed_edges,
        )
        right_data = _changed_graph(
            snapshots[right],
            changed_nodes,
            changed_edges,
        )
        merge_data = _changed_graph(
            snapshots[merge_sha],
            changed_nodes,
            changed_edges,
        )

        policy = ManimRenderPolicy()
        left_graph = SemanticGraphView(policy).build(left_data)
        right_graph = SemanticGraphView(policy).build(right_data)
        merged_graph = SemanticGraphView(policy).build(merge_data)
        legend = _legend(
            policy,
            _relation_kinds(left_data, right_data, merge_data),
        )
        self.play(FadeIn(legend), run_time=0.25)

        left_path = fork_payload["left_path"]
        right_path = fork_payload["right_path"]

        left_group = VGroup(
            Text(
                f"parent A · {left[:9]} · {max(0, len(left_path) - 1)} steps",
                font_size=18,
            ),
            left_graph,
        ).arrange(DOWN, buff=0.2)
        right_group = VGroup(
            Text(
                f"parent B · {right[:9]} · {max(0, len(right_path) - 1)} steps",
                font_size=18,
            ),
            right_graph,
        ).arrange(DOWN, buff=0.2)
        parents = VGroup(left_group, right_group).arrange(buff=1.0)
        parents.scale_to_fit_width(12.0)

        title = Text(
            f"semantic merge · {merge_sha[:10]} · fork {fork_payload['fork_base'][:9]}",
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
        ).arrange(DOWN, buff=0.2)
        merged_group.scale_to_fit_width(11.0)

        self.play(
            ReplacementTransform(parents, merged_group),
            run_time=1.6,
        )
        self.wait(2)


def _film_graph(
    snapshot: dict[str, Any],
    admitted_nodes: set[str],
) -> dict[str, Any]:
    graph = snapshot["graph"]
    nodes = [
        node
        for node in graph.get("nodes", [])
        if node["symbol_id"] in admitted_nodes
    ]
    node_ids = {node["symbol_id"] for node in nodes}
    edges = [
        edge
        for edge in graph.get("edges", [])
        if edge["source"] in node_ids
        and edge["target"] in node_ids
    ]
    return {"nodes": nodes, "edges": edges}


def _camera_fit_width(
    group: VGroup,
    *,
    frame_aspect: float,
    padding: float,
    min_width: float,
    max_width: float,
) -> float:
    width = max(
        group.width * padding,
        group.height * frame_aspect * padding,
        min_width,
    )
    return min(max_width, width)


def _focus_group(view, node_ids: set[str]) -> VGroup:
    mobjects = [
        view.graph.vertices[node_id]
        for node_id in node_ids
        if node_id in view.graph.vertices
    ]
    return VGroup(*mobjects)


class ResearchAtlasGraphView(SemanticGraphView):
    """Semantic graph view with persistent programme territories."""

    def __init__(
        self,
        regions,
        policy: ManimRenderPolicy | None = None,
    ) -> None:
        super().__init__(policy)
        self.atlas = ResearchAtlasLayout(
            {
                region.programme: region
                for region in regions
            }
        )

    def build(self, graph_data: dict[str, Any]) -> DiGraph:
        nodes = [node["symbol_id"] for node in graph_data["nodes"]]
        edges, edge_kinds = _visual_edge_projection(graph_data)
        target_layout = self.atlas.solve(graph_data)
        node_data = {
            node["symbol_id"]: node
            for node in graph_data["nodes"]
        }
        self.graph = DiGraph(
            nodes,
            edges,
            layout=target_layout,
            vertex_mobjects={
                node_id: self.policy.vertex_mobject(
                    node_data[node_id],
                    total_nodes=len(nodes),
                )
                for node_id in nodes
            },
            edge_config={
                edge: self.policy.edges.edge_config(edge_kinds[edge])
                for edge in edges
            },
        )
        self.current_nodes = set(nodes)
        self.current_edges = set(edges)
        self.current_edge_kinds = edge_kinds
        self.current_graph_data = graph_data
        return self.graph

    def apply_snapshot(
        self,
        scene: MovingCameraScene,
        graph_data: dict[str, Any],
        *,
        run_time: float = 0.35,
    ) -> None:
        target_nodes = {
            node["symbol_id"]
            for node in graph_data["nodes"]
        }
        projected_edges, target_edge_kinds = _visual_edge_projection(
            graph_data
        )
        target_edges = set(projected_edges)

        for old_id, new_id in supported_transfers(
            self.current_graph_data,
            graph_data,
        ).items():
            self.atlas.transfer_identity(old_id, new_id)

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
            scene.play(*edge_fades, run_time=run_time / 3)
        if removed_edges:
            self.graph.remove_edges(*removed_edges)

        node_fades = [
            FadeOut(self.graph.vertices[node])
            for node in removed_nodes
            if node in self.graph.vertices
        ]
        if node_fades:
            scene.play(*node_fades, run_time=run_time / 3)
        if removed_nodes:
            self.graph.remove_vertices(*removed_nodes)

        target_layout = self.atlas.solve(graph_data)
        node_data = {
            node["symbol_id"]: node
            for node in graph_data["nodes"]
        }

        if added_nodes:
            new_vertices = self.graph.add_vertices(
                *added_nodes,
                positions={
                    node: target_layout[node]
                    for node in added_nodes
                },
                vertex_mobjects={
                    node: self.policy.vertex_mobject(
                        node_data[node],
                        total_nodes=len(target_nodes),
                    )
                    for node in added_nodes
                },
            )
            scene.play(
                GrowFromCenter(new_vertices),
                run_time=run_time / 2,
            )

        if added_edges:
            new_edges = self.graph.add_edges(
                *added_edges,
                edge_config={
                    edge: self.policy.edges.edge_config(
                        target_edge_kinds[edge]
                    )
                    for edge in added_edges
                },
            )
            scene.play(Create(new_edges), run_time=run_time / 2)

        if target_nodes:
            scene.play(
                self.graph.animate.change_layout(target_layout),
                run_time=run_time,
            )

        self.current_nodes = target_nodes
        self.current_edges = target_edges
        self.current_edge_kinds = target_edge_kinds
        self.current_graph_data = graph_data


def _research_time_rail(
    commits: dict[str, dict[str, Any]],
):
    timestamps = [
        int(commit.get("timestamp", 0))
        for commit in commits.values()
        if commit.get("timestamp") is not None
    ]
    if not timestamps:
        return VGroup(), None, None, None

    minimum = min(timestamps)
    maximum = max(timestamps)
    line = Line(
        [0.0, -2.0, 0.0],
        [0.0, 2.0, 0.0],
    )
    marker = Dot(radius=0.055).move_to(line.get_bottom())
    oldest = Text(
        format_timestamp_date(minimum),
        font_size=8,
    ).next_to(line, DOWN, buff=0.08)
    newest = Text(
        format_timestamp_date(maximum),
        font_size=8,
    ).next_to(line, UP, buff=0.08)
    caption = Text(
        "time",
        font_size=8,
    ).next_to(line, LEFT, buff=0.08)
    return (
        VGroup(line, marker, oldest, newest, caption),
        line,
        marker,
        (minimum, maximum),
    )


class ResearchEvolutionScene(MovingCameraScene):
    """Directed semantic film of the evolving formal research programme."""

    def _pin_hud(self, mobject, slot: str) -> None:
        base_frame_width = float(self.camera.frame.width)
        base_width = max(0.01, float(mobject.width))

        def updater(mob):
            frame = self.camera.frame
            scale = float(frame.width) / max(0.01, base_frame_width)
            mob.scale_to_fit_width(base_width * scale)

            if slot == "title":
                target = frame.get_top() + DOWN * (0.28 * scale)
            elif slot == "programme":
                target = frame.get_top() + DOWN * (0.72 * scale)
            elif slot == "topic":
                target = frame.get_top() + DOWN * (1.02 * scale)
            elif slot == "work":
                target = frame.get_top() + DOWN * (1.30 * scale)
            elif slot == "commit":
                target = (
                    frame.get_corner(DOWN + LEFT)
                    + UP * (0.28 * scale)
                    + RIGHT * (2.2 * scale)
                )
            elif slot == "date":
                target = (
                    frame.get_corner(DOWN + RIGHT)
                    + UP * (0.28 * scale)
                    + LEFT * (1.25 * scale)
                )
            elif slot == "timeline":
                target = (
                    frame.get_right()
                    + LEFT * (0.48 * scale)
                )
            else:
                target = frame.get_bottom() + UP * (0.62 * scale)

            mob.move_to(target)

        mobject.add_updater(updater)
        updater(mobject)

    def _focus_camera(
        self,
        view: ResearchAtlasGraphView,
        node_ids: set[str],
        directive,
    ) -> None:
        focus = _focus_group(view, node_ids)
        if len(focus) == 0:
            region = view.atlas.regions.get(directive.programme)
            if region is None:
                return
            target = [region.x, region.y, 0.0]
            width = directive.min_width
        else:
            target = focus.get_center()
            frame_aspect = (
                self.camera.frame.width
                / max(0.01, self.camera.frame.height)
            )
            width = _camera_fit_width(
                focus,
                frame_aspect=frame_aspect,
                padding=directive.padding,
                min_width=directive.min_width,
                max_width=directive.max_width,
            )

        previous = getattr(self, "_last_camera_target", None)
        previous_width = getattr(self, "_last_camera_width", None)
        if previous is not None and previous_width is not None:
            distance = hypot(
                float(target[0]) - float(previous[0]),
                float(target[1]) - float(previous[1]),
            )
            width_change = abs(width - previous_width) / max(
                0.01,
                previous_width,
            )
            # Camera motion is editorial, not a response to every microscopic
            # layout movement. Keep the current frame unless the semantic
            # working set has moved materially.
            if distance < 0.18 and width_change < 0.06:
                return

        self.play(
            self.camera.frame.animate.move_to(target).set(width=width),
            run_time=directive.transition_seconds,
        )
        self._last_camera_target = (
            float(target[0]),
            float(target[1]),
        )
        self._last_camera_width = float(width)

    def construct(self) -> None:
        path = os.environ.get("DASHI_REPO_HISTORY_JSON")
        if not path:
            self.add(Text("Set DASHI_REPO_HISTORY_JSON", font_size=28))
            return

        data = load_history_file(path)
        plan = compile_research_film(data)
        if not plan.beats:
            self.add(Text("No semantic research-film beats", font_size=28))
            return

        commits = {
            commit["commit"]: commit
            for commit in data.get("commits", [])
        }
        snapshots = {
            snapshot["commit"]: snapshot
            for snapshot in data.get("snapshots", [])
        }
        time_rail, time_line, time_marker, time_bounds = (
            _research_time_rail(commits)
        )

        policy = ManimRenderPolicy()
        view = ResearchAtlasGraphView(plan.regions, policy)

        title = Text("Dashi formal research evolution", font_size=28)
        programme_label = Text("", font_size=18)
        topic_label = Text("", font_size=13)
        work_label = Text("", font_size=11)
        commit_label = Text("", font_size=10)
        date_label = Text("", font_size=12)
        self._pin_hud(title, "title")
        self._pin_hud(programme_label, "programme")
        self._pin_hud(topic_label, "topic")
        self._pin_hud(work_label, "work")
        self._pin_hud(commit_label, "commit")
        self._pin_hud(date_label, "date")
        if len(time_rail) > 0:
            self._pin_hud(time_rail, "timeline")
        self.add(
            title,
            programme_label,
            topic_label,
            work_label,
            commit_label,
            date_label,
            time_rail,
        )

        region_labels = VGroup(
            *[
                Text(
                    region.programme,
                    font_size=20,
                )
                .move_to([region.x, region.y + 3.7, 0.0])
                .set_opacity(0.22)
                for region in plan.regions
            ]
        )
        self.add(region_labels)
        self.play(
            FadeIn(title),
            FadeIn(region_labels),
            run_time=0.35,
        )

        graph_created = False
        current_commit: str | None = None

        for beat in plan.beats:
            if beat.kind == "episode-title":
                next_programme = Text(
                    beat.programme or "Unclassified",
                    font_size=18,
                )
                next_topic = Text(
                    str(
                        (beat.payload or {}).get(
                            "headline",
                            beat.topic or "formal development",
                        )
                    ),
                    font_size=13,
                )
                self._pin_hud(next_programme, "programme")
                self._pin_hud(next_topic, "topic")
                self.add(next_programme, next_topic)
                self.play(
                    ReplacementTransform(
                        programme_label,
                        next_programme,
                    ),
                    ReplacementTransform(
                        topic_label,
                        next_topic,
                    ),
                    run_time=0.25,
                )
                programme_label = next_programme
                topic_label = next_topic

                if beat.camera is not None and graph_created:
                    self._focus_camera(
                        view,
                        set(beat.focus_node_ids),
                        beat.camera,
                    )
                continue

            if beat.kind in {
                "branch-fork",
                "branch-merge",
                "pr-merge",
                "cross-programme-overview",
            }:
                if (
                    beat.kind == "cross-programme-overview"
                    and beat.commit is not None
                    and beat.visible_node_ids
                ):
                    overview_snapshot = snapshots.get(beat.commit)
                    if overview_snapshot is not None:
                        overview_graph = _film_graph(
                            overview_snapshot,
                            set(beat.visible_node_ids),
                        )
                        if graph_created:
                            view.apply_snapshot(
                                self,
                                overview_graph,
                                run_time=0.35,
                            )
                        else:
                            graph = view.build(overview_graph)
                            self.play(Create(graph), run_time=0.65)
                            graph_created = True

                if beat.camera is not None and graph_created:
                    self._focus_camera(
                        view,
                        set(beat.focus_node_ids),
                        beat.camera,
                    )

                event_text = beat.topic or beat.kind.replace("-", " ")
                banner = Text(
                    event_text,
                    font_size=15,
                )
                self._pin_hud(banner, "event")
                self.add(banner)
                self.play(FadeIn(banner), run_time=0.18)
                self.wait(max(0.05, beat.duration_seconds - 0.30))
                self.play(FadeOut(banner), run_time=0.12)
                self.remove(banner)
                continue

            if beat.kind != "semantic-change" or beat.commit is None:
                continue

            snapshot = snapshots.get(beat.commit)
            if snapshot is None:
                continue

            # Focus the previous state first so removals happen where the viewer
            # is already looking rather than disappearing off-screen.
            if beat.camera is not None and graph_created:
                self._focus_camera(
                    view,
                    set(beat.focus_node_ids),
                    beat.camera,
                )

            visible_nodes = set(
                beat.visible_node_ids
                or beat.focus_node_ids
            )
            next_graph = _film_graph(
                snapshot,
                visible_nodes,
            )

            if not graph_created:
                graph = view.build(next_graph)
                self.play(Create(graph), run_time=0.8)
                graph_created = True
            else:
                view.apply_snapshot(
                    self,
                    next_graph,
                    run_time=max(0.25, beat.duration_seconds * 0.55),
                )

            current_commit = beat.commit
            commit = commits.get(current_commit, {})
            next_date = Text(
                f"{_commit_date(commits, current_commit)} · "
                f"{current_commit[:10]}",
                font_size=12,
            )
            self._pin_hud(next_date, "date")
            self.add(next_date)
            self.play(
                ReplacementTransform(date_label, next_date),
                run_time=0.12,
            )
            date_label = next_date

            if (
                time_line is not None
                and time_marker is not None
                and time_bounds is not None
                and commit.get("timestamp") is not None
            ):
                minimum, maximum = time_bounds
                timestamp = int(commit["timestamp"])
                fraction = (
                    0.0
                    if maximum <= minimum
                    else (timestamp - minimum) / (maximum - minimum)
                )
                fraction = min(1.0, max(0.0, fraction))
                self.play(
                    time_marker.animate.move_to(
                        time_line.point_from_proportion(fraction)
                    ),
                    run_time=0.10,
                )

            payload = beat.payload or {}
            changed_symbols = payload.get("changed_symbols", [])
            lane = payload.get("lane")
            modules = payload.get("modules", [])
            symbol_text = " · ".join(
                str(item.get("label", ""))
                for item in changed_symbols[:4]
                if item.get("label")
            )
            if len(changed_symbols) > 4:
                symbol_text += f" +{len(changed_symbols) - 4}"
            context_bits = []
            if lane:
                context_bits.append(f"Lane {lane}")
            if modules:
                context_bits.append(
                    str(modules[0]).replace("DASHI.", "")
                )
            if symbol_text:
                context_bits.append(symbol_text)
            next_work = Text(
                "  |  ".join(context_bits),
                font_size=11,
            )
            self._pin_hud(next_work, "work")
            self.add(next_work)
            self.play(
                ReplacementTransform(work_label, next_work),
                run_time=0.10,
            )
            work_label = next_work

            subject = str(payload.get("commit_subject", "")).strip()
            next_commit_label = Text(
                subject[:120],
                font_size=10,
            )
            self._pin_hud(next_commit_label, "commit")
            self.add(next_commit_label)
            self.play(
                ReplacementTransform(
                    commit_label,
                    next_commit_label,
                ),
                run_time=0.10,
            )
            commit_label = next_commit_label

            if beat.camera is not None:
                self._focus_camera(
                    view,
                    set(beat.focus_node_ids),
                    beat.camera,
                )

            changed = set(
                (beat.payload or {}).get("changed_nodes", [])
            )
            highlights = [
                Indicate(
                    view.graph.vertices[node_id],
                    scale_factor=1.35,
                )
                for node_id in list(changed)[:8]
                if node_id in view.graph.vertices
            ]
            if highlights:
                self.play(
                    *highlights,
                    run_time=min(0.45, beat.duration_seconds * 0.35),
                )

            hold = max(
                0.05,
                beat.duration_seconds
                - (beat.camera.transition_seconds if beat.camera else 0.0)
                - 0.20,
            )
            self.wait(hold)

        self.wait(1.0)
