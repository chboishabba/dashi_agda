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
    DOWN,
    LEFT,
    RIGHT,
    FadeIn,
    FadeOut,
    GrowFromCenter,
    Indicate,
    MovingCameraScene,
    ReplacementTransform,
    Text,
    TransformFromCopy,
    UP,
    VGroup,
)

from dashi_repo_history.identity import supported_transfers
from dashi_repo_history.layout import PersistentLayout
from dashi_repo_history.merge_attribution import attribute_merge
from dashi_repo_history.render_policy import ManimRenderPolicy
from dashi_repo_history.scene_program import (
    compile_branch_episode_program,
    compile_first_parent_program,
    compile_merge_episode_program,
)


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
        edges = _visual_edges(graph_data)
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
        )
        self.current_nodes = set(nodes)
        self.current_edges = set(edges)
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
        target_edges = set(_visual_edges(graph_data))

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
    # entire repository graph.
    for commit in relevant_commits:
        snapshot = snapshots.get(commit)
        if snapshot is None:
            continue
        for edge in snapshot["graph"]["edges"]:
            if edge["source"] in node_ids or edge["target"] in node_ids:
                edge_ids.add(edge["relation_id"])
                node_ids.add(edge["source"])
                node_ids.add(edge["target"])

    return node_ids, edge_ids


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
    """Interpret a renderer-neutral first-parent semantic scene program."""

    def construct(self) -> None:
        path = os.environ.get("DASHI_REPO_HISTORY_JSON")
        if not path:
            self.add(Text("Set DASHI_REPO_HISTORY_JSON", font_size=28))
            return

        data = json.loads(Path(path).read_text(encoding="utf-8"))
        target_commit = os.environ.get("DASHI_REPO_TARGET_COMMIT")
        program = compile_first_parent_program(
            data,
            target_commit=target_commit,
        )
        if not program:
            self.add(Text("No semantic scene program", font_size=28))
            return

        _commits, snapshots = _snapshot_maps(data)
        title = Text(
            "dashi_agda — semantic evolution",
            font_size=30,
        ).to_edge(UP)
        stamp = Text("", font_size=17).next_to(title, DOWN, buff=0.12)
        self.play(FadeIn(title), FadeIn(stamp))

        view = SemanticGraphView()
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
                    commit[:10],
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
                    pending_commit[:10],
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

        data = json.loads(Path(path).read_text(encoding="utf-8"))
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

        fork_view = SemanticGraphView(
            viewport_scale=0.66,
            viewport_shift=(0.0, -0.15, 0.0),
        )
        fork_graph = fork_view.build(focused(fork))
        fork_label = Text(
            f"fork · {fork[:10]}",
            font_size=18,
        ).next_to(title, DOWN, buff=0.12)
        self.play(FadeIn(fork_label), Create(fork_graph), run_time=1.1)

        left_view = SemanticGraphView(
            viewport_scale=0.40,
            viewport_shift=(-3.35, -0.25, 0.0),
        )
        right_view = SemanticGraphView(
            viewport_scale=0.40,
            viewport_shift=(3.35, -0.25, 0.0),
        )
        left_graph = left_view.build(focused(fork))
        right_graph = right_view.build(focused(fork))

        left_label = Text(
            f"branch A · {fork[:9]}",
            font_size=16,
        ).move_to(LEFT * 3.35 + UP * 2.15)
        right_label = Text(
            f"branch B · {fork[:9]}",
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
                f"branch {'A' if side == 'left' else 'B'} · {commit[:9]}",
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
            viewport_scale=0.66,
            viewport_shift=(0.0, -0.15, 0.0),
        )
        merge_graph = merge_view.build(focused(merge_sha))
        merge_label = Text(
            f"merge · {merge_sha[:10]}",
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

        data = json.loads(Path(path).read_text(encoding="utf-8"))
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

        left_graph = SemanticGraphView().build(left_data)
        right_graph = SemanticGraphView().build(right_data)
        merged_graph = SemanticGraphView().build(merge_data)

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
