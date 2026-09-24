from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
from typing import Any


COMPACT_SCHEMA = "dashi.repo-history.v2"
EXPANDED_SCHEMA = "dashi.repo-history.v1"


def _node_map(graph: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        node["symbol_id"]: node
        for node in graph.get("nodes", [])
    }


def _edge_map(graph: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        edge["relation_id"]: edge
        for edge in graph.get("edges", [])
    }


def graph_patch(
    before: dict[str, Any],
    after: dict[str, Any],
) -> dict[str, Any]:
    before_nodes = _node_map(before)
    after_nodes = _node_map(after)
    before_edges = _edge_map(before)
    after_edges = _edge_map(after)

    added_nodes = [
        deepcopy(after_nodes[node_id])
        for node_id in sorted(after_nodes.keys() - before_nodes.keys())
    ]
    removed_nodes = sorted(before_nodes.keys() - after_nodes.keys())
    updated_nodes = [
        deepcopy(after_nodes[node_id])
        for node_id in sorted(before_nodes.keys() & after_nodes.keys())
        if before_nodes[node_id] != after_nodes[node_id]
    ]

    added_edges = [
        deepcopy(after_edges[edge_id])
        for edge_id in sorted(after_edges.keys() - before_edges.keys())
    ]
    removed_edges = sorted(before_edges.keys() - after_edges.keys())
    updated_edges = [
        deepcopy(after_edges[edge_id])
        for edge_id in sorted(before_edges.keys() & after_edges.keys())
        if before_edges[edge_id] != after_edges[edge_id]
    ]

    return {
        "added_nodes": added_nodes,
        "removed_nodes": removed_nodes,
        "updated_nodes": updated_nodes,
        "added_edges": added_edges,
        "removed_edges": removed_edges,
        "updated_edges": updated_edges,
        # These are observation collections rather than identity-keyed graph
        # elements. Replacing them keeps the patch contract simple and lossless.
        "unresolved_references": deepcopy(
            after.get("unresolved_references", [])
        ),
        "parse_error_files": list(
            after.get("parse_error_files", [])
        ),
    }


def apply_graph_patch(
    before: dict[str, Any],
    patch: dict[str, Any],
) -> dict[str, Any]:
    nodes = _node_map(before)
    edges = _edge_map(before)

    for node_id in patch.get("removed_nodes", []):
        nodes.pop(node_id, None)
    for node in patch.get("updated_nodes", []):
        nodes[node["symbol_id"]] = deepcopy(node)
    for node in patch.get("added_nodes", []):
        nodes[node["symbol_id"]] = deepcopy(node)

    for edge_id in patch.get("removed_edges", []):
        edges.pop(edge_id, None)
    for edge in patch.get("updated_edges", []):
        edges[edge["relation_id"]] = deepcopy(edge)
    for edge in patch.get("added_edges", []):
        edges[edge["relation_id"]] = deepcopy(edge)

    return {
        "graph_id": _graph_id_passthrough(
            patch.get("graph_id")
        ),
        "nodes": [
            nodes[node_id]
            for node_id in sorted(nodes)
        ],
        "edges": [
            edges[edge_id]
            for edge_id in sorted(edges)
        ],
        "unresolved_references": deepcopy(
            patch.get("unresolved_references", [])
        ),
        "parse_error_files": list(
            patch.get("parse_error_files", [])
        ),
    }


def _graph_id_passthrough(value: Any) -> Any:
    # graph_id is stored on each semantic-state record because reproducing the
    # Python stable_hash implementation in every future renderer is unnecessary.
    return value


def compact_timeline(
    timeline: dict[str, Any],
    *,
    checkpoint_interval: int = 50,
) -> dict[str, Any]:
    if timeline.get("schema") == COMPACT_SCHEMA:
        return deepcopy(timeline)
    if timeline.get("schema") != EXPANDED_SCHEMA:
        raise ValueError(
            f"unsupported history schema: {timeline.get('schema')!r}"
        )

    checkpoint_interval = max(1, int(checkpoint_interval))
    commits = list(timeline.get("commits", []))
    snapshots = {
        snapshot["commit"]: snapshot
        for snapshot in timeline.get("snapshots", [])
    }

    materialized: dict[str, dict[str, Any]] = {}
    states: list[dict[str, Any]] = []
    since_checkpoint = 0

    for commit in commits:
        sha = commit["commit"]
        snapshot = snapshots.get(sha)
        if snapshot is None:
            continue

        graph = snapshot["graph"]
        parent = next(
            (
                candidate
                for candidate in commit.get("parents", [])
                if candidate in materialized
            ),
            None,
        )

        must_checkpoint = (
            parent is None
            or since_checkpoint >= checkpoint_interval
        )

        if must_checkpoint:
            states.append(
                {
                    "commit": sha,
                    "parent": parent,
                    "checkpoint": deepcopy(graph),
                    "parent_deltas": deepcopy(
                        snapshot.get("parent_deltas", {})
                    ),
                }
            )
            since_checkpoint = 0
        else:
            patch = graph_patch(materialized[parent], graph)
            patch["graph_id"] = graph.get("graph_id")
            states.append(
                {
                    "commit": sha,
                    "parent": parent,
                    "patch": patch,
                    "parent_deltas": deepcopy(
                        snapshot.get("parent_deltas", {})
                    ),
                }
            )
            since_checkpoint += 1

        materialized[sha] = deepcopy(graph)

    result = {
        "schema": COMPACT_SCHEMA,
        "checkpoint_interval": checkpoint_interval,
        "commits": deepcopy(commits),
        "refs": deepcopy(timeline.get("refs", {})),
        "branch_episodes": deepcopy(
            timeline.get("branch_episodes", [])
        ),
        "semantic_states": states,
    }
    if "pull_requests" in timeline:
        result["pull_requests"] = deepcopy(
            timeline.get("pull_requests", [])
        )
    return result


def expand_timeline(compact: dict[str, Any]) -> dict[str, Any]:
    if compact.get("schema") == EXPANDED_SCHEMA:
        return deepcopy(compact)
    if compact.get("schema") != COMPACT_SCHEMA:
        raise ValueError(
            f"unsupported history schema: {compact.get('schema')!r}"
        )

    graphs: dict[str, dict[str, Any]] = {}
    snapshots: list[dict[str, Any]] = []

    for state in compact.get("semantic_states", []):
        sha = state["commit"]
        if "checkpoint" in state:
            graph = deepcopy(state["checkpoint"])
        else:
            parent = state.get("parent")
            if parent not in graphs:
                raise ValueError(
                    f"missing materialized parent {parent!r} for {sha}"
                )
            graph = apply_graph_patch(
                graphs[parent],
                state["patch"],
            )
            graph["graph_id"] = state["patch"].get("graph_id")

        graphs[sha] = graph
        snapshots.append(
            {
                "commit": sha,
                "graph": deepcopy(graph),
                "parent_deltas": deepcopy(
                    state.get("parent_deltas", {})
                ),
            }
        )

    result = {
        "schema": EXPANDED_SCHEMA,
        "commits": deepcopy(compact.get("commits", [])),
        "refs": deepcopy(compact.get("refs", {})),
        "branch_episodes": deepcopy(
            compact.get("branch_episodes", [])
        ),
        "snapshots": snapshots,
    }
    if "pull_requests" in compact:
        result["pull_requests"] = deepcopy(
            compact.get("pull_requests", [])
        )
    return result


def load_history_file(path: str | Path) -> dict[str, Any]:
    data = json.loads(
        Path(path).read_text(encoding="utf-8")
    )
    if data.get("schema") == COMPACT_SCHEMA:
        return expand_timeline(data)
    if data.get("schema") == EXPANDED_SCHEMA:
        return data
    raise ValueError(
        f"unsupported history schema: {data.get('schema')!r}"
    )
