from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .merge_attribution import attribute_merge


NODE_WEIGHT = 5
EDGE_WEIGHT = 1
STEP_WEIGHT = 1
MERGE_ONLY_NODE_BONUS = 3
MERGE_ONLY_EDGE_BONUS = 1


@dataclass(frozen=True)
class EpisodeSalience:
    episode_index: int
    score: int
    branch_node_churn: int
    branch_edge_churn: int
    merge_only_nodes: int
    merge_only_edges: int
    branch_steps: int


def _delta_churn(delta: dict[str, Any]) -> tuple[int, int]:
    node_churn = (
        len(delta.get("added_nodes", []))
        + len(delta.get("removed_nodes", []))
    )
    edge_churn = (
        len(delta.get("added_edges", []))
        + len(delta.get("removed_edges", []))
    )
    return node_churn, edge_churn


def score_episode(
    timeline: dict[str, Any],
    episode_index: int,
) -> EpisodeSalience:
    episodes = timeline.get("branch_episodes", [])
    episode = episodes[episode_index]

    commits = {
        commit["commit"]: commit
        for commit in timeline.get("commits", [])
    }
    snapshots = {
        snapshot["commit"]: snapshot
        for snapshot in timeline.get("snapshots", [])
    }

    branch_node_churn = 0
    branch_edge_churn = 0
    branch_steps = 0

    for path_name in ("left_path", "right_path"):
        path = list(episode.get(path_name, []))
        for parent, child in zip(path, path[1:]):
            child_snapshot = snapshots.get(child)
            if child_snapshot is None:
                continue
            delta = child_snapshot.get("parent_deltas", {}).get(parent)
            if delta is None:
                continue
            nodes, edges = _delta_churn(delta)
            branch_node_churn += nodes
            branch_edge_churn += edges
            branch_steps += 1

    merge_only_nodes = 0
    merge_only_edges = 0
    merge_sha = episode["merge_commit"]
    left = episode["left_tip"]
    right = episode["right_tip"]

    if (
        merge_sha in commits
        and merge_sha in snapshots
        and left in snapshots
        and right in snapshots
    ):
        attribution = attribute_merge(
            merge_commit=commits[merge_sha],
            snapshots_by_commit=snapshots,
        )
        merge_only_nodes = len(attribution.introduced_nodes)
        merge_only_edges = len(attribution.introduced_edges)

    score = (
        NODE_WEIGHT * branch_node_churn
        + EDGE_WEIGHT * branch_edge_churn
        + STEP_WEIGHT * branch_steps
        + MERGE_ONLY_NODE_BONUS * merge_only_nodes
        + MERGE_ONLY_EDGE_BONUS * merge_only_edges
    )

    return EpisodeSalience(
        episode_index=episode_index,
        score=score,
        branch_node_churn=branch_node_churn,
        branch_edge_churn=branch_edge_churn,
        merge_only_nodes=merge_only_nodes,
        merge_only_edges=merge_only_edges,
        branch_steps=branch_steps,
    )


def rank_episodes(
    timeline: dict[str, Any],
) -> list[EpisodeSalience]:
    scored = [
        score_episode(timeline, index)
        for index, _episode in enumerate(
            timeline.get("branch_episodes", [])
        )
    ]
    return sorted(
        scored,
        key=lambda item: (
            -item.score,
            item.episode_index,
        ),
    )
