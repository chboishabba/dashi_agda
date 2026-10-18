from __future__ import annotations

from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class MergeAttribution:
    merge_commit: str
    parents: tuple[str, ...]
    common_nodes: tuple[str, ...]
    parent_only_nodes: dict[str, tuple[str, ...]]
    introduced_nodes: tuple[str, ...]
    removed_nodes: dict[str, tuple[str, ...]]
    common_edges: tuple[str, ...]
    parent_only_edges: dict[str, tuple[str, ...]]
    introduced_edges: tuple[str, ...]
    removed_edges: dict[str, tuple[str, ...]]


def _ids(snapshot: dict[str, Any], key: str, id_key: str) -> set[str]:
    return {item[id_key] for item in snapshot["graph"][key]}


def attribute_merge(
    *,
    merge_commit: dict[str, Any],
    snapshots_by_commit: dict[str, dict[str, Any]],
) -> MergeAttribution:
    merge_sha = merge_commit["commit"]
    parents = tuple(
        p for p in merge_commit["parents"] if p in snapshots_by_commit
    )
    if len(parents) < 2:
        raise ValueError("merge attribution requires at least two available parents")

    merge_snapshot = snapshots_by_commit[merge_sha]
    merge_nodes = _ids(merge_snapshot, "nodes", "symbol_id")
    merge_edges = _ids(merge_snapshot, "edges", "relation_id")

    parent_nodes = {
        p: _ids(snapshots_by_commit[p], "nodes", "symbol_id")
        for p in parents
    }
    parent_edges = {
        p: _ids(snapshots_by_commit[p], "edges", "relation_id")
        for p in parents
    }

    common_parent_nodes = set.intersection(*(parent_nodes[p] for p in parents))
    common_parent_edges = set.intersection(*(parent_edges[p] for p in parents))

    parent_only_nodes: dict[str, tuple[str, ...]] = {}
    parent_only_edges: dict[str, tuple[str, ...]] = {}
    removed_nodes: dict[str, tuple[str, ...]] = {}
    removed_edges: dict[str, tuple[str, ...]] = {}

    for parent in parents:
        others_nodes = set().union(
            *(parent_nodes[p] for p in parents if p != parent)
        )
        others_edges = set().union(
            *(parent_edges[p] for p in parents if p != parent)
        )
        parent_only_nodes[parent] = tuple(
            sorted((parent_nodes[parent] - others_nodes) & merge_nodes)
        )
        parent_only_edges[parent] = tuple(
            sorted((parent_edges[parent] - others_edges) & merge_edges)
        )
        removed_nodes[parent] = tuple(
            sorted(parent_nodes[parent] - merge_nodes)
        )
        removed_edges[parent] = tuple(
            sorted(parent_edges[parent] - merge_edges)
        )

    any_parent_nodes = set().union(*(parent_nodes[p] for p in parents))
    any_parent_edges = set().union(*(parent_edges[p] for p in parents))

    return MergeAttribution(
        merge_commit=merge_sha,
        parents=parents,
        common_nodes=tuple(sorted(common_parent_nodes & merge_nodes)),
        parent_only_nodes=parent_only_nodes,
        introduced_nodes=tuple(sorted(merge_nodes - any_parent_nodes)),
        removed_nodes=removed_nodes,
        common_edges=tuple(sorted(common_parent_edges & merge_edges)),
        parent_only_edges=parent_only_edges,
        introduced_edges=tuple(sorted(merge_edges - any_parent_edges)),
        removed_edges=removed_edges,
    )
