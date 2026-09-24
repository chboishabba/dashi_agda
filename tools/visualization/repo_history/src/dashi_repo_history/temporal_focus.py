from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .focus import FocusResult, focus_symbol, resolve_symbol
from .identity import match_node_identity


@dataclass(frozen=True)
class TemporalFocusFrame:
    commit: str
    root_id: str
    root_label: str
    root_module: str
    identity_evidence: str
    identity_confidence: str
    focus: FocusResult

    def graph(self, snapshots_by_commit: dict[str, dict[str, Any]]) -> dict[str, Any]:
        return self.focus.graph(
            snapshots_by_commit[self.commit]["graph"]
        )


def first_parent_snapshot_lineage(
    timeline: dict[str, Any],
    *,
    target_commit: str | None = None,
) -> list[dict[str, Any]]:
    commits = {
        commit["commit"]: commit
        for commit in timeline.get("commits", [])
    }
    snapshots = {
        snapshot["commit"]: snapshot
        for snapshot in timeline.get("snapshots", [])
    }
    if not snapshots:
        return []

    if target_commit is None:
        for record in reversed(timeline.get("commits", [])):
            if record["commit"] in snapshots:
                target_commit = record["commit"]
                break
    if target_commit is None or target_commit not in snapshots:
        return []

    lineage: list[str] = []
    seen: set[str] = set()
    current = target_commit

    while current in snapshots and current not in seen:
        seen.add(current)
        lineage.append(current)
        record = commits.get(current)
        if record is None:
            break

        parents = [
            parent
            for parent in record.get("parents", [])
            if parent in snapshots
        ]
        if not parents:
            break
        current = parents[0]

    lineage.reverse()
    return [snapshots[commit] for commit in lineage]


def track_symbol_history(
    timeline: dict[str, Any],
    selector: str,
    *,
    target_commit: str | None = None,
    upstream_depth: int = 2,
    downstream_depth: int = 0,
    max_nodes: int = 250,
    max_edges: int = 800,
) -> list[TemporalFocusFrame]:
    lineage = first_parent_snapshot_lineage(
        timeline,
        target_commit=target_commit,
    )
    if not lineage:
        return []

    target_snapshot = lineage[-1]
    root = resolve_symbol(target_snapshot["graph"], selector)
    current_id = root["symbol_id"]

    reversed_states: list[tuple[dict[str, Any], str]] = [
        (target_snapshot, current_id)
    ]
    transition_evidence: dict[str, tuple[str, str]] = {}

    for before, after in zip(
        reversed(lineage[:-1]),
        reversed(lineage[1:]),
    ):
        matches = match_node_identity(
            before["graph"],
            after["graph"],
        )
        candidates = [
            match
            for match in matches
            if match.new_id == current_id
            and match.confidence in {"exact", "supported"}
        ]
        if len(candidates) != 1:
            break

        match = candidates[0]
        transition_evidence[after["commit"]] = (
            match.evidence,
            match.confidence,
        )
        current_id = match.old_id
        reversed_states.append((before, current_id))

    states = list(reversed(reversed_states))
    frames: list[TemporalFocusFrame] = []

    for index, (snapshot, root_id) in enumerate(states):
        nodes = {
            node["symbol_id"]: node
            for node in snapshot["graph"].get("nodes", [])
        }
        node = nodes[root_id]
        if index == 0:
            evidence, confidence = (
                "introduction-or-earliest-match",
                "exact",
            )
        else:
            evidence, confidence = transition_evidence.get(
                snapshot["commit"],
                ("exact-semantic-key", "exact"),
            )

        focus = focus_symbol(
            snapshot["graph"],
            root_id,
            upstream_depth=upstream_depth,
            downstream_depth=downstream_depth,
            max_nodes=max_nodes,
            max_edges=max_edges,
        )
        frames.append(
            TemporalFocusFrame(
                commit=snapshot["commit"],
                root_id=root_id,
                root_label=str(node.get("label", "")),
                root_module=str(node.get("module", "")),
                identity_evidence=evidence,
                identity_confidence=confidence,
                focus=focus,
            )
        )

    return frames
