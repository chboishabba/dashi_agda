from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Iterable


@dataclass(frozen=True)
class SceneCommand:
    kind: str
    payload: dict[str, Any]

    def to_dict(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "payload": self.payload,
        }


def _delta_commands(
    *,
    parent: str,
    commit: str,
    delta: dict[str, Any],
) -> list[SceneCommand]:
    commands: list[SceneCommand] = []
    for node in delta.get("removed_nodes", []):
        commands.append(
            SceneCommand(
                "remove-node",
                {"parent": parent, "commit": commit, "node": node},
            )
        )
    for edge in delta.get("removed_edges", []):
        commands.append(
            SceneCommand(
                "remove-edge",
                {"parent": parent, "commit": commit, "edge": edge},
            )
        )
    for node in delta.get("added_nodes", []):
        commands.append(
            SceneCommand(
                "add-node",
                {"parent": parent, "commit": commit, "node": node},
            )
        )
    for edge in delta.get("added_edges", []):
        commands.append(
            SceneCommand(
                "add-edge",
                {"parent": parent, "commit": commit, "edge": edge},
            )
        )
    return commands


def compile_first_parent_program(
    timeline: dict[str, Any],
    *,
    target_commit: str | None = None,
) -> list[SceneCommand]:
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
        for commit in reversed(timeline.get("commits", [])):
            if commit["commit"] in snapshots:
                target_commit = commit["commit"]
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

    commands: list[SceneCommand] = []
    if lineage:
        commands.append(
            SceneCommand(
                "show-snapshot",
                {"commit": lineage[0]},
            )
        )

    for commit in lineage[1:]:
        record = commits[commit]
        parent = next(
            (
                candidate
                for candidate in record.get("parents", [])
                if candidate in snapshots
            ),
            None,
        )
        if parent is None:
            commands.append(
                SceneCommand(
                    "show-snapshot",
                    {"commit": commit},
                )
            )
            continue

        delta = snapshots[commit].get("parent_deltas", {}).get(parent, {})
        commands.append(
            SceneCommand(
                "advance-commit",
                {"parent": parent, "commit": commit},
            )
        )
        commands.extend(
            _delta_commands(
                parent=parent,
                commit=commit,
                delta=delta,
            )
        )
        commands.append(
            SceneCommand(
                "settle-layout",
                {"commit": commit},
            )
        )

    return commands


def compile_merge_episode_program(
    timeline: dict[str, Any],
    *,
    episode_index: int,
) -> list[SceneCommand]:
    episodes = timeline.get("branch_episodes", [])
    if not episodes:
        return []
    episode = episodes[episode_index]

    left = episode["left_tip"]
    right = episode["right_tip"]
    merge = episode["merge_commit"]
    snapshots = {
        snapshot["commit"]: snapshot
        for snapshot in timeline.get("snapshots", [])
    }
    if merge not in snapshots or left not in snapshots or right not in snapshots:
        return []

    commands = [
        SceneCommand(
            "show-fork",
            {
                "fork_base": episode["fork_base"],
                "left_path": list(episode["left_path"]),
                "right_path": list(episode["right_path"]),
            },
        ),
        SceneCommand(
            "show-parent-snapshot",
            {"side": "left", "commit": left},
        ),
        SceneCommand(
            "show-parent-snapshot",
            {"side": "right", "commit": right},
        ),
    ]

    for parent in (left, right):
        delta = snapshots[merge].get("parent_deltas", {}).get(parent, {})
        commands.append(
            SceneCommand(
                "show-parent-delta",
                {
                    "parent": parent,
                    "merge": merge,
                    "delta": delta,
                },
            )
        )

    commands.append(
        SceneCommand(
            "converge-parents",
            {
                "left": left,
                "right": right,
                "merge": merge,
            },
        )
    )
    commands.append(
        SceneCommand(
            "show-snapshot",
            {"commit": merge},
        )
    )
    return commands


def serialize_program(commands: Iterable[SceneCommand]) -> list[dict[str, Any]]:
    return [command.to_dict() for command in commands]
