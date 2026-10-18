from __future__ import annotations

from collections import deque
from .model import BranchEpisode, CommitRecord


def _ancestor_distances(
    start: str,
    parents: dict[str, tuple[str, ...]],
) -> dict[str, int]:
    distance = {start: 0}
    queue = deque([start])
    while queue:
        current = queue.popleft()
        next_distance = distance[current] + 1
        for parent in parents.get(current, ()):
            if parent not in distance or next_distance < distance[parent]:
                distance[parent] = next_distance
                queue.append(parent)
    return distance


def nearest_common_ancestor(
    left: str,
    right: str,
    parents: dict[str, tuple[str, ...]],
) -> str | None:
    left_distance = _ancestor_distances(left, parents)
    right_distance = _ancestor_distances(right, parents)
    common = set(left_distance) & set(right_distance)
    if not common:
        return None

    return min(
        common,
        key=lambda commit: (
            max(left_distance[commit], right_distance[commit]),
            left_distance[commit] + right_distance[commit],
            commit,
        ),
    )


def _shortest_parent_path(
    tip: str,
    base: str,
    parents: dict[str, tuple[str, ...]],
) -> tuple[str, ...]:
    if tip == base:
        return (base,)

    queue = deque([(tip, (tip,))])
    seen = {tip}
    while queue:
        current, path = queue.popleft()
        for parent in parents.get(current, ()):
            if parent == base:
                return tuple(reversed(path + (base,)))
            if parent not in seen:
                seen.add(parent)
                queue.append((parent, path + (parent,)))
    return ()


def derive_branch_episodes(
    commits: list[CommitRecord],
    *,
    merge_commits: set[str] | None = None,
) -> list[BranchEpisode]:
    """Recover branch episodes, optionally only for named merge commits.

    ``commits`` must still contain the complete DAG needed to trace each
    requested merge's parents back to its fork base.  Limiting the merge set is
    important for timeline windows: a short recent window should not calculate
    ancestry paths for every historical merge in the repository.
    """
    parents = {
        commit.commit: commit.parents
        for commit in commits
    }
    known = set(parents)
    episodes: list[BranchEpisode] = []

    for commit in commits:
        if merge_commits is not None and commit.commit not in merge_commits:
            continue
        merge_parents = [
            parent
            for parent in commit.parents
            if parent in known
        ]
        if len(merge_parents) < 2:
            continue

        left, right = merge_parents[:2]
        base = nearest_common_ancestor(left, right, parents)
        if base is None:
            continue

        left_path = _shortest_parent_path(left, base, parents)
        right_path = _shortest_parent_path(right, base, parents)
        if not left_path or not right_path:
            continue

        episodes.append(
            BranchEpisode(
                fork_base=base,
                left_tip=left,
                right_tip=right,
                merge_commit=commit.commit,
                left_path=left_path,
                right_path=right_path,
            )
        )

    return episodes
