from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from typing import Any


@dataclass(frozen=True)
class TimeAxisTick:
    timestamp: int
    y: float
    label: str


@dataclass(frozen=True)
class TemporalHistoryLayout:
    positions: dict[str, tuple[float, float, float]]
    ticks: tuple[TimeAxisTick, ...]
    min_timestamp: int | None
    max_timestamp: int | None


def _branch_lanes(commits: list[dict[str, Any]]) -> dict[str, int]:
    """Assign stable horizontal lanes while preserving fork/merge topology."""

    children: dict[str, list[str]] = {}
    by_sha = {commit["commit"]: commit for commit in commits}
    for commit in commits:
        for parent in commit.get("parents", []):
            if parent in by_sha:
                children.setdefault(parent, []).append(commit["commit"])

    lanes: dict[str, int] = {}
    next_lane = 1

    for commit in commits:
        sha = commit["commit"]
        parents = [
            parent
            for parent in commit.get("parents", [])
            if parent in lanes
        ]
        if not parents:
            lane = 0
        else:
            primary = parents[0]
            lane = lanes[primary]

            siblings = children.get(primary, [])
            if len(siblings) > 1 and siblings.index(sha) > 0:
                lane = next_lane
                next_lane += 1

            if len(parents) > 1:
                lane = lanes[parents[0]]

        lanes[sha] = lane

    return lanes


def _normalized_y(
    timestamp: int,
    *,
    minimum: int,
    maximum: int,
    height: float,
) -> float:
    if maximum <= minimum:
        return 0.0
    fraction = (timestamp - minimum) / (maximum - minimum)
    return -height / 2 + fraction * height


def _tick_indices(count: int, max_ticks: int) -> list[int]:
    if count <= 0:
        return []
    if count <= max_ticks:
        return list(range(count))
    if max_ticks <= 1:
        return [count - 1]

    indices = {
        round(i * (count - 1) / (max_ticks - 1))
        for i in range(max_ticks)
    }
    return sorted(indices)


def temporal_history_layout(
    commits: list[dict[str, Any]],
    *,
    height: float = 6.2,
    lane_spacing: float = 0.95,
    max_ticks: int = 7,
) -> TemporalHistoryLayout:
    """Lay out Git history with actual time on Y and branches on X.

    Time is authoritative for the vertical coordinate. Topological order is
    used only as a deterministic epsilon tie-breaker for equal timestamps.
    """

    if not commits:
        return TemporalHistoryLayout({}, (), None, None)

    lanes = _branch_lanes(commits)
    timestamps = [int(commit["timestamp"]) for commit in commits]
    minimum = min(timestamps)
    maximum = max(timestamps)

    lane_values = list(lanes.values())
    lane_centre = (
        (min(lane_values) + max(lane_values)) / 2
        if lane_values
        else 0.0
    )

    positions: dict[str, tuple[float, float, float]] = {}
    same_timestamp_counts: dict[int, int] = {}

    for index, commit in enumerate(commits):
        sha = commit["commit"]
        timestamp = int(commit["timestamp"])
        x = (lanes[sha] - lane_centre) * lane_spacing
        y = _normalized_y(
            timestamp,
            minimum=minimum,
            maximum=maximum,
            height=height,
        )

        # Equal-second commits need a tiny deterministic separation so vertices
        # do not sit exactly on top of each other. The displacement is visual
        # only and deliberately much smaller than normal graph spacing.
        tie_index = same_timestamp_counts.get(timestamp, 0)
        same_timestamp_counts[timestamp] = tie_index + 1
        y += tie_index * 0.018

        positions[sha] = (x, y, 0.0)

    sorted_unique = sorted(set(timestamps))
    ticks: list[TimeAxisTick] = []
    previous_label: str | None = None
    for index in _tick_indices(len(sorted_unique), max_ticks):
        timestamp = sorted_unique[index]
        label = datetime.fromtimestamp(
            timestamp,
            tz=timezone.utc,
        ).strftime("%Y-%m-%d")
        if label == previous_label:
            continue
        previous_label = label
        ticks.append(
            TimeAxisTick(
                timestamp=timestamp,
                y=_normalized_y(
                    timestamp,
                    minimum=minimum,
                    maximum=maximum,
                    height=height,
                ),
                label=label,
            )
        )

    return TemporalHistoryLayout(
        positions=positions,
        ticks=tuple(ticks),
        min_timestamp=minimum,
        max_timestamp=maximum,
    )


def format_timestamp_date(timestamp: int | None) -> str:
    if timestamp is None:
        return "date unknown"
    return datetime.fromtimestamp(
        int(timestamp),
        tz=timezone.utc,
    ).strftime("%Y-%m-%d")
