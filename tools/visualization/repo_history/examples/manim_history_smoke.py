from __future__ import annotations

import json
import os
from datetime import datetime, timezone
from pathlib import Path

import numpy as np
from manim import (
    BLUE,
    GREY_B,
    WHITE,
    Create,
    Dot,
    FadeIn,
    Line,
    MovingCameraScene,
    Text,
    VGroup,
)


def _time_layout(commits, *, y_min=-3.2, y_max=3.0):
    timestamps = [int(commit["timestamp"]) for commit in commits]
    lo = min(timestamps)
    hi = max(timestamps)

    if hi <= lo:
        ys = {commit["commit"]: 0.0 for commit in commits}
    else:
        ys = {
            commit["commit"]: y_min
            + (int(commit["timestamp"]) - lo)
            / (hi - lo)
            * (y_max - y_min)
            for commit in commits
        }

    lane = {}
    next_lane = 1
    children = {}
    known = {commit["commit"] for commit in commits}
    for commit in commits:
        for parent in commit.get("parents", []):
            if parent in known:
                children.setdefault(parent, []).append(commit["commit"])

    for commit in commits:
        sha = commit["commit"]
        parents = [p for p in commit.get("parents", []) if p in lane]
        if not parents:
            lane[sha] = 0
            continue
        primary = parents[0]
        lane[sha] = lane[primary]
        siblings = children.get(primary, [])
        if len(siblings) > 1 and siblings.index(sha) > 0:
            lane[sha] = next_lane
            next_lane += 1

    values = list(lane.values()) or [0]
    centre = (min(values) + max(values)) / 2
    return {
        commit["commit"]: np.array(
            [
                (lane[commit["commit"]] - centre) * 0.9,
                ys[commit["commit"]],
                0.0,
            ]
        )
        for commit in commits
    }


class DashiRepositoryHistorySmoke(MovingCameraScene):
    """Minimal real-Manim repository-history render.

    Input:
      DASHI_REPO_HISTORY_JSON=/path/to/dashi.repo-history.v1.json
    """

    def construct(self):
        path = os.environ["DASHI_REPO_HISTORY_JSON"]
        data = json.loads(Path(path).read_text(encoding="utf-8"))
        commits = data.get("commits", [])
        if not commits:
            self.add(Text("No commits", font_size=32))
            return

        positions = _time_layout(commits)
        commit_ids = {commit["commit"] for commit in commits}
        by_sha = {commit["commit"]: commit for commit in commits}

        title = Text(
            "dashi_agda · repository evolution",
            font_size=28,
        ).to_edge(np.array([0.0, 1.0, 0.0]))
        subtitle = Text(
            "vertical position = real commit time · horizontal = branch lane",
            font_size=15,
        ).next_to(title, np.array([0.0, -1.0, 0.0]), buff=0.10)
        self.play(FadeIn(title), FadeIn(subtitle), run_time=0.4)

        t0 = min(int(commit["timestamp"]) for commit in commits)
        t1 = max(int(commit["timestamp"]) for commit in commits)

        axis_x = min(point[0] for point in positions.values()) - 1.25
        y0 = min(point[1] for point in positions.values())
        y1 = max(point[1] for point in positions.values())
        axis = Line(
            np.array([axis_x, y0, 0.0]),
            np.array([axis_x, y1, 0.0]),
            stroke_width=1.5,
            color=GREY_B,
        )
        axis_group = VGroup(axis)
        for index in range(6):
            ts = int(t0 + (t1 - t0) * index / 5) if t1 > t0 else t0
            y = y0 + (y1 - y0) * index / 5 if y1 > y0 else y0
            tick = Line(
                np.array([axis_x - 0.07, y, 0.0]),
                np.array([axis_x + 0.07, y, 0.0]),
                stroke_width=1.5,
                color=GREY_B,
            )
            label = Text(
                datetime.fromtimestamp(ts, timezone.utc).strftime(
                    "%Y-%m-%d\n%H:%M:%S UTC"
                ),
                font_size=10,
            ).next_to(tick, np.array([-1.0, 0.0, 0.0]), buff=0.05)
            axis_group.add(tick, label)
        self.play(Create(axis), FadeIn(axis_group[1:]), run_time=0.5)

        dots = {}
        edges = VGroup()
        for commit in commits:
            sha = commit["commit"]
            dot = Dot(
                positions[sha],
                radius=0.055,
                color=BLUE,
            )
            dots[sha] = dot

            new_edges = []
            for parent in commit.get("parents", []):
                if parent not in commit_ids or parent not in dots:
                    continue
                edge = Line(
                    dots[parent].get_center(),
                    dot.get_center(),
                    stroke_width=1.6,
                    color=GREY_B,
                )
                edges.add(edge)
                new_edges.append(Create(edge))

            animations = [FadeIn(dot)]
            animations.extend(new_edges)
            self.play(*animations, run_time=0.06)

        latest = commits[-1]
        stamp = Text(
            f"{latest['commit'][:10]} · "
            + datetime.fromtimestamp(
                int(latest["timestamp"]),
                timezone.utc,
            ).strftime("%Y-%m-%d %H:%M:%S UTC"),
            font_size=13,
            color=WHITE,
        ).to_edge(np.array([0.0, -1.0, 0.0]))
        self.play(FadeIn(stamp), run_time=0.3)

        graph_group = VGroup(axis_group, edges, *dots.values())
        self.play(
            self.camera.frame.animate.move_to(graph_group).set(
                width=max(9.5, graph_group.width + 2.2)
            ),
            run_time=0.7,
        )
        self.wait(1)
