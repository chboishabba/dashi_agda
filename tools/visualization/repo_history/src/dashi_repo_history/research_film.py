from __future__ import annotations

from dataclasses import asdict, dataclass
from math import ceil, sqrt
import re
from typing import Any, Iterable


TOKEN_RE = re.compile(r"[A-Z]+(?=[A-Z][a-z]|\d|\b)|[A-Z]?[a-z]+|[A-Z]+|\d+")

GENERIC_MODULE_TOKENS = frozenset(
    {
        "DASHI",
        "Core",
        "Everything",
        "Exact",
        "Synthesis",
        "Visual",
        "Formal",
        "Proof",
        "Theorem",
        "Lemma",
        "Common",
        "Util",
        "Utils",
        "Test",
        "Tests",
    }
)

PROGRAMME_ALIASES = {
    "NavierStokes": ("navier", "stokes"),
    "RiemannHypothesis": ("riemann", "zeta"),
    "YangMills": ("yang", "mills"),
    "BirchSwinnertonDyer": ("birch", "swinnerton", "dyer", "bsd"),
    "Poincare": ("poincare",),
    "Hodge": ("hodge",),
    "CookLevin": ("cook", "levin"),
    "Cuisine": ("cuisine", "food", "recipe"),
    "Antigravity": ("antigravity", "gravity"),
}


def _tokens(value: str) -> tuple[str, ...]:
    pieces: list[str] = []
    for part in re.split(r"[./:_\-]+", value):
        pieces.extend(TOKEN_RE.findall(part))
    return tuple(piece for piece in pieces if piece)


def _normalise(token: str) -> str:
    return token.casefold()


def programme_key(module: str, label: str = "") -> str:
    """Infer a stable research-programme key from semantic names.

    Aliases only normalise obvious domain spellings. Unknown programmes remain
    first-class and derive from their earliest informative module segment.
    """

    tokens = _tokens(f"{module} {label}")
    lowered = tuple(_normalise(token) for token in tokens)

    for canonical, aliases in PROGRAMME_ALIASES.items():
        if any(alias in lowered for alias in aliases):
            return canonical

    module_parts = [
        part
        for part in module.split(".")
        if part and part not in GENERIC_MODULE_TOKENS
    ]
    if module_parts:
        # Prefer the first semantically informative namespace. Physics/Math are
        # category shelves, so one more segment is usually more explanatory.
        shelves = {"Physics", "Math", "Mathematics", "Arithmetic", "Research"}
        first = module_parts[0]
        if first in shelves and len(module_parts) > 1:
            return module_parts[1]
        return first

    informative = [
        token
        for token in tokens
        if token not in GENERIC_MODULE_TOKENS
    ]
    return informative[0] if informative else "Unclassified"


def _topic_tokens(nodes: Iterable[dict[str, Any]]) -> tuple[str, ...]:
    counts: dict[str, int] = {}
    for node in nodes:
        for token in _tokens(str(node.get("label", ""))):
            lower = _normalise(token)
            if len(lower) < 3 or token in GENERIC_MODULE_TOKENS:
                continue
            counts[lower] = counts.get(lower, 0) + 1

    ranked = sorted(
        counts,
        key=lambda token: (-counts[token], token),
    )
    return tuple(ranked[:4])


LANE_RE = re.compile(
    r"(?:^|[^A-Za-z0-9])(?:lane|route|goal)?[-_ ]*([ABCD])(?:\d+)?(?:$|[^A-Za-z0-9])",
    re.IGNORECASE,
)


def _lane_hint(nodes: Iterable[dict[str, Any]]) -> str | None:
    scores: dict[str, int] = {}
    for node in nodes:
        haystack = " ".join(
            [
                str(node.get("module", "")),
                str(node.get("label", "")),
                str(node.get("span", {}).get("path", "")),
            ]
        )
        for match in LANE_RE.finditer(haystack):
            lane = match.group(1).upper()
            scores[lane] = scores.get(lane, 0) + 1
    if not scores:
        return None
    return min(
        scores,
        key=lambda lane: (-scores[lane], lane),
    )


def _symbol_summary(
    nodes: Iterable[dict[str, Any]],
    *,
    limit: int = 6,
) -> tuple[tuple[str, str, str], ...]:
    ranked = sorted(
        nodes,
        key=lambda node: (
            0 if node.get("kind") in {"theorem", "function", "postulate"} else 1,
            0 if node.get("scope") is None else 1,
            str(node.get("module", "")),
            str(node.get("label", "")),
        ),
    )
    return tuple(
        (
            str(node.get("label", "")),
            str(node.get("kind", "")),
            str(node.get("module", "")),
        )
        for node in ranked[:limit]
    )


def _headline(
    programme: str,
    symbols: tuple[tuple[str, str, str], ...],
    topics: tuple[str, ...],
    lane: str | None,
) -> str:
    prefix = programme
    if lane:
        prefix += f" · Lane {lane}"

    labels = [label for label, _kind, _module in symbols if label]
    if labels:
        shown = " → ".join(labels[:3])
        if len(labels) > 3:
            shown += f" +{len(labels) - 3}"
        return f"{prefix} · {shown}"

    if topics:
        return f"{prefix} · {' · '.join(topics[:3])}"
    return f"{prefix} · formal development"


@dataclass(frozen=True)
class ActiveWorkingSet:
    commit: str
    programme: str
    topic_tokens: tuple[str, ...]
    changed_node_ids: tuple[str, ...]
    changed_edge_ids: tuple[str, ...]
    context_node_ids: tuple[str, ...]
    context_edge_ids: tuple[str, ...]
    salience: int
    modules: tuple[str, ...] = ()
    changed_symbols: tuple[tuple[str, str, str], ...] = ()
    lane: str | None = None
    headline: str = ""

    @property
    def focus_node_ids(self) -> tuple[str, ...]:
        return tuple(
            dict.fromkeys(
                (*self.changed_node_ids, *self.context_node_ids)
            )
        )

    @property
    def focus_edge_ids(self) -> tuple[str, ...]:
        return tuple(
            dict.fromkeys(
                (*self.changed_edge_ids, *self.context_edge_ids)
            )
        )


@dataclass(frozen=True)
class SemanticEpisode:
    programme: str
    topic_tokens: tuple[str, ...]
    commits: tuple[str, ...]
    started_at: int
    ended_at: int
    focus_node_ids: tuple[str, ...]
    focus_edge_ids: tuple[str, ...]
    salience: int
    return_to_existing_region: bool


@dataclass(frozen=True)
class CameraDirective:
    programme: str
    focus_node_ids: tuple[str, ...]
    mode: str
    padding: float
    min_width: float
    max_width: float
    transition_seconds: float
    reason: str


@dataclass(frozen=True)
class ProgrammeRegion:
    programme: str
    x: float
    y: float


@dataclass(frozen=True)
class FilmBeat:
    kind: str
    commit: str | None
    programme: str | None
    topic: str | None
    duration_seconds: float
    focus_node_ids: tuple[str, ...] = ()
    focus_edge_ids: tuple[str, ...] = ()
    visible_node_ids: tuple[str, ...] = ()
    visible_edge_ids: tuple[str, ...] = ()
    camera: CameraDirective | None = None
    payload: dict[str, Any] | None = None

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        if self.camera is not None:
            value["camera"] = asdict(self.camera)
        return value


@dataclass(frozen=True)
class ResearchFilmPlan:
    regions: tuple[ProgrammeRegion, ...]
    working_sets: tuple[ActiveWorkingSet, ...]
    episodes: tuple[SemanticEpisode, ...]
    beats: tuple[FilmBeat, ...]

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": "dashi.research-film.v1",
            "regions": [asdict(region) for region in self.regions],
            "working_sets": [asdict(item) for item in self.working_sets],
            "episodes": [asdict(item) for item in self.episodes],
            "beats": [beat.to_dict() for beat in self.beats],
        }


def _node_maps(snapshot: dict[str, Any]) -> tuple[
    dict[str, dict[str, Any]],
    dict[str, dict[str, Any]],
]:
    graph = snapshot["graph"]
    return (
        {
            node["symbol_id"]: node
            for node in graph.get("nodes", [])
        },
        {
            edge["relation_id"]: edge
            for edge in graph.get("edges", [])
        },
    )


def _changed_payload_ids(
    parent_snapshot: dict[str, Any] | None,
    snapshot: dict[str, Any],
    parent: str | None,
) -> tuple[set[str], set[str]]:
    changed_nodes: set[str] = set()
    changed_edges: set[str] = set()

    if parent is not None:
        delta = snapshot.get("parent_deltas", {}).get(parent, {})
        changed_nodes.update(delta.get("added_nodes", []))
        changed_nodes.update(delta.get("removed_nodes", []))
        changed_edges.update(delta.get("added_edges", []))
        changed_edges.update(delta.get("removed_edges", []))

    if parent_snapshot is None:
        nodes, edges = _node_maps(snapshot)
        return set(nodes), set(edges)

    before_nodes, before_edges = _node_maps(parent_snapshot)
    after_nodes, after_edges = _node_maps(snapshot)

    # Same semantic identity may still have changed payload/fingerprint/span.
    for node_id in before_nodes.keys() & after_nodes.keys():
        if before_nodes[node_id] != after_nodes[node_id]:
            changed_nodes.add(node_id)
    for edge_id in before_edges.keys() & after_edges.keys():
        if before_edges[edge_id] != after_edges[edge_id]:
            changed_edges.add(edge_id)

    return changed_nodes, changed_edges


def _working_sets_for_commit(
    *,
    commit: dict[str, Any],
    snapshot: dict[str, Any],
    parent_snapshot: dict[str, Any] | None,
    parent: str | None,
    max_context_nodes: int,
    max_context_edges: int,
) -> list[ActiveWorkingSet]:
    after_nodes, after_edges = _node_maps(snapshot)
    before_nodes, before_edges = (
        _node_maps(parent_snapshot)
        if parent_snapshot is not None
        else ({}, {})
    )
    changed_nodes, changed_edges = _changed_payload_ids(
        parent_snapshot,
        snapshot,
        parent,
    )

    all_nodes = {**before_nodes, **after_nodes}
    all_edges = {**before_edges, **after_edges}

    # Pull endpoints for relation-only additions/removals.
    for edge_id in list(changed_edges):
        edge = all_edges.get(edge_id)
        if edge is None:
            continue
        changed_nodes.update((edge["source"], edge["target"]))

    programme_nodes: dict[str, set[str]] = {}
    for node_id in sorted(changed_nodes):
        node = all_nodes.get(node_id)
        if node is None:
            continue
        programme = programme_key(
            str(node.get("module", "")),
            str(node.get("label", "")),
        )
        programme_nodes.setdefault(programme, set()).add(node_id)

    if not programme_nodes:
        programme_nodes["Unclassified"] = set(changed_nodes)

    programme_edges: dict[str, set[str]] = {
        programme: set()
        for programme in programme_nodes
    }
    for edge_id in changed_edges:
        edge = all_edges.get(edge_id)
        if edge is None:
            continue
        endpoint_programmes = set()
        for endpoint in (edge["source"], edge["target"]):
            node = all_nodes.get(endpoint)
            if node is None:
                continue
            endpoint_programmes.add(
                programme_key(
                    str(node.get("module", "")),
                    str(node.get("label", "")),
                )
            )
        for programme in endpoint_programmes or {"Unclassified"}:
            programme_edges.setdefault(programme, set()).add(edge_id)
            programme_nodes.setdefault(programme, set())

    working_sets: list[ActiveWorkingSet] = []
    candidates = sorted(
        all_edges.values(),
        key=lambda edge: (
            edge.get("kind", ""),
            edge["source"],
            edge["target"],
            edge["relation_id"],
        ),
    )

    for programme in sorted(programme_nodes):
        local_changed = programme_nodes[programme]
        local_edges = programme_edges.get(programme, set())
        payloads = [
            all_nodes[node_id]
            for node_id in sorted(local_changed)
            if node_id in all_nodes
        ]
        topics = _topic_tokens(payloads)
        modules = tuple(
            sorted(
                {
                    str(node.get("module", ""))
                    for node in payloads
                    if node.get("module")
                }
            )
        )
        symbols = _symbol_summary(payloads)
        lane = _lane_hint(payloads)
        headline = _headline(
            programme,
            symbols,
            topics,
            lane,
        )

        context_nodes: set[str] = set()
        context_edges: set[str] = set()
        for edge in candidates:
            if (
                edge["source"] not in local_changed
                and edge["target"] not in local_changed
            ):
                continue
            if len(context_edges) >= max_context_edges:
                break

            additions = {
                endpoint
                for endpoint in (edge["source"], edge["target"])
                if endpoint not in local_changed
                and endpoint not in context_nodes
            }
            if len(context_nodes) + len(additions) > max_context_nodes:
                continue

            context_edges.add(edge["relation_id"])
            context_nodes.update(additions)

        salience = (
            6 * len(local_changed)
            + 2 * len(local_edges)
            + len(context_nodes)
        )
        if len(commit.get("parents", [])) > 1:
            salience += 20

        working_sets.append(
            ActiveWorkingSet(
                commit=commit["commit"],
                programme=programme,
                topic_tokens=topics,
                changed_node_ids=tuple(sorted(local_changed)),
                changed_edge_ids=tuple(sorted(local_edges)),
                context_node_ids=tuple(sorted(context_nodes)),
                context_edge_ids=tuple(sorted(context_edges)),
                salience=salience,
                modules=modules,
                changed_symbols=symbols,
                lane=lane,
                headline=headline,
            )
        )

    return working_sets


def derive_working_sets(
    timeline: dict[str, Any],
    *,
    max_context_nodes: int = 40,
    max_context_edges: int = 100,
) -> list[ActiveWorkingSet]:
    commits = timeline.get("commits", [])
    snapshots = {
        snapshot["commit"]: snapshot
        for snapshot in timeline.get("snapshots", [])
    }
    working_sets: list[ActiveWorkingSet] = []

    for commit in commits:
        sha = commit["commit"]
        snapshot = snapshots.get(sha)
        if snapshot is None:
            continue

        parent = next(
            (
                candidate
                for candidate in commit.get("parents", [])
                if candidate in snapshots
            ),
            None,
        )
        parent_snapshot = snapshots.get(parent) if parent else None

        # A selected history window often begins from a materialized checkpoint
        # whose real parent lies outside the window. Existing declarations in
        # that snapshot are baseline context, not thousands of simultaneous
        # proof-production events.
        if parent is None and commit.get("parents"):
            continue

        working_sets.extend(
            _working_sets_for_commit(
                commit=commit,
                snapshot=snapshot,
                parent_snapshot=parent_snapshot,
                parent=parent,
                max_context_nodes=max_context_nodes,
                max_context_edges=max_context_edges,
            )
        )

    return working_sets


def _topic_similarity(
    left: tuple[str, ...],
    right: tuple[str, ...],
) -> float:
    a, b = set(left), set(right)
    if not a and not b:
        return 1.0
    if not a or not b:
        return 0.0
    return len(a & b) / len(a | b)


def derive_episodes(
    timeline: dict[str, Any],
    working_sets: list[ActiveWorkingSet],
    *,
    max_gap_seconds: int = 6 * 60 * 60,
    topic_similarity_threshold: float = 0.20,
) -> list[SemanticEpisode]:
    commits = {
        commit["commit"]: commit
        for commit in timeline.get("commits", [])
    }

    episodes: list[SemanticEpisode] = []
    current: list[ActiveWorkingSet] = []
    seen_programmes: set[str] = set()

    def flush() -> None:
        nonlocal current
        if not current:
            return

        programme = current[0].programme
        timestamps = [
            int(commits[item.commit]["timestamp"])
            for item in current
        ]
        topic_counts: dict[str, int] = {}
        for item in current:
            for token in item.topic_tokens:
                topic_counts[token] = topic_counts.get(token, 0) + 1
        topics = tuple(
            sorted(
                topic_counts,
                key=lambda token: (-topic_counts[token], token),
            )[:5]
        )
        focus_nodes = tuple(
            dict.fromkeys(
                node
                for item in current
                for node in item.focus_node_ids
            )
        )
        focus_edges = tuple(
            dict.fromkeys(
                edge
                for item in current
                for edge in item.focus_edge_ids
            )
        )

        episodes.append(
            SemanticEpisode(
                programme=programme,
                topic_tokens=topics,
                commits=tuple(item.commit for item in current),
                started_at=min(timestamps),
                ended_at=max(timestamps),
                focus_node_ids=focus_nodes,
                focus_edge_ids=focus_edges,
                salience=sum(item.salience for item in current),
                return_to_existing_region=programme in seen_programmes,
            )
        )
        seen_programmes.add(programme)
        current = []

    for working_set in working_sets:
        if not current:
            current = [working_set]
            continue

        previous = current[-1]
        gap = (
            int(commits[working_set.commit]["timestamp"])
            - int(commits[previous.commit]["timestamp"])
        )
        compatible = (
            previous.programme == working_set.programme
            and gap <= max_gap_seconds
            and _topic_similarity(
                previous.topic_tokens,
                working_set.topic_tokens,
            )
            >= topic_similarity_threshold
        )

        if compatible:
            current.append(working_set)
        else:
            flush()
            current = [working_set]

    flush()
    return episodes


def programme_regions(
    programmes: Iterable[str],
    *,
    spacing_x: float = 15.0,
    spacing_y: float = 9.0,
) -> tuple[ProgrammeRegion, ...]:
    programmes = sorted(set(programmes))
    if not programmes:
        return ()

    columns = max(1, ceil(sqrt(len(programmes))))
    rows = max(1, ceil(len(programmes) / columns))
    regions: list[ProgrammeRegion] = []

    for index, programme in enumerate(programmes):
        col = index % columns
        row = index // columns
        x = (col - (columns - 1) / 2) * spacing_x
        y = ((rows - 1) / 2 - row) * spacing_y
        regions.append(
            ProgrammeRegion(programme=programme, x=x, y=y)
        )
    return tuple(regions)


def _episode_duration(episode: SemanticEpisode) -> float:
    commit_count = len(episode.commits)
    if episode.salience >= 120:
        return min(8.0, 3.0 + 0.30 * commit_count)
    if episode.salience >= 50:
        return min(5.0, 2.0 + 0.22 * commit_count)
    return min(3.0, 1.1 + 0.15 * commit_count)


def _working_set_duration(
    working: ActiveWorkingSet,
    *,
    pace_scale: float,
) -> float:
    """Reading/reveal time for one semantic change.

    Camera travel has its own timing. This duration grows with semantic density
    so a dense proof-construction cluster is readable instead of flashing by.
    """

    changed = len(working.changed_node_ids)
    relations = len(working.changed_edge_ids)
    context = len(working.context_node_ids)
    symbols = len(working.changed_symbols)

    seconds = (
        0.80
        + 0.16 * min(changed, 12)
        + 0.035 * min(relations, 30)
        + 0.025 * min(context, 24)
        + 0.08 * min(symbols, 6)
    )
    return max(0.70, min(4.8, seconds * max(0.25, pace_scale)))


def compile_research_film(
    timeline: dict[str, Any],
    *,
    max_context_nodes: int = 40,
    max_context_edges: int = 100,
    programme_memory_nodes: int = 28,
    pace_scale: float = 1.0,
) -> ResearchFilmPlan:
    working_sets = derive_working_sets(
        timeline,
        max_context_nodes=max_context_nodes,
        max_context_edges=max_context_edges,
    )
    episodes = derive_episodes(timeline, working_sets)
    regions = programme_regions(
        episode.programme
        for episode in episodes
    )

    beats: list[FilmBeat] = []
    previous_programme: str | None = None
    programme_memory: dict[str, list[str]] = {}
    working_by_commit: dict[str, list[ActiveWorkingSet]] = {}
    for working in working_sets:
        working_by_commit.setdefault(working.commit, []).append(working)
    emitted_multi_overviews: set[str] = set()
    prs_by_merge = {
        pr.get("merge_commit"): pr
        for pr in timeline.get("pull_requests", [])
        if pr.get("merge_commit")
    }
    forks_by_commit: dict[str, list[dict[str, Any]]] = {}
    merges_by_commit: dict[str, list[dict[str, Any]]] = {}
    for branch_episode in timeline.get("branch_episodes", []):
        forks_by_commit.setdefault(
            branch_episode["fork_base"], []
        ).append(branch_episode)
        merges_by_commit.setdefault(
            branch_episode["merge_commit"], []
        ).append(branch_episode)

    for episode in episodes:
        first_commit = episode.commits[0]
        topic = " · ".join(episode.topic_tokens) or "formal development"
        return_visit = (
            episode.return_to_existing_region
            and previous_programme != episode.programme
        )

        camera = CameraDirective(
            programme=episode.programme,
            focus_node_ids=episode.focus_node_ids,
            mode="fit-active",
            padding=1.18,
            min_width=6.5,
            max_width=24.0,
            transition_seconds=(
                1.25 if return_visit else 0.85
            ),
            reason=(
                "return-to-existing-programme"
                if return_visit
                else "active-semantic-working-set"
            ),
        )

        beats.append(
            FilmBeat(
                kind="episode-title",
                commit=first_commit,
                programme=episode.programme,
                topic=topic,
                duration_seconds=0.45,
                focus_node_ids=episode.focus_node_ids,
                focus_edge_ids=episode.focus_edge_ids,
                camera=camera,
                payload={
                    "commits": list(episode.commits),
                    "return_visit": return_visit,
                    "salience": episode.salience,
                    "headline": next(
                        (
                            item.headline
                            for item in working_sets
                            if item.commit == first_commit
                            and item.programme == episode.programme
                        ),
                        topic,
                    ),
                },
            )
        )

        for commit in episode.commits:
            working = next(
                item
                for item in working_sets
                if item.commit == commit
                and item.programme == episode.programme
            )

            simultaneous = working_by_commit.get(commit, [])
            if (
                len(simultaneous) > 1
                and commit not in emitted_multi_overviews
            ):
                emitted_multi_overviews.add(commit)
                overview_nodes = tuple(
                    dict.fromkeys(
                        node
                        for item in simultaneous
                        for node in item.focus_node_ids
                    )
                )
                overview_edges = tuple(
                    dict.fromkeys(
                        edge
                        for item in simultaneous
                        for edge in item.focus_edge_ids
                    )
                )
                beats.append(
                    FilmBeat(
                        kind="cross-programme-overview",
                        commit=commit,
                        programme="Multiple",
                        topic=" · ".join(
                            item.programme
                            for item in simultaneous
                        ),
                        duration_seconds=0.65,
                        focus_node_ids=overview_nodes,
                        focus_edge_ids=overview_edges,
                        visible_node_ids=overview_nodes,
                        visible_edge_ids=overview_edges,
                        camera=CameraDirective(
                            programme="Multiple",
                            focus_node_ids=overview_nodes,
                            mode="programme-overview",
                            padding=1.30,
                            min_width=10.0,
                            max_width=36.0,
                            transition_seconds=0.80,
                            reason="simultaneous-multi-programme-change",
                        ),
                        payload={
                            "programmes": [
                                item.programme
                                for item in simultaneous
                            ]
                        },
                    )
                )

            for branch_episode in forks_by_commit.get(commit, []):
                beats.append(
                    FilmBeat(
                        kind="branch-fork",
                        commit=commit,
                        programme=working.programme,
                        topic="branch split",
                        duration_seconds=0.45,
                        focus_node_ids=working.focus_node_ids,
                        focus_edge_ids=working.focus_edge_ids,
                        camera=CameraDirective(
                            programme=working.programme,
                            focus_node_ids=working.focus_node_ids,
                            mode="fit-active",
                            padding=1.25,
                            min_width=7.0,
                            max_width=22.0,
                            transition_seconds=0.55,
                            reason="branch-fork-context",
                        ),
                        payload=dict(branch_episode),
                    )
                )

            memory = programme_memory.setdefault(
                working.programme,
                [],
            )
            for node_id in (
                *working.changed_node_ids,
                *working.context_node_ids,
            ):
                if node_id in memory:
                    memory.remove(node_id)
                memory.append(node_id)
            if len(memory) > programme_memory_nodes:
                del memory[:-programme_memory_nodes]

            visible_nodes = tuple(
                dict.fromkeys(
                    (
                        *memory,
                        *working.focus_node_ids,
                    )
                )
            )

            visible_node_set = set(visible_nodes)
            snapshot = next(
                (
                    item
                    for item in timeline.get("snapshots", [])
                    if item["commit"] == commit
                ),
                None,
            )
            visible_edges: tuple[str, ...] = ()
            if snapshot is not None:
                visible_edges = tuple(
                    edge["relation_id"]
                    for edge in snapshot["graph"].get("edges", [])
                    if edge["source"] in visible_node_set
                    and edge["target"] in visible_node_set
                )

            beats.append(
                FilmBeat(
                    kind="semantic-change",
                    commit=commit,
                    programme=working.programme,
                    topic=" · ".join(working.topic_tokens),
                    duration_seconds=max(
                        _episode_duration(episode)
                        / max(1, len(episode.commits)),
                        _working_set_duration(
                            working,
                            pace_scale=pace_scale,
                        ),
                    ),
                    focus_node_ids=working.focus_node_ids,
                    focus_edge_ids=working.focus_edge_ids,
                    visible_node_ids=visible_nodes,
                    visible_edge_ids=visible_edges,
                    camera=CameraDirective(
                        programme=working.programme,
                        focus_node_ids=working.focus_node_ids,
                        mode="fit-active",
                        padding=1.15,
                        min_width=5.5,
                        max_width=20.0,
                        transition_seconds=0.45,
                        reason="commit-active-working-set",
                    ),
                    payload={
                        "salience": working.salience,
                        "changed_nodes": list(
                            working.changed_node_ids
                        ),
                        "changed_edges": list(
                            working.changed_edge_ids
                        ),
                        "changed_symbols": [
                            {
                                "label": label,
                                "kind": kind,
                                "module": module,
                            }
                            for label, kind, module
                            in working.changed_symbols
                        ],
                        "modules": list(working.modules),
                        "lane": working.lane,
                        "headline": working.headline,
                        "commit_subject": str(
                            next(
                                (
                                    item.get("subject", "")
                                    for item in timeline.get("commits", [])
                                    if item["commit"] == commit
                                ),
                                "",
                            )
                        ),
                    },
                )
            )

            pr = prs_by_merge.get(commit)
            if pr is not None and working.focus_node_ids:
                beats.append(
                    FilmBeat(
                        kind="pr-merge",
                        commit=commit,
                        programme=working.programme,
                        topic=(
                            f"PR #{pr.get('number')} · "
                            f"{pr.get('title', '')}"
                        ),
                        duration_seconds=0.75,
                        focus_node_ids=working.focus_node_ids,
                        focus_edge_ids=working.focus_edge_ids,
                        camera=CameraDirective(
                            programme=working.programme,
                            focus_node_ids=working.focus_node_ids,
                            mode="fit-active",
                            padding=1.22,
                            min_width=7.0,
                            max_width=22.0,
                            transition_seconds=0.40,
                            reason="pull-request-merge",
                        ),
                        payload=dict(pr),
                    )
                )

            for branch_episode in merges_by_commit.get(commit, []):
                if not working.focus_node_ids:
                    continue
                beats.append(
                    FilmBeat(
                        kind="branch-merge",
                        commit=commit,
                        programme=working.programme,
                        topic="branch merge",
                        duration_seconds=0.55,
                        focus_node_ids=working.focus_node_ids,
                        focus_edge_ids=working.focus_edge_ids,
                        camera=CameraDirective(
                            programme=working.programme,
                            focus_node_ids=working.focus_node_ids,
                            mode="fit-active",
                            padding=1.28,
                            min_width=7.0,
                            max_width=24.0,
                            transition_seconds=0.50,
                            reason="branch-merge-context",
                        ),
                        payload=dict(branch_episode),
                    )
                )

        previous_programme = episode.programme

    # Branch/PR events are independent timeline evidence. They must not vanish
    # merely because the exact fork/merge commit introduced no fresh semantic
    # object in the selected source slice.
    commit_order = {
        commit["commit"]: index
        for index, commit in enumerate(timeline.get("commits", []))
    }

    def event_context(
        commit_ids: Iterable[str],
    ) -> tuple[
        str,
        tuple[str, ...],
        tuple[str, ...],
    ]:
        selected = [
            item
            for commit_id in commit_ids
            for item in working_by_commit.get(commit_id, [])
        ]
        programmes = tuple(
            dict.fromkeys(item.programme for item in selected)
        )
        programme = (
            programmes[0]
            if len(programmes) == 1
            else "Multiple"
        )
        nodes = tuple(
            dict.fromkeys(
                node
                for item in selected
                for node in item.focus_node_ids
            )
        )
        edges = tuple(
            dict.fromkeys(
                edge
                for item in selected
                for edge in item.focus_edge_ids
            )
        )
        return programme, nodes, edges

    def event_key(beat: FilmBeat) -> tuple[Any, ...]:
        payload = beat.payload or {}
        return (
            beat.kind,
            beat.commit,
            payload.get("number"),
            payload.get("merge_commit"),
            payload.get("fork_base"),
        )

    existing_event_keys = {
        event_key(beat)
        for beat in beats
        if beat.kind in {
            "branch-fork",
            "branch-merge",
            "pr-merge",
        }
    }

    def insert_timeline_event(
        beat: FilmBeat,
        *,
        after_semantic: bool,
    ) -> None:
        target_order = commit_order.get(beat.commit or "", 10**12)
        same_commit = [
            index
            for index, existing in enumerate(beats)
            if existing.commit == beat.commit
        ]
        if same_commit:
            if after_semantic:
                position = max(same_commit) + 1
            else:
                semantic_positions = [
                    index
                    for index in same_commit
                    if beats[index].kind == "semantic-change"
                ]
                position = (
                    min(semantic_positions)
                    if semantic_positions
                    else max(same_commit) + 1
                )
            beats.insert(position, beat)
            return

        position = len(beats)
        for index, existing in enumerate(beats):
            existing_order = commit_order.get(
                existing.commit or "",
                10**12,
            )
            if existing_order > target_order:
                position = index
                break
        beats.insert(position, beat)

    for branch_episode in timeline.get("branch_episodes", []):
        fork = branch_episode["fork_base"]
        left_path = list(branch_episode.get("left_path", []))
        right_path = list(branch_episode.get("right_path", []))
        fork_context = [
            fork,
            *(left_path[1:2]),
            *(right_path[1:2]),
        ]
        programme, nodes, edges = event_context(fork_context)
        fork_payload = dict(branch_episode)
        fork_beat = FilmBeat(
            kind="branch-fork",
            commit=fork,
            programme=programme,
            topic="branch split",
            duration_seconds=0.45,
            focus_node_ids=nodes,
            focus_edge_ids=edges,
            visible_node_ids=nodes,
            visible_edge_ids=edges,
            camera=(
                CameraDirective(
                    programme=programme,
                    focus_node_ids=nodes,
                    mode=(
                        "programme-overview"
                        if programme == "Multiple"
                        else "fit-active"
                    ),
                    padding=1.25,
                    min_width=7.0,
                    max_width=28.0,
                    transition_seconds=0.55,
                    reason="branch-fork-context",
                )
                if nodes
                else None
            ),
            payload=fork_payload,
        )
        if event_key(fork_beat) not in existing_event_keys:
            insert_timeline_event(
                fork_beat,
                after_semantic=False,
            )
            existing_event_keys.add(event_key(fork_beat))

        merge = branch_episode["merge_commit"]
        programme, nodes, edges = event_context(
            [
                merge,
                branch_episode["left_tip"],
                branch_episode["right_tip"],
            ]
        )
        merge_beat = FilmBeat(
            kind="branch-merge",
            commit=merge,
            programme=programme,
            topic="branch merge",
            duration_seconds=0.55,
            focus_node_ids=nodes,
            focus_edge_ids=edges,
            visible_node_ids=nodes,
            visible_edge_ids=edges,
            camera=(
                CameraDirective(
                    programme=programme,
                    focus_node_ids=nodes,
                    mode=(
                        "programme-overview"
                        if programme == "Multiple"
                        else "fit-active"
                    ),
                    padding=1.28,
                    min_width=7.0,
                    max_width=30.0,
                    transition_seconds=0.50,
                    reason="branch-merge-context",
                )
                if nodes
                else None
            ),
            payload=dict(branch_episode),
        )
        if event_key(merge_beat) not in existing_event_keys:
            insert_timeline_event(
                merge_beat,
                after_semantic=True,
            )
            existing_event_keys.add(event_key(merge_beat))

    for pr in timeline.get("pull_requests", []):
        merge = pr.get("merge_commit")
        if not merge or merge not in commit_order:
            continue
        programme, nodes, edges = event_context([merge])
        if not nodes:
            continue
        pr_beat = FilmBeat(
            kind="pr-merge",
            commit=merge,
            programme=programme,
            topic=(
                f"PR #{pr.get('number')} · "
                f"{pr.get('title', '')}"
            ),
            duration_seconds=0.75,
            focus_node_ids=nodes,
            focus_edge_ids=edges,
            visible_node_ids=nodes,
            visible_edge_ids=edges,
            camera=CameraDirective(
                programme=programme,
                focus_node_ids=nodes,
                mode=(
                    "programme-overview"
                    if programme == "Multiple"
                    else "fit-active"
                ),
                padding=1.22,
                min_width=7.0,
                max_width=28.0,
                transition_seconds=0.40,
                reason="pull-request-merge",
            ),
            payload=dict(pr),
        )
        if event_key(pr_beat) not in existing_event_keys:
            insert_timeline_event(
                pr_beat,
                after_semantic=True,
            )
            existing_event_keys.add(event_key(pr_beat))

    return ResearchFilmPlan(
        regions=regions,
        working_sets=tuple(working_sets),
        episodes=tuple(episodes),
        beats=tuple(beats),
    )
