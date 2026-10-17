from __future__ import annotations

from collections import defaultdict
from dataclasses import replace
from typing import Any, Iterable

from .narrative import NarrativeEvent


def _symbol_label(node: dict[str, Any]) -> str:
    module = str(node.get("module", "") or "")
    label = str(node.get("label", "") or "")
    if module and label:
        return f"{module}::{label}"
    return label or str(node.get("symbol_id", ""))


def _symbol_name_index(history: dict[str, Any]) -> dict[str, str]:
    names: dict[str, str] = {}
    for snapshot in history.get("snapshots", []):
        graph = snapshot.get("graph", {})
        for node in graph.get("nodes", []):
            symbol_id = str(node.get("symbol_id", ""))
            if symbol_id:
                names.setdefault(symbol_id, _symbol_label(node))
    return names


def _delta_by_commit(history: dict[str, Any]) -> dict[str, dict[str, set[str]]]:
    result: dict[str, dict[str, set[str]]] = {}
    for snapshot in history.get("snapshots", []):
        commit = str(snapshot.get("commit", ""))
        if not commit:
            continue
        aggregate = {
            "added": set(),
            "removed": set(),
        }
        for delta in snapshot.get("parent_deltas", {}).values():
            aggregate["added"].update(str(item) for item in delta.get("added_nodes", []))
            aggregate["removed"].update(str(item) for item in delta.get("removed_nodes", []))
        result[commit] = aggregate
    return result


def link_events_to_history(
    events: Iterable[NarrativeEvent],
    history: dict[str, Any],
) -> list[NarrativeEvent]:
    """Attach semantic-delta names to development narrative events.

    The link is observational: it says the event and semantic delta share the
    same commit. It does not make narrative prose formal authority.
    """

    names = _symbol_name_index(history)
    deltas = _delta_by_commit(history)
    linked: list[NarrativeEvent] = []
    for event in events:
        if not event.commit or event.commit not in deltas:
            linked.append(event)
            continue
        delta = deltas[event.commit]
        introduced = tuple(sorted(names.get(item, item) for item in delta["added"]))
        removed = tuple(sorted(names.get(item, item) for item in delta["removed"]))
        touched = tuple(
            sorted(
                set(event.touched_objects)
                | set(introduced)
                | set(removed)
            )
        )
        linked.append(
            replace(
                event,
                touched_objects=touched,
                introduced_objects=tuple(sorted(set(event.introduced_objects) | set(introduced))),
                removed_objects=tuple(sorted(set(event.removed_objects) | set(removed))),
            )
        )
    return linked


def attach_pr_semantic_context(
    pr_event,
    commit_events: Iterable[NarrativeEvent],
) -> NarrativeEvent:
    """Union semantic context from commits known to belong to one PR."""

    by_commit = {event.commit: event for event in commit_events if event.commit}
    base = pr_event.to_narrative_event()
    touched_paths = set(base.touched_paths)
    touched_objects = set(base.touched_objects)
    introduced = set(base.introduced_objects)
    removed = set(base.removed_objects)
    for commit in getattr(pr_event, "commits", ()):
        event = by_commit.get(commit)
        if event is None:
            continue
        touched_paths.update(event.touched_paths)
        touched_objects.update(event.touched_objects)
        introduced.update(event.introduced_objects)
        removed.update(event.removed_objects)
    return replace(
        base,
        touched_paths=tuple(sorted(touched_paths)),
        touched_objects=tuple(sorted(touched_objects)),
        introduced_objects=tuple(sorted(introduced)),
        removed_objects=tuple(sorted(removed)),
    )


def group_events_by_object(events: Iterable[NarrativeEvent]) -> dict[str, list[NarrativeEvent]]:
    grouped: dict[str, list[NarrativeEvent]] = defaultdict(list)
    for event in events:
        for obj in event.touched_objects:
            grouped[obj].append(event)
    for obj in grouped:
        grouped[obj].sort(key=lambda event: (event.timestamp, event.event_id))
    return dict(grouped)
