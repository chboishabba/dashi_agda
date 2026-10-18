from __future__ import annotations

from dataclasses import replace

from agda_preflight.development_history import (
    NarrativeEvent,
    archaeology,
    classify_narrative,
    frontier_genealogy,
    stale_frontiers,
)

from .model import GraphDelta


def link_event_to_semantic_delta(
    event: NarrativeEvent,
    delta: GraphDelta,
) -> NarrativeEvent:
    """Attach repo-history semantic deltas to the shared narrative event type."""

    touched = tuple(
        sorted(
            set(event.touched_objects)
            | set(delta.added_nodes)
            | set(delta.removed_nodes)
        )
    )
    return replace(
        event,
        touched_objects=touched,
        introduced_objects=tuple(
            sorted(set(event.introduced_objects) | set(delta.added_nodes))
        ),
        removed_objects=tuple(
            sorted(set(event.removed_objects) | set(delta.removed_nodes))
        ),
    )


__all__ = [
    "NarrativeEvent",
    "archaeology",
    "classify_narrative",
    "frontier_genealogy",
    "stale_frontiers",
    "link_event_to_semantic_delta",
]
