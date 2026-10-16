from __future__ import annotations

from dataclasses import dataclass, replace
import re
from typing import Any, Iterable

from .model import GraphDelta


_SENTENCE_RE = re.compile(r"(?<=[.!?])\s+|\n+")
_TOKEN_RE = re.compile(r"[A-Za-z0-9_+'-]+")

_DELTA_MARKERS = (
    "recover", "recovered", "close", "closed", "prove", "proved",
    "introduce", "introduced", "replace", "replaced", "strengthen",
    "strengthened", "complete", "completed", "promote", "promoted",
    "repair", "repaired", "expose", "exposed", "reuse", "reused",
)
_FRONTIER_MARKERS = (
    "remaining", "remains", "open", "unpaid", "blocker", "blocked",
    "actual leaf", "remaining leaf", "remaining physical leaf", "frontier",
    "next payment", "hard payment", "outstanding", "missing",
)
_NONCLAIM_MARKERS = (
    "does not", "do not", "not establish", "not imply", "not promote",
    "no independent semantic promotion", "cannot", "must not", "!=",
    "not required", "not fabricated", "not manufacture",
)
_VERIFICATION_MARKERS = (
    "kernel-pending", "kernel pending", "kernel-unverified", "kernel unverified",
    "source-written", "red-first", "typecheck", "verification", "ci ",
    "workflow", "agda", "status:",
)


def _sentences(text: str) -> list[str]:
    return [item.strip(" \t-*#") for item in _SENTENCE_RE.split(text) if item.strip(" \t-*#")]


def _matches(sentence: str, markers: tuple[str, ...]) -> bool:
    lowered = sentence.lower()
    return any(marker in lowered for marker in markers)


def classify_narrative(text: str) -> dict[str, list[str]]:
    """Classify development prose without promoting it to theorem authority."""

    result = {
        "claimed_delta": [],
        "frontier": [],
        "nonclaims": [],
        "verification": [],
    }
    for sentence in _sentences(text):
        if _matches(sentence, _DELTA_MARKERS):
            result["claimed_delta"].append(sentence)
        if _matches(sentence, _FRONTIER_MARKERS):
            result["frontier"].append(sentence)
        if _matches(sentence, _NONCLAIM_MARKERS):
            result["nonclaims"].append(sentence)
        if _matches(sentence, _VERIFICATION_MARKERS):
            result["verification"].append(sentence)
    return result


@dataclass(frozen=True)
class NarrativeEvent:
    event_id: str
    timestamp: int
    kind: str
    title: str
    text: str = ""
    commit: str | None = None
    pull_request: int | None = None
    url: str | None = None
    touched_paths: tuple[str, ...] = ()
    touched_objects: tuple[str, ...] = ()
    introduced_objects: tuple[str, ...] = ()
    removed_objects: tuple[str, ...] = ()
    authority: str = "development-narrative"
    may_guide_discovery: bool = True
    may_explain_intent: bool = True
    may_establish_formal_fact: bool = False
    may_establish_empirical_fact: bool = False

    def to_dict(self) -> dict[str, Any]:
        classified = classify_narrative("\n".join((self.title, self.text)))
        return {
            "event_id": self.event_id,
            "timestamp": self.timestamp,
            "kind": self.kind,
            "title": self.title,
            "text": self.text,
            "commit": self.commit,
            "pull_request": self.pull_request,
            "url": self.url,
            "touched_paths": list(self.touched_paths),
            "touched_objects": list(self.touched_objects),
            "introduced_objects": list(self.introduced_objects),
            "removed_objects": list(self.removed_objects),
            "authority": self.authority,
            "may_guide_discovery": self.may_guide_discovery,
            "may_explain_intent": self.may_explain_intent,
            "may_establish_formal_fact": self.may_establish_formal_fact,
            "may_establish_empirical_fact": self.may_establish_empirical_fact,
            **classified,
        }


def link_event_to_semantic_delta(event: NarrativeEvent, delta: GraphDelta) -> NarrativeEvent:
    touched = tuple(sorted(set(event.touched_objects) | set(delta.added_nodes) | set(delta.removed_nodes)))
    return replace(
        event,
        touched_objects=touched,
        introduced_objects=tuple(sorted(set(event.introduced_objects) | set(delta.added_nodes))),
        removed_objects=tuple(sorted(set(event.removed_objects) | set(delta.removed_nodes))),
    )


def _tokens(value: str) -> set[str]:
    return {token.lower() for token in _TOKEN_RE.findall(value) if len(token) > 1}


def _event_score(event: NarrativeEvent, query: str) -> tuple[float, dict[str, float]]:
    q = _tokens(query)
    title = _tokens(event.title)
    body = _tokens(event.text)
    objects = _tokens(" ".join(event.touched_objects + event.introduced_objects + event.removed_objects))
    classified = classify_narrative(event.text)
    frontier = _tokens(" ".join(classified["frontier"] + classified["claimed_delta"]))

    def overlap(tokens: set[str]) -> float:
        if not q or not tokens:
            return 0.0
        return len(q & tokens) / len(q)

    exact_phrase = 1.0 if query.lower() in (event.title + "\n" + event.text).lower() else 0.0
    parts = {
        "object_overlap": overlap(objects),
        "frontier_overlap": overlap(frontier),
        "title_overlap": overlap(title),
        "body_overlap": overlap(body),
        "exact_phrase": exact_phrase,
    }
    score = (
        0.34 * parts["object_overlap"]
        + 0.28 * parts["frontier_overlap"]
        + 0.20 * parts["title_overlap"]
        + 0.10 * parts["body_overlap"]
        + 0.08 * parts["exact_phrase"]
    )
    return score, parts


def archaeology(events: Iterable[NarrativeEvent], query: str, *, limit: int = 40) -> list[dict[str, Any]]:
    """Rank development-history candidates for a concept/object query.

    This is a discovery aid only. Scores never establish semantic identity.
    """

    ranked: list[dict[str, Any]] = []
    for event in events:
        score, reasons = _event_score(event, query)
        if score <= 0.0:
            continue
        ranked.append({"event": event, "score": score, "reasons": reasons})
    ranked.sort(key=lambda item: (-item["score"], -item["event"].timestamp, item["event"].event_id))
    return ranked[:limit]


def frontier_genealogy(events: Iterable[NarrativeEvent], query: str, *, limit: int = 100) -> list[dict[str, Any]]:
    """Return time-ordered frontier/delta/nonclaim statements relevant to query."""

    q = _tokens(query)
    rows: list[dict[str, Any]] = []
    for event in events:
        classified = classify_narrative("\n".join((event.title, event.text)))
        relevant_text = " ".join(
            classified["claimed_delta"]
            + classified["frontier"]
            + classified["nonclaims"]
        )
        if q and not (q & _tokens(" ".join((event.title, relevant_text, " ".join(event.touched_objects))))):
            continue
        if not (classified["claimed_delta"] or classified["frontier"] or classified["nonclaims"]):
            continue
        rows.append(
            {
                "event_id": event.event_id,
                "timestamp": event.timestamp,
                "kind": event.kind,
                "title": event.title,
                "commit": event.commit,
                "pull_request": event.pull_request,
                "claimed_delta": classified["claimed_delta"],
                "frontier": classified["frontier"],
                "nonclaims": classified["nonclaims"],
                "verification": classified["verification"],
                "authority": event.authority,
            }
        )
    rows.sort(key=lambda item: (item["timestamp"], item["event_id"]))
    return rows[-limit:]
