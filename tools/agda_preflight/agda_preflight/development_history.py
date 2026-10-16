from __future__ import annotations

from dataclasses import dataclass, replace
from datetime import datetime
from pathlib import Path
import re
import subprocess
from typing import Any, Dict, Iterable, List, Optional, Tuple


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


def _sentences(text: str) -> List[str]:
    return [
        item.strip(" \t-*#")
        for item in _SENTENCE_RE.split(text)
        if item.strip(" \t-*#")
    ]


def _matches(sentence: str, markers: Tuple[str, ...]) -> bool:
    lowered = sentence.lower()
    return any(marker in lowered for marker in markers)


def classify_narrative(text: str) -> Dict[str, List[str]]:
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
    commit: Optional[str] = None
    pull_request: Optional[int] = None
    url: Optional[str] = None
    touched_paths: Tuple[str, ...] = ()
    touched_objects: Tuple[str, ...] = ()
    introduced_objects: Tuple[str, ...] = ()
    removed_objects: Tuple[str, ...] = ()
    authority: str = "development-narrative"
    may_guide_discovery: bool = True
    may_explain_intent: bool = True
    may_establish_formal_fact: bool = False
    may_establish_empirical_fact: bool = False

    def as_record(self) -> Dict[str, Any]:
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

    # Compatibility name used by the former repo-history package.
    def to_dict(self) -> Dict[str, Any]:
        return self.as_record()

    @classmethod
    def from_record(cls, item: Dict[str, Any]) -> "NarrativeEvent":
        return cls(
            event_id=str(item["event_id"]),
            timestamp=int(item.get("timestamp", 0) or 0),
            kind=str(item.get("kind", "unknown")),
            title=str(item.get("title", "")),
            text=str(item.get("text", "")),
            commit=item.get("commit"),
            pull_request=item.get("pull_request"),
            url=item.get("url"),
            touched_paths=tuple(str(value) for value in item.get("touched_paths", ())),
            touched_objects=tuple(str(value) for value in item.get("touched_objects", ())),
            introduced_objects=tuple(str(value) for value in item.get("introduced_objects", ())),
            removed_objects=tuple(str(value) for value in item.get("removed_objects", ())),
            authority=str(item.get("authority", "development-narrative")),
            may_guide_discovery=bool(item.get("may_guide_discovery", True)),
            may_explain_intent=bool(item.get("may_explain_intent", True)),
            may_establish_formal_fact=bool(item.get("may_establish_formal_fact", False)),
            may_establish_empirical_fact=bool(item.get("may_establish_empirical_fact", False)),
        )


def _tokens(value: str) -> set:
    return {token.lower() for token in _TOKEN_RE.findall(value) if len(token) > 1}


def _event_score(event: NarrativeEvent, query: str) -> Tuple[float, Dict[str, float]]:
    q = _tokens(query)
    title = _tokens(event.title)
    body = _tokens(event.text)
    objects = _tokens(" ".join(event.touched_objects + event.introduced_objects + event.removed_objects))
    classified = classify_narrative(event.text)
    frontier = _tokens(" ".join(classified["frontier"] + classified["claimed_delta"]))

    def overlap(tokens: set) -> float:
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


def archaeology(events: Iterable[NarrativeEvent], query: str, limit: int = 40) -> List[Dict[str, Any]]:
    ranked = []
    for event in events:
        score, reasons = _event_score(event, query)
        if score > 0.0:
            ranked.append({"event": event, "score": score, "reasons": reasons})
    ranked.sort(key=lambda item: (-item["score"], -item["event"].timestamp, item["event"].event_id))
    return ranked[:limit]


def frontier_genealogy(events: Iterable[NarrativeEvent], query: str, limit: int = 100) -> List[Dict[str, Any]]:
    q = _tokens(query)
    rows = []
    for event in events:
        classified = classify_narrative("\n".join((event.title, event.text)))
        relevant_text = " ".join(
            classified["claimed_delta"] + classified["frontier"] + classified["nonclaims"]
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


def stale_frontiers(events: Iterable[NarrativeEvent], query: str, limit: int = 100) -> List[Dict[str, Any]]:
    ordered = sorted(events, key=lambda event: (event.timestamp, event.event_id))
    q = _tokens(query)
    rows = []
    for index, event in enumerate(ordered):
        classified = classify_narrative("\n".join((event.title, event.text)))
        for frontier in classified["frontier"]:
            frontier_tokens = _tokens(frontier)
            if q and not (q & frontier_tokens):
                continue
            best = None
            best_overlap = 0.0
            for later in ordered[index + 1 :]:
                later_classified = classify_narrative("\n".join((later.title, later.text)))
                for delta in later_classified["claimed_delta"]:
                    delta_tokens = _tokens(delta)
                    denominator = len(frontier_tokens | q) or 1
                    overlap = len((frontier_tokens | q) & delta_tokens) / denominator
                    if overlap > best_overlap:
                        best_overlap = overlap
                        best = later
            if best is not None and best_overlap >= 0.20:
                rows.append(
                    {
                        "event_id": event.event_id,
                        "timestamp": event.timestamp,
                        "frontier": frontier,
                        "potentially_superseded_by": best.event_id,
                        "overlap_score": best_overlap,
                        "authority": "development-narrative-heuristic",
                        "may_establish_formal_fact": False,
                    }
                )
    rows.sort(key=lambda item: (item["timestamp"], item["event_id"]))
    return rows[-limit:]


def _run_bytes(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=repo)


def _run_text(repo: Path, *args: str) -> str:
    return _run_bytes(repo, *args).decode("utf-8", "replace")


def _changed_paths(repo: Path, commit: str) -> Tuple[str, ...]:
    raw = _run_bytes(
        repo,
        "diff-tree",
        "--root",
        "--no-commit-id",
        "--name-only",
        "-r",
        "-z",
        commit,
    )
    return tuple(
        sorted(
            {
                item.decode("utf-8", "replace")
                for item in raw.split(b"\0")
                if item
            }
        )
    )


def read_commit_narrative_events(
    repo: Path,
    refs: Tuple[str, ...] = ("HEAD",),
    max_commits: Optional[int] = None,
) -> List[NarrativeEvent]:
    repo = repo.resolve()
    rev_args = ["rev-list", "--reverse", "--topo-order"] + list(refs)
    commits = [item for item in _run_text(repo, *rev_args).splitlines() if item]
    if max_commits is not None:
        commits = commits[-max(0, max_commits):]
    events = []
    for commit in commits:
        raw = _run_text(
            repo,
            "show",
            "-s",
            "--format=%ct%x00%s%x00%b",
            commit,
        ).rstrip("\n")
        parts = raw.split("\x00", 2)
        if len(parts) != 3:
            continue
        timestamp_text, subject, body = parts
        try:
            timestamp = int(timestamp_text)
        except ValueError:
            timestamp = 0
        events.append(
            NarrativeEvent(
                event_id="commit:" + commit,
                timestamp=timestamp,
                kind="commit",
                title=subject.strip(),
                text=body.strip(),
                commit=commit,
                touched_paths=_changed_paths(repo, commit),
            )
        )
    return events


@dataclass(frozen=True)
class PullRequestEvent:
    number: int
    title: str
    head_ref: str
    base_ref: str
    created_at: Optional[int]
    merged_at: Optional[int]
    closed_at: Optional[int]
    merge_commit: Optional[str]
    url: Optional[str]
    body: str = ""
    commits: Tuple[str, ...] = ()

    def as_record(self) -> Dict[str, Any]:
        return {
            "number": self.number,
            "title": self.title,
            "head_ref": self.head_ref,
            "base_ref": self.base_ref,
            "created_at": self.created_at,
            "merged_at": self.merged_at,
            "closed_at": self.closed_at,
            "merge_commit": self.merge_commit,
            "url": self.url,
            "body": self.body,
            "commits": list(self.commits),
        }

    def to_dict(self) -> Dict[str, Any]:
        return self.as_record()

    def to_narrative_event(self) -> NarrativeEvent:
        timestamp = self.merged_at or self.closed_at or self.created_at or 0
        return NarrativeEvent(
            event_id="pr:{}".format(self.number),
            timestamp=timestamp,
            kind="pull_request",
            title=self.title,
            text=self.body,
            commit=self.merge_commit,
            pull_request=self.number,
            url=self.url,
        )


def _timestamp(value: Optional[str]) -> Optional[int]:
    if not value:
        return None
    return int(datetime.fromisoformat(value.replace("Z", "+00:00")).timestamp())


def _commit_oids(value: Any) -> Tuple[str, ...]:
    if not isinstance(value, list):
        return ()
    result = []
    for item in value:
        if isinstance(item, dict):
            oid = item.get("oid")
            if oid:
                result.append(str(oid))
        elif isinstance(item, str):
            result.append(item)
    return tuple(result)


def parse_pr_records(records: List[Dict[str, Any]]) -> List[PullRequestEvent]:
    events = []
    for record in records:
        merge = record.get("mergeCommit")
        if isinstance(merge, dict):
            merge = merge.get("oid")
        events.append(
            PullRequestEvent(
                number=int(record["number"]),
                title=str(record.get("title", "")),
                head_ref=str(record.get("headRefName", record.get("head_ref", ""))),
                base_ref=str(record.get("baseRefName", record.get("base_ref", ""))),
                created_at=_timestamp(record.get("createdAt")) if isinstance(record.get("createdAt"), str) else record.get("created_at"),
                merged_at=_timestamp(record.get("mergedAt")) if isinstance(record.get("mergedAt"), str) else record.get("merged_at"),
                closed_at=_timestamp(record.get("closedAt")) if isinstance(record.get("closedAt"), str) else record.get("closed_at"),
                merge_commit=str(merge) if merge else record.get("merge_commit"),
                url=str(record["url"]) if record.get("url") else None,
                body=str(record.get("body", "") or ""),
                commits=_commit_oids(record.get("commits")),
            )
        )
    return sorted(events, key=lambda event: event.number)


def collect_pr_events(repository: str) -> List[PullRequestEvent]:
    """Collect optional GitHub development narrative through authenticated gh."""

    fields = ",".join(
        [
            "number", "title", "body", "headRefName", "baseRefName",
            "createdAt", "mergedAt", "closedAt", "mergeCommit", "commits", "url",
        ]
    )
    raw = subprocess.check_output(
        [
            "gh", "pr", "list", "--repo", repository, "--state", "all",
            "--limit", "1000", "--json", fields,
        ],
        text=True,
    )
    # The gh interface is the external transport boundary. Its output is parsed
    # in memory and immediately normalized into SQLite by repository_store.
    import json as _transport_json
    return parse_pr_records(_transport_json.loads(raw))


def attach_pr_semantic_context(
    pr: PullRequestEvent,
    commit_events: Iterable[NarrativeEvent],
) -> NarrativeEvent:
    by_commit = {event.commit: event for event in commit_events if event.commit}
    touched_paths = set()
    touched_objects = set()
    introduced_objects = set()
    removed_objects = set()
    for sha in pr.commits:
        event = by_commit.get(sha)
        if event is None:
            continue
        touched_paths.update(event.touched_paths)
        touched_objects.update(event.touched_objects)
        introduced_objects.update(event.introduced_objects)
        removed_objects.update(event.removed_objects)
    return replace(
        pr.to_narrative_event(),
        touched_paths=tuple(sorted(touched_paths)),
        touched_objects=tuple(sorted(touched_objects)),
        introduced_objects=tuple(sorted(introduced_objects)),
        removed_objects=tuple(sorted(removed_objects)),
    )
