from __future__ import annotations

from dataclasses import asdict, dataclass
from datetime import datetime
import json
import subprocess
from typing import Any

from .narrative import NarrativeEvent


@dataclass(frozen=True)
class PullRequestEvent:
    number: int
    title: str
    head_ref: str
    base_ref: str
    created_at: int | None
    merged_at: int | None
    closed_at: int | None
    merge_commit: str | None
    url: str | None
    body: str = ""
    commits: tuple[str, ...] = ()

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    def to_narrative_event(self) -> NarrativeEvent:
        timestamp = self.merged_at or self.closed_at or self.created_at or 0
        return NarrativeEvent(
            event_id=f"pr:{self.number}",
            timestamp=timestamp,
            kind="pull_request",
            title=self.title,
            text=self.body,
            commit=self.merge_commit,
            pull_request=self.number,
            url=self.url,
        )


def _timestamp(value: str | None) -> int | None:
    if not value:
        return None
    return int(
        datetime.fromisoformat(
            value.replace("Z", "+00:00")
        ).timestamp()
    )


def _commit_oids(value: Any) -> tuple[str, ...]:
    if not isinstance(value, list):
        return ()
    result: list[str] = []
    for item in value:
        if isinstance(item, dict):
            oid = item.get("oid")
            if oid:
                result.append(str(oid))
        elif isinstance(item, str):
            result.append(item)
    return tuple(result)


def parse_pr_records(records: list[dict[str, Any]]) -> list[PullRequestEvent]:
    events: list[PullRequestEvent] = []
    for record in records:
        merge = record.get("mergeCommit")
        if isinstance(merge, dict):
            merge = merge.get("oid")
        events.append(
            PullRequestEvent(
                number=int(record["number"]),
                title=str(record.get("title", "")),
                head_ref=str(record.get("headRefName", "")),
                base_ref=str(record.get("baseRefName", "")),
                created_at=_timestamp(record.get("createdAt")),
                merged_at=_timestamp(record.get("mergedAt")),
                closed_at=_timestamp(record.get("closedAt")),
                merge_commit=str(merge) if merge else None,
                url=(
                    str(record["url"])
                    if record.get("url")
                    else None
                ),
                body=str(record.get("body", "") or ""),
                commits=_commit_oids(record.get("commits")),
            )
        )
    return sorted(events, key=lambda event: event.number)


def collect_pr_events(repository: str) -> list[PullRequestEvent]:
    """Read GitHub PR metadata through the authenticated gh CLI.

    This is optional development-narrative metadata. Failure to access GitHub
    must never change semantic graph extraction or formal authority.
    """

    fields = ",".join(
        [
            "number",
            "title",
            "body",
            "headRefName",
            "baseRefName",
            "createdAt",
            "mergedAt",
            "closedAt",
            "mergeCommit",
            "commits",
            "url",
        ]
    )
    raw = subprocess.check_output(
        [
            "gh",
            "pr",
            "list",
            "--repo",
            repository,
            "--state",
            "all",
            "--limit",
            "1000",
            "--json",
            fields,
        ],
        text=True,
    )
    return parse_pr_records(json.loads(raw))
