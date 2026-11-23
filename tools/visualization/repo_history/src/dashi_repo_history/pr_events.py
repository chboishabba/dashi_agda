from __future__ import annotations

from dataclasses import asdict, dataclass
from datetime import datetime
import json
import subprocess
from typing import Any


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

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _timestamp(value: str | None) -> int | None:
    if not value:
        return None
    return int(
        datetime.fromisoformat(
            value.replace("Z", "+00:00")
        ).timestamp()
    )


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
            )
        )
    return sorted(events, key=lambda event: event.number)


def collect_pr_events(repository: str) -> list[PullRequestEvent]:
    """Read GitHub PR metadata through the authenticated gh CLI.

    This is optional timeline metadata. Failure to access GitHub must never
    change semantic graph extraction.
    """

    fields = ",".join(
        [
            "number",
            "title",
            "headRefName",
            "baseRefName",
            "createdAt",
            "mergedAt",
            "closedAt",
            "mergeCommit",
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
