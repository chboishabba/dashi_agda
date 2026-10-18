from __future__ import annotations

from typing import Any

from agda_preflight.development_history import (
    PullRequestEvent as _CorePullRequestEvent,
    collect_pr_events as _collect_pr_events,
    parse_pr_records as _parse_pr_records,
)


class PullRequestEvent(_CorePullRequestEvent):
    """Compatibility surface for the former repo-history PR event type."""

    @classmethod
    def from_dict(cls, value: dict[str, Any]) -> "PullRequestEvent":
        return cls(
            number=int(value["number"]),
            title=str(value.get("title", "")),
            head_ref=str(value.get("head_ref", "")),
            base_ref=str(value.get("base_ref", "")),
            created_at=(int(value["created_at"]) if value.get("created_at") is not None else None),
            merged_at=(int(value["merged_at"]) if value.get("merged_at") is not None else None),
            closed_at=(int(value["closed_at"]) if value.get("closed_at") is not None else None),
            merge_commit=(str(value["merge_commit"]) if value.get("merge_commit") else None),
            url=(str(value["url"]) if value.get("url") else None),
            body=str(value.get("body", "") or ""),
            commits=tuple(str(item) for item in value.get("commits", ())),
        )


def _compat(event: _CorePullRequestEvent) -> PullRequestEvent:
    return PullRequestEvent.from_dict(event.as_record())


def parse_pr_records(records: list[dict[str, Any]]) -> list[PullRequestEvent]:
    return [_compat(event) for event in _parse_pr_records(records)]


def collect_pr_events(repository: str) -> list[PullRequestEvent]:
    return [_compat(event) for event in _collect_pr_events(repository)]


__all__ = ["PullRequestEvent", "parse_pr_records", "collect_pr_events"]
