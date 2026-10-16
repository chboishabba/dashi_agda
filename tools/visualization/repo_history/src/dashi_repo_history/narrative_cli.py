from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
from typing import Any, Iterable

from .narrative import (
    NarrativeEvent,
    archaeology,
    frontier_genealogy,
    stale_frontiers,
)
from .narrative_git import read_commit_narrative_events
from .narrative_index import attach_pr_semantic_context, link_events_to_history
from .pr_events import PullRequestEvent, collect_pr_events


def _load_history(path: str | None) -> dict[str, Any] | None:
    if not path:
        return None
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _cached_pr_events(history: dict[str, Any] | None) -> list[PullRequestEvent]:
    if history is None:
        return []
    result: list[PullRequestEvent] = []
    for item in history.get("pull_requests", []):
        if isinstance(item, dict):
            try:
                result.append(PullRequestEvent.from_dict(item))
            except (KeyError, TypeError, ValueError):
                continue
    return result


def collect_narrative_events(
    repo: Path,
    *,
    history_path: str | None = None,
    github_repository: str | None = None,
    max_commits: int | None = None,
) -> tuple[list[NarrativeEvent], dict[str, Any]]:
    commit_events = read_commit_narrative_events(
        repo,
        refs=("HEAD",),
        max_commits=max_commits,
    )
    history = _load_history(history_path)
    if history is not None:
        commit_events = link_events_to_history(commit_events, history)

    events = list(commit_events)
    cached_prs = _cached_pr_events(history)
    source_status: dict[str, Any] = {
        "git_commits": len(commit_events),
        "semantic_history_linked": history is not None,
        "cached_prs": len(cached_prs),
        "github_prs_requested": bool(github_repository),
        "github_prs_available": False,
        "github_prs": 0,
    }

    prs_by_number = {pr.number: pr for pr in cached_prs}
    if github_repository:
        try:
            live_prs = collect_pr_events(github_repository)
        except (OSError, subprocess.CalledProcessError, json.JSONDecodeError) as exc:
            source_status["github_prs_error"] = type(exc).__name__
        else:
            prs_by_number.update({pr.number: pr for pr in live_prs})
            source_status["github_prs_available"] = True
            source_status["github_prs"] = len(live_prs)

    pr_events = [
        attach_pr_semantic_context(pr, commit_events)
        for _, pr in sorted(prs_by_number.items())
    ]
    events.extend(pr_events)

    events.sort(key=lambda event: (event.timestamp, event.event_id))
    return events, source_status


def _ranked_payload(items: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    payload: list[dict[str, Any]] = []
    for item in items:
        payload.append(
            {
                "event": item["event"].to_dict(),
                "score": item["score"],
                "reasons": item["reasons"],
            }
        )
    return payload


def build_explanation(events: Iterable[NarrativeEvent], query: str) -> dict[str, Any]:
    materialized = list(events)
    ranked = archaeology(materialized, query, limit=80)
    genealogy = frontier_genealogy(materialized, query, limit=120)
    stale = stale_frontiers(materialized, query, limit=120)
    relevant = [item["event"] for item in ranked]
    latest = max(relevant, key=lambda event: (event.timestamp, event.event_id)) if relevant else None

    current_frontier: list[str] = []
    if genealogy:
        for row in reversed(genealogy):
            if row["frontier"]:
                current_frontier = list(row["frontier"])
                break

    return {
        "query": query,
        "authority": "development-narrative",
        "may_guide_discovery": True,
        "may_explain_intent": True,
        "may_establish_formal_fact": False,
        "may_establish_empirical_fact": False,
        "latest_event": latest.to_dict() if latest is not None else None,
        "current_frontier": current_frontier,
        "frontier_genealogy": genealogy,
        "potentially_stale_frontiers": stale,
        "archaeology": _ranked_payload(ranked[:20]),
    }


def _add_source_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("repo", help="local Git repository")
    parser.add_argument("--history", help="repo-history JSON used to attach semantic deltas and cached PRs")
    parser.add_argument("--github-prs", help="owner/repo for optional live PR narrative enrichment via gh")
    parser.add_argument("--max-commits", type=int, default=None)
    parser.add_argument("--json", action="store_true")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="dashi-repo-narrative",
        description="Query commit/PR narrative context without promoting it to theorem authority.",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    for name in ("history", "explain", "frontier", "stale", "archaeology"):
        command = sub.add_parser(name)
        _add_source_args(command)
        command.add_argument("query")
        command.add_argument("--limit", type=int, default=40)

    harvest = sub.add_parser("harvest")
    _add_source_args(harvest)
    harvest.add_argument("-o", "--output")
    return parser


def _print(payload: Any, *, as_json: bool) -> None:
    if as_json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
        return
    if isinstance(payload, dict) and "events" in payload:
        for event in payload["events"]:
            print(f"{event['timestamp']} {event['event_id']} {event['title']}")
        return
    print(json.dumps(payload, indent=2, ensure_ascii=False))


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    events, source_status = collect_narrative_events(
        Path(args.repo),
        history_path=args.history,
        github_repository=args.github_prs,
        max_commits=args.max_commits,
    )

    if args.command == "harvest":
        payload = {
            "schema": "dashi.repo-narrative.v1",
            "authority": "development-narrative",
            "source_status": source_status,
            "events": [event.to_dict() for event in events],
        }
        rendered = json.dumps(payload, indent=2, ensure_ascii=False) + "\n"
        if args.output:
            Path(args.output).write_text(rendered, encoding="utf-8")
            print(args.output)
        else:
            print(rendered, end="")
        return 0

    query = args.query
    if args.command == "archaeology":
        payload = {
            "query": query,
            "source_status": source_status,
            "authority": "development-narrative",
            "matches": _ranked_payload(archaeology(events, query, limit=args.limit)),
        }
    elif args.command == "frontier":
        payload = {
            "query": query,
            "source_status": source_status,
            "authority": "development-narrative",
            "genealogy": frontier_genealogy(events, query, limit=args.limit),
        }
    elif args.command == "stale":
        payload = {
            "query": query,
            "source_status": source_status,
            "authority": "development-narrative-heuristic",
            "potentially_stale_frontiers": stale_frontiers(events, query, limit=args.limit),
        }
    elif args.command == "explain":
        payload = build_explanation(events, query)
        payload["source_status"] = source_status
    elif args.command == "history":
        ranked = archaeology(events, query, limit=max(args.limit * 3, 60))
        selected = [item["event"] for item in ranked[: args.limit]]
        selected.sort(key=lambda event: (event.timestamp, event.event_id))
        payload = {
            "query": query,
            "source_status": source_status,
            "authority": "development-narrative",
            "events": [event.to_dict() for event in selected],
        }
    else:  # pragma: no cover
        raise AssertionError(args.command)

    _print(payload, as_json=args.json)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
