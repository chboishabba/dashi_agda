from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
from typing import Any, Iterable

from agda_preflight.development_history import (
    NarrativeEvent,
    archaeology,
    attach_pr_semantic_context,
    collect_pr_events,
    frontier_genealogy,
    read_commit_narrative_events,
    stale_frontiers,
)
from agda_preflight.repository_cli import main as repository_main


def collect_narrative_events(
    repo: Path,
    *,
    github_repository: str | None = None,
    max_commits: int | None = None,
    connection=None,
) -> tuple[list[NarrativeEvent], dict[str, Any]]:
    """Compatibility collector over the unified development-history core."""

    commit_events = read_commit_narrative_events(
        repo,
        refs=("HEAD",),
        max_commits=max_commits,
    )
    events = list(commit_events)
    source_status: dict[str, Any] = {
        "git_commits": len(commit_events),
        "commit_history_complete": max_commits is None,
        "semantic_history_linked": connection is not None,
        "github_prs_requested": bool(github_repository),
        "github_prs_available": False,
        "github_prs": 0,
    }
    if github_repository:
        try:
            prs = collect_pr_events(github_repository)
        except (OSError, subprocess.CalledProcessError) as exc:
            source_status["github_prs_error"] = type(exc).__name__
        else:
            events.extend(
                attach_pr_semantic_context(pr, commit_events)
                for pr in prs
            )
            source_status["github_prs_available"] = True
            source_status["github_prs"] = len(prs)
    events.sort(key=lambda event: (event.timestamp, event.event_id))
    return events, source_status


def _ranked_payload(items: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "event": item["event"].as_record(),
            "score": item["score"],
            "reasons": item["reasons"],
        }
        for item in items
    ]


def build_explanation(events: Iterable[NarrativeEvent], query: str) -> dict[str, Any]:
    materialized = list(events)
    ranked = archaeology(materialized, query, limit=80)
    genealogy = frontier_genealogy(materialized, query, limit=120)
    stale = stale_frontiers(materialized, query, limit=120)
    relevant = [item["event"] for item in ranked]
    latest = (
        max(relevant, key=lambda event: (event.timestamp, event.event_id))
        if relevant
        else None
    )
    current_frontier: list[str] = []
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
        "latest_event": latest.as_record() if latest else None,
        "current_frontier": current_frontier,
        "frontier_genealogy": genealogy,
        "potentially_stale_frontiers": stale,
        "archaeology": _ranked_payload(ranked[:20]),
    }


def _add_database_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("repo", help="local Git repository")
    parser.add_argument("--database", type=Path)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="dashi-repo-narrative",
        description="Compatibility frontend for dashi-repo history commands.",
    )
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("history", "explain", "frontier", "stale", "archaeology"):
        command = sub.add_parser(name)
        _add_database_args(command)
        command.add_argument("query")
        command.add_argument("--limit", type=int, default=40)
    harvest = sub.add_parser("harvest")
    _add_database_args(harvest)
    harvest.add_argument("--github-prs")
    harvest.add_argument("--max-commits", type=int)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    forwarded = [args.command]
    if args.command != "harvest":
        forwarded.append(args.query)
        forwarded.extend(["--limit", str(args.limit)])
    elif args.github_prs:
        forwarded.extend(["--github-prs", args.github_prs])
    if args.command == "harvest" and args.max_commits is not None:
        forwarded.extend(["--max-commits", str(args.max_commits)])
    forwarded.extend(["--root", str(Path(args.repo).resolve())])
    if args.database is not None:
        forwarded.extend(["--database", str(args.database)])
    return repository_main(forwarded)


if __name__ == "__main__":
    raise SystemExit(main())
