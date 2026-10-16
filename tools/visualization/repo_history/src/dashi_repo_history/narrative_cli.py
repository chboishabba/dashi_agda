from __future__ import annotations

import argparse
from dataclasses import replace
from pathlib import Path
import sqlite3
import subprocess
from typing import Any, Iterable

from .narrative import (
    NarrativeEvent,
    archaeology,
    frontier_genealogy,
    stale_frontiers,
)
from .narrative_git import read_commit_narrative_events
from .narrative_index import attach_pr_semantic_context
from .pr_events import collect_pr_events


def _store_api():
    """Load the repository-intelligence store lazily.

    repo-history is now a frontend of the shared repository-intelligence
    product. Keeping this import lazy allows pure narrative classification
    helpers to remain importable in isolation.
    """

    try:
        from agda_preflight.repository_store import (
            DEFAULT_REPOSITORY_DB,
            ensure_repository_schema,
            load_narrative_events,
            replace_narrative_events,
            replace_pull_requests,
        )
    except ImportError as error:  # pragma: no cover - packaging guard
        raise SystemExit(
            "dashi-repo-narrative requires the repository-intelligence core; "
            "install tools/agda_preflight in the same environment"
        ) from error
    return (
        DEFAULT_REPOSITORY_DB,
        ensure_repository_schema,
        load_narrative_events,
        replace_narrative_events,
        replace_pull_requests,
    )


def _database_path(repo: Path, value: Path | None) -> Path:
    default, *_ = _store_api()
    chosen = value or default
    return chosen if chosen.is_absolute() else repo.resolve() / chosen


def _connect_database(repo: Path, value: Path | None) -> sqlite3.Connection:
    path = _database_path(repo, value)
    path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(path)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("PRAGMA foreign_keys=ON")
    conn.execute("PRAGMA busy_timeout=5000")
    _default, ensure_schema, *_rest = _store_api()
    ensure_schema(conn)
    return conn


def _event_from_record(item: dict[str, Any]) -> NarrativeEvent:
    return NarrativeEvent(
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


def _attach_current_objects(
    conn: sqlite3.Connection,
    events: Iterable[NarrativeEvent],
) -> list[NarrativeEvent]:
    """Attach mechanically known current objects for touched source paths.

    This does not infer historical identity. Historical add/remove identity is
    supplied only by revision semantic deltas when those are materialized.
    """

    by_path: dict[str, tuple[str, ...]] = {}
    result: list[NarrativeEvent] = []
    for event in events:
        objects = set(event.touched_objects)
        for path in event.touched_paths:
            cached = by_path.get(path)
            if cached is None:
                try:
                    rows = conn.execute(
                        "SELECT symbol_id FROM repo_symbols WHERE file=? ORDER BY symbol_id",
                        (path,),
                    ).fetchall()
                except sqlite3.DatabaseError:
                    rows = []
                cached = tuple(str(row[0]) for row in rows)
                by_path[path] = cached
            objects.update(cached)
        result.append(replace(event, touched_objects=tuple(sorted(objects))))
    return result


def collect_narrative_events(
    repo: Path,
    *,
    github_repository: str | None = None,
    max_commits: int | None = None,
    connection: sqlite3.Connection | None = None,
) -> tuple[list[NarrativeEvent], dict[str, Any]]:
    commit_events = read_commit_narrative_events(
        repo,
        refs=("HEAD",),
        max_commits=max_commits,
    )
    if connection is not None:
        commit_events = _attach_current_objects(connection, commit_events)

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
            pr_events = [attach_pr_semantic_context(pr, commit_events) for pr in prs]
            events.extend(pr_events)
            source_status["github_prs_available"] = True
            source_status["github_prs"] = len(pr_events)

    events.sort(key=lambda event: (event.timestamp, event.event_id))
    return events, source_status


def _load_database_events(conn: sqlite3.Connection) -> list[NarrativeEvent]:
    _default, _ensure, load_events, *_rest = _store_api()
    return [_event_from_record(item) for item in load_events(conn)]


def _ranked_payload(items: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    payload: list[dict[str, Any]] = []
    for item in items:
        payload.append(
            {
                "event": item["event"],
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
        "latest_event": latest,
        "current_frontier": current_frontier,
        "frontier_genealogy": genealogy,
        "potentially_stale_frontiers": stale,
        "archaeology": _ranked_payload(ranked[:20]),
    }


def _add_database_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("repo", help="local Git repository")
    parser.add_argument(
        "--database",
        type=Path,
        help="repository-intelligence SQLite DB; defaults to .dashi/repository.sqlite3",
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="dashi-repo-narrative",
        description="Query commit/PR context stored in the DASHI repository-intelligence database.",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    for name in ("history", "explain", "frontier", "stale", "archaeology"):
        command = sub.add_parser(name)
        _add_database_args(command)
        command.add_argument("query")
        command.add_argument("--limit", type=int, default=40)

    harvest = sub.add_parser("harvest")
    _add_database_args(harvest)
    harvest.add_argument("--github-prs", help="owner/repo for optional PR enrichment via gh")
    harvest.add_argument("--max-commits", type=int, default=None)
    return parser


def _print_event(event: NarrativeEvent) -> None:
    print(f"{event.timestamp}\t{event.event_id}\t{event.title}")


def _print_explanation(payload: dict[str, Any]) -> None:
    latest = payload.get("latest_event")
    if latest is not None:
        print(f"latest\t{latest.event_id}\t{latest.title}")
    for item in payload.get("current_frontier", ()):
        print(f"frontier\t{item}")
    for item in payload.get("potentially_stale_frontiers", ()):
        print(
            "stale\t{}\t{}\t{}".format(
                item["event_id"],
                item["potentially_superseded_by"],
                item["frontier"],
            )
        )


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    repo = Path(args.repo).resolve()
    conn = _connect_database(repo, args.database)
    try:
        if args.command == "harvest":
            events, source_status = collect_narrative_events(
                repo,
                github_repository=args.github_prs,
                max_commits=args.max_commits,
                connection=conn,
            )
            _default, _ensure, _load, replace_events, replace_prs = _store_api()
            replace_events(
                conn,
                events=[event.to_dict() for event in events],
                source_status=source_status,
            )
            if args.github_prs and source_status.get("github_prs_available"):
                prs = collect_pr_events(args.github_prs)
                replace_prs(conn, [pr.to_dict() for pr in prs])
            print(
                "database={} events={} complete={} prs={}".format(
                    _database_path(repo, args.database),
                    len(events),
                    source_status["commit_history_complete"],
                    source_status.get("github_prs", 0),
                )
            )
            return 0

        events = _load_database_events(conn)
        query = args.query
        if args.command == "archaeology":
            for item in archaeology(events, query, limit=args.limit):
                event = item["event"]
                print(f"{item['score']:.3f}\t{event.event_id}\t{event.title}")
        elif args.command == "frontier":
            for row in frontier_genealogy(events, query, limit=args.limit):
                for statement in row["frontier"]:
                    print(f"{row['timestamp']}\t{row['event_id']}\tfrontier\t{statement}")
                for statement in row["claimed_delta"]:
                    print(f"{row['timestamp']}\t{row['event_id']}\tdelta\t{statement}")
                for statement in row["nonclaims"]:
                    print(f"{row['timestamp']}\t{row['event_id']}\tnonclaim\t{statement}")
        elif args.command == "stale":
            for row in stale_frontiers(events, query, limit=args.limit):
                print(
                    "{}\t{}\t{}\t{}".format(
                        row["event_id"],
                        row["potentially_superseded_by"],
                        row["overlap_score"],
                        row["frontier"],
                    )
                )
        elif args.command == "explain":
            _print_explanation(build_explanation(events, query))
        elif args.command == "history":
            ranked = archaeology(events, query, limit=max(args.limit * 3, 60))
            selected = [item["event"] for item in ranked[: args.limit]]
            selected.sort(key=lambda event: (event.timestamp, event.event_id))
            for event in selected:
                _print_event(event)
        else:  # pragma: no cover
            raise AssertionError(args.command)
        return 0
    finally:
        conn.close()


if __name__ == "__main__":
    raise SystemExit(main())
