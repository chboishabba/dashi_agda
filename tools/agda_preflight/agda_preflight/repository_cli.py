from __future__ import annotations

import argparse
from dataclasses import replace
from pathlib import Path
import sqlite3
import subprocess
from typing import Any, Iterable, Optional

from .development_history import (
    NarrativeEvent,
    archaeology,
    attach_pr_semantic_context,
    collect_pr_events,
    frontier_genealogy,
    read_commit_narrative_events,
    stale_frontiers,
)
from .repository_store import (
    DEFAULT_REPOSITORY_DB,
    ensure_repository_schema,
    load_narrative_events,
    replace_narrative_events,
    replace_pull_requests,
    sync_legacy_repo_index,
)
from .service import DashiAgdaService


def _add_common(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument(
        "--database",
        type=Path,
        default=DEFAULT_REPOSITORY_DB,
        help="single repository-intelligence SQLite database",
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="dashi-repo",
        description="DASHI repository intelligence: semantics, preflight, history and archaeology.",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    status = sub.add_parser("status", help="show shared database coverage")
    _add_common(status)

    sync = sub.add_parser("sync-index", help="migrate the legacy repo-index into the shared DB")
    _add_common(sync)
    sync.add_argument("--force", action="store_true")

    diagnose = sub.add_parser("diagnose", help="run structural preflight diagnostics")
    diagnose.add_argument("target")
    diagnose.add_argument("--errors-only", action="store_true")
    diagnose.add_argument("--limit", type=int)
    _add_common(diagnose)

    nxt = sub.add_parser("next", help="return the next cached/preflight diagnostic")
    nxt.add_argument("target")
    nxt.add_argument("--require-fix", action="store_true")
    _add_common(nxt)

    affected = sub.add_parser("affected", help="show indexed reverse-affected modules")
    affected.add_argument("target")
    affected.add_argument("--within")
    _add_common(affected)

    refresh = sub.add_parser("refresh", help="refresh one semantic/preflight target")
    refresh.add_argument("target")
    _add_common(refresh)

    symbol = sub.add_parser("symbol", help="search repository symbols")
    symbol.add_argument("query")
    symbol.add_argument("--history", action="store_true")
    symbol.add_argument("--limit", type=int, default=50)
    _add_common(symbol)

    related = sub.add_parser("related", help="find exact/equivalent/similar declarations")
    related.add_argument("symbol")
    related.add_argument("--history", action="store_true")
    related.add_argument("--limit", type=int, default=50)
    _add_common(related)

    obj = sub.add_parser("object", help="show one indexed object")
    obj.add_argument("symbol_id")
    _add_common(obj)

    discover = sub.add_parser("discover", help="produce fail-closed discovery/absence receipt")
    discover.add_argument("query")
    discover.add_argument("--limit", type=int, default=50)
    _add_common(discover)

    lineage = sub.add_parser("lineage", help="report RoundNNN lineage/noise")
    lineage.add_argument("--prefix")
    _add_common(lineage)

    harvest = sub.add_parser("harvest", help="store Git/PR development history in the shared DB")
    harvest.add_argument("--github-prs", help="owner/repo for optional PR metadata via gh")
    harvest.add_argument("--max-commits", type=int)
    _add_common(harvest)

    for name in ("history", "archaeology", "frontier", "stale", "explain"):
        command = sub.add_parser(name)
        command.add_argument("query")
        command.add_argument("--limit", type=int, default=40)
        _add_common(command)

    return parser


def _db_path(root: Path, database: Path) -> Path:
    return database if database.is_absolute() else root.resolve() / database


def _connect(root: Path, database: Path) -> sqlite3.Connection:
    path = _db_path(root, database)
    path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(path)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("PRAGMA foreign_keys=ON")
    conn.execute("PRAGMA busy_timeout=5000")
    ensure_repository_schema(conn)
    return conn


def _events_from_db(conn: sqlite3.Connection) -> list[NarrativeEvent]:
    return [NarrativeEvent.from_record(item) for item in load_narrative_events(conn)]


def _attach_current_objects(
    conn: sqlite3.Connection,
    events: Iterable[NarrativeEvent],
) -> list[NarrativeEvent]:
    cache: dict[str, tuple[str, ...]] = {}
    result = []
    for event in events:
        objects = set(event.touched_objects)
        for path in event.touched_paths:
            if path not in cache:
                try:
                    rows = conn.execute(
                        "SELECT symbol_id FROM repo_symbols WHERE file=? ORDER BY symbol_id",
                        (path,),
                    ).fetchall()
                except sqlite3.DatabaseError:
                    rows = []
                cache[path] = tuple(str(row[0]) for row in rows)
            objects.update(cache[path])
        result.append(replace(event, touched_objects=tuple(sorted(objects))))
    return result


def _harvest(
    root: Path,
    conn: sqlite3.Connection,
    *,
    github_repository: Optional[str],
    max_commits: Optional[int],
) -> dict[str, Any]:
    commit_events = read_commit_narrative_events(root, max_commits=max_commits)
    commit_events = _attach_current_objects(conn, commit_events)
    events = list(commit_events)
    source_status: dict[str, Any] = {
        "git_commits": len(commit_events),
        "commit_history_complete": max_commits is None,
        "semantic_history_linked": True,
        "github_prs_requested": bool(github_repository),
        "github_prs_available": False,
        "github_prs": 0,
    }
    prs = []
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
    replace_narrative_events(
        conn,
        events=[event.as_record() for event in events],
        source_status=source_status,
    )
    if prs:
        replace_pull_requests(conn, [pr.as_record() for pr in prs])
    return {
        "events": len(events),
        "commits": len(commit_events),
        "pull_requests": len(prs),
        "complete": bool(source_status["commit_history_complete"]),
    }


def _print_mapping(prefix: str, value: dict[str, Any]) -> None:
    for key, item in value.items():
        if isinstance(item, (str, int, float, bool)) or item is None:
            print(f"{prefix}{key}\t{item}")


def _print_semantic_results(items: Iterable[dict[str, Any]]) -> None:
    for item in items:
        qualified = item.get("qualified_name") or item.get("symbol_id") or item.get("name")
        role = item.get("surface_role", "unknown")
        kind = item.get("kind", "unknown")
        location = ""
        if item.get("file"):
            location = str(item["file"])
            if item.get("line_start"):
                location += ":" + str(item["line_start"])
        print(f"{qualified}\t{kind}\t{role}\t{location}")


def _run_history_query(command: str, query: str, limit: int, events: list[NarrativeEvent]) -> None:
    if command == "archaeology":
        for item in archaeology(events, query, limit=limit):
            event = item["event"]
            print(f"{item['score']:.3f}\t{event.timestamp}\t{event.event_id}\t{event.title}")
        return
    if command == "history":
        ranked = archaeology(events, query, limit=max(limit * 3, 60))
        selected = [item["event"] for item in ranked[:limit]]
        selected.sort(key=lambda event: (event.timestamp, event.event_id))
        for event in selected:
            print(f"{event.timestamp}\t{event.event_id}\t{event.title}")
        return
    if command == "frontier":
        for row in frontier_genealogy(events, query, limit=limit):
            for text in row["claimed_delta"]:
                print(f"{row['timestamp']}\t{row['event_id']}\tdelta\t{text}")
            for text in row["frontier"]:
                print(f"{row['timestamp']}\t{row['event_id']}\tfrontier\t{text}")
            for text in row["nonclaims"]:
                print(f"{row['timestamp']}\t{row['event_id']}\tnonclaim\t{text}")
        return
    if command == "stale":
        for row in stale_frontiers(events, query, limit=limit):
            print(
                f"{row['event_id']}\t{row['potentially_superseded_by']}\t"
                f"{row['overlap_score']:.3f}\t{row['frontier']}"
            )
        return
    if command == "explain":
        ranked = archaeology(events, query, limit=80)
        if ranked:
            latest = max(
                (item["event"] for item in ranked),
                key=lambda event: (event.timestamp, event.event_id),
            )
            print(f"latest\t{latest.event_id}\t{latest.title}")
        genealogy = frontier_genealogy(events, query, limit=120)
        for row in reversed(genealogy):
            if row["frontier"]:
                for text in row["frontier"]:
                    print(f"frontier\t{row['event_id']}\t{text}")
                break
        for row in stale_frontiers(events, query, limit=20):
            print(
                f"stale\t{row['event_id']}\t{row['potentially_superseded_by']}\t{row['frontier']}"
            )
        return
    raise AssertionError(command)


def main(argv=None) -> int:
    args = build_parser().parse_args(argv)
    root = args.root.resolve()
    database = _db_path(root, args.database)

    if args.command in {"status", "sync-index", "harvest", "history", "archaeology", "frontier", "stale", "explain"}:
        conn = _connect(root, args.database)
        try:
            if args.command == "status":
                print(f"database\t{database}")
                for table in (
                    "modules", "repo_files", "repo_symbols", "narrative_events",
                    "pull_requests", "promotion_receipts",
                ):
                    try:
                        count = int(conn.execute(f"SELECT count(*) FROM {table}").fetchone()[0])
                    except sqlite3.DatabaseError:
                        count = 0
                    print(f"{table}\t{count}")
                return 0
            if args.command == "sync-index":
                changed = sync_legacy_repo_index(root, conn, force=args.force)
                print(f"database\t{database}")
                print(f"legacy_repo_index_imported\t{changed}")
                return 0
            if args.command == "harvest":
                result = _harvest(
                    root,
                    conn,
                    github_repository=args.github_prs,
                    max_commits=args.max_commits,
                )
                print(f"database\t{database}")
                _print_mapping("", result)
                return 0
            _run_history_query(args.command, args.query, args.limit, _events_from_db(conn))
            return 0
        finally:
            conn.close()

    with DashiAgdaService(root, database) as service:
        if args.command == "diagnose":
            result = service.diagnose(
                args.target,
                errors_only=args.errors_only,
                limit=args.limit,
            )
            for diagnostic in result["diagnostics"]:
                print(
                    "{}:{}:{}\t{}\t{}\t{}".format(
                        diagnostic["path"], diagnostic["line"], diagnostic["column"],
                        diagnostic["severity"], diagnostic["code"], diagnostic["message"],
                    )
                )
            return 0
        if args.command == "next":
            result = service.next_error(args.target, require_fix=args.require_fix)
            diagnostic = result.get("diagnostic")
            if diagnostic:
                print(
                    "{}:{}:{}\t{}\t{}".format(
                        diagnostic["path"], diagnostic["line"], diagnostic["column"],
                        diagnostic["code"], diagnostic["message"],
                    )
                )
            else:
                print(result.get("status", "clean"))
            return 0
        if args.command == "affected":
            result = service.affected(args.target, within=args.within)
            for module in result["modules"]:
                print(module)
            return 0
        if args.command == "refresh":
            result = service.refresh(args.target)
            print(f"refreshed\t{args.target}")
            _print_mapping("", result.get("profile", {}).get("counts", {}))
            return 0
        if args.command == "symbol":
            result = service.symbol_search(args.query, include_history=args.history, limit=args.limit)
            _print_semantic_results(result["results"])
            return 0
        if args.command == "related":
            result = service.related_symbols(args.symbol, include_history=args.history, limit=args.limit)
            for group in ("exact", "signature_equivalent", "body_equivalent", "similar"):
                for item in result.get(group, ()):
                    qualified = item.get("qualified_name", "")
                    score = item.get("similarity", "")
                    print(f"{group}\t{qualified}\t{score}")
            return 0
        if args.command == "object":
            result = service.object_detail(args.symbol_id)
            symbol = result.get("symbol")
            if symbol:
                _print_semantic_results([symbol])
            for ref in result.get("refs", ()):
                print(f"ref\t{ref.get('ref_kind')}\t{ref.get('from_symbol')}\t{ref.get('to_symbol')}")
            return 0
        if args.command == "discover":
            result = service.discover(args.query, limit=args.limit)
            print(f"absence_status\t{result['absence_status']}")
            print(f"absence_claim_permitted\t{result['absence_claim_permitted']}")
            _print_semantic_results(result.get("live_matches", ()))
            for event in result.get("narrative_archaeology", {}).get("matches", ()):
                print(f"history\t{event.get('event_id')}\t{event.get('title')}")
            return 0
        if args.command == "lineage":
            result = service.round_lineage(prefix=args.prefix)
            for family in result.get("families", ()):
                print(f"family\t{family['family']}\t{family['module_count']}")
                for transition in family["transitions"]:
                    print(
                        "transition\t{}\t{}\t{}\t{}".format(
                            transition["from_round"], transition["to_round"],
                            transition["novelty_ratio"], transition["snapshot_noise_ratio"],
                        )
                    )
            return 0
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())
