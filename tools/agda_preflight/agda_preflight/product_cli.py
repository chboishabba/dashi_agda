from __future__ import annotations

import argparse
from pathlib import Path
import sqlite3
import sys

from .development_history import NarrativeEvent
from .repository_annotations import (
    capture_repository_annotations,
    restore_repository_annotations,
)
from .repository_cli import main as repository_main
from .repository_coverage import repository_inventory_coverage
from .repository_git_store import git_history_status, replace_git_history
from .repository_inventory import refresh_repository_inventory
from .repository_store import (
    DEFAULT_REPOSITORY_DB,
    ensure_repository_schema,
    load_narrative_events,
    narrative_coverage,
)


def _connect(root: Path, database: Path) -> sqlite3.Connection:
    path = database if database.is_absolute() else root / database
    path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(path)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("PRAGMA foreign_keys=ON")
    conn.execute("PRAGMA busy_timeout=5000")
    ensure_repository_schema(conn)
    return conn


def _status(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo status",
        description="Report coverage of the unified repository-intelligence database.",
    )
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--database", type=Path, default=DEFAULT_REPOSITORY_DB)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    database = args.database if args.database.is_absolute() else root / args.database
    with _connect(root, args.database) as conn:
        semantic = repository_inventory_coverage(root, conn)
        narrative = narrative_coverage(conn)
        git = git_history_status(conn)
        counts = {}
        for table in (
            "modules",
            "repo_files",
            "repo_symbols",
            "repo_symbol_signatures",
            "narrative_events",
            "pull_requests",
            "git_commits",
            "git_commit_parents",
            "git_refs",
            "promotion_receipts",
        ):
            try:
                counts[table] = int(
                    conn.execute(f"SELECT count(*) FROM {table}").fetchone()[0]
                )
            except sqlite3.DatabaseError:
                counts[table] = 0
    print(f"database\t{database}")
    print(f"semantic_available\t{semantic.get('available', False)}")
    print(f"semantic_complete\t{semantic.get('complete', False)}")
    print(f"semantic_producer\t{semantic.get('producer')}")
    print(f"semantic_missing\t{len(semantic.get('missing', ()))}")
    print(f"semantic_stale\t{len(semantic.get('stale', ()))}")
    print(f"semantic_parse_errors\t{len(semantic.get('parse_errors', ()))}")
    print(f"narrative_available\t{narrative.get('available', False)}")
    print(f"narrative_complete\t{narrative.get('complete', False)}")
    print(f"git_complete\t{git.get('complete', False)}")
    for key in ("commits", "parent_edges", "refs", "commit_paths"):
        print(f"git_{key}\t{git[key]}")
    for table, count in counts.items():
        print(f"table_{table}\t{count}")
    return 0


def _index(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo index",
        description="Build the canonical whole-repo inventory with the preflight parser.",
    )
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--database", type=Path, default=DEFAULT_REPOSITORY_DB)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    with _connect(root, args.database) as conn:
        annotations = capture_repository_annotations(conn)
        result = refresh_repository_inventory(root, conn)
        result["annotations_restored"] = restore_repository_annotations(
            conn,
            annotations,
        )
    database = args.database if args.database.is_absolute() else root / args.database
    print(f"database\t{database}")
    for key in (
        "files",
        "symbols",
        "imports",
        "parse_errors",
        "annotations_restored",
        "elapsed_ms",
    ):
        print(f"{key}\t{result[key]}")
    for error in result["errors"]:
        print(f"parse_error\t{error['path']}\t{error['error']}")
    return 0 if not result["parse_errors"] else 2


def _harvest(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo harvest",
        description="Persist Git/PR development history into the shared DB.",
    )
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--database", type=Path, default=DEFAULT_REPOSITORY_DB)
    parser.add_argument("--github-prs")
    parser.add_argument("--max-commits", type=int)
    args = parser.parse_args(argv)
    root = args.root.resolve()

    forwarded = [
        "harvest",
        "--root",
        str(root),
        "--database",
        str(args.database),
    ]
    if args.github_prs:
        forwarded.extend(["--github-prs", args.github_prs])
    if args.max_commits is not None:
        forwarded.extend(["--max-commits", str(args.max_commits)])
    history_code = repository_main(forwarded)

    complete = args.max_commits is None
    with _connect(root, args.database) as conn:
        events = [
            NarrativeEvent.from_record(item)
            for item in load_narrative_events(conn)
        ]
        git_result = replace_git_history(
            conn,
            root,
            events,
            complete=complete,
        )
    for key in ("commits", "parent_edges", "refs", "commit_paths", "complete"):
        print(f"git_{key}\t{git_result[key]}")
    return history_code


def _bootstrap(argv) -> int:
    parser = argparse.ArgumentParser(
        prog="dashi-repo bootstrap",
        description="Build semantic inventory then harvest complete Git/PR history into one DB.",
    )
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--database", type=Path, default=DEFAULT_REPOSITORY_DB)
    parser.add_argument("--github-prs")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    index_code = _index(["--root", str(root), "--database", str(args.database)])
    forwarded = ["--root", str(root), "--database", str(args.database)]
    if args.github_prs:
        forwarded.extend(["--github-prs", args.github_prs])
    history_code = _harvest(forwarded)
    return max(index_code, history_code)


def main(argv=None) -> int:
    actual = list(sys.argv[1:] if argv is None else argv)
    if actual and actual[0] == "status":
        return _status(actual[1:])
    if actual and actual[0] == "index":
        return _index(actual[1:])
    if actual and actual[0] == "harvest":
        return _harvest(actual[1:])
    if actual and actual[0] == "bootstrap":
        return _bootstrap(actual[1:])
    return repository_main(actual)


if __name__ == "__main__":
    raise SystemExit(main())
