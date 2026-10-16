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
from .repository_git_store import replace_git_history
from .repository_inventory import refresh_repository_inventory
from .repository_store import (
    DEFAULT_REPOSITORY_DB,
    ensure_repository_schema,
    load_narrative_events,
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
    if actual and actual[0] == "index":
        return _index(actual[1:])
    if actual and actual[0] == "harvest":
        return _harvest(actual[1:])
    if actual and actual[0] == "bootstrap":
        return _bootstrap(actual[1:])
    return repository_main(actual)


if __name__ == "__main__":
    raise SystemExit(main())
