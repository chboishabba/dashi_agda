from __future__ import annotations

from pathlib import Path
import sqlite3
import subprocess
from typing import Any, Iterable

from .development_history import NarrativeEvent
from .repository_store import ensure_repository_schema


def ensure_git_schema(conn: sqlite3.Connection) -> None:
    ensure_repository_schema(conn)
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS git_commits (
            commit_sha TEXT PRIMARY KEY,
            timestamp INTEGER NOT NULL,
            subject TEXT NOT NULL,
            body TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS git_commits_timestamp
            ON git_commits(timestamp, commit_sha);

        CREATE TABLE IF NOT EXISTS git_commit_parents (
            commit_sha TEXT NOT NULL REFERENCES git_commits(commit_sha) ON DELETE CASCADE,
            ordinal INTEGER NOT NULL,
            parent_sha TEXT NOT NULL,
            PRIMARY KEY(commit_sha, ordinal)
        ) WITHOUT ROWID;
        CREATE INDEX IF NOT EXISTS git_commit_parents_parent
            ON git_commit_parents(parent_sha);

        CREATE TABLE IF NOT EXISTS git_refs (
            ref_name TEXT PRIMARY KEY,
            ref_kind TEXT NOT NULL,
            commit_sha TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS git_refs_commit ON git_refs(commit_sha);

        CREATE TABLE IF NOT EXISTS git_commit_paths (
            commit_sha TEXT NOT NULL REFERENCES git_commits(commit_sha) ON DELETE CASCADE,
            path TEXT NOT NULL,
            PRIMARY KEY(commit_sha, path)
        ) WITHOUT ROWID;
        CREATE INDEX IF NOT EXISTS git_commit_paths_path
            ON git_commit_paths(path, commit_sha);
        """
    )
    conn.commit()


def _run(repo: Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=repo, text=True)


def _parents(repo: Path, commits: set[str]) -> dict[str, tuple[str, ...]]:
    if not commits:
        return {}
    raw = _run(repo, "rev-list", "--parents", "--all")
    result: dict[str, tuple[str, ...]] = {}
    for line in raw.splitlines():
        fields = line.split()
        if not fields:
            continue
        commit = fields[0]
        if commit in commits:
            result[commit] = tuple(fields[1:])
    return result


def _refs(repo: Path) -> list[tuple[str, str, str]]:
    raw = _run(
        repo,
        "for-each-ref",
        "--format=%(refname)%00%(objectname)",
        "refs/heads",
        "refs/remotes",
        "refs/tags",
    )
    rows = []
    for line in raw.splitlines():
        if "\x00" not in line:
            continue
        ref_name, commit = line.split("\x00", 1)
        if ref_name.startswith("refs/heads/"):
            kind = "head"
        elif ref_name.startswith("refs/remotes/"):
            kind = "remote"
        elif ref_name.startswith("refs/tags/"):
            kind = "tag"
        else:
            kind = "other"
        rows.append((ref_name, kind, commit))
    return rows


def replace_git_history(
    conn: sqlite3.Connection,
    repo: Path,
    events: Iterable[NarrativeEvent],
    *,
    complete: bool = True,
) -> dict[str, Any]:
    """Persist commit DAG, refs and touched paths from harvested Git events."""

    ensure_git_schema(conn)
    commits = [event for event in events if event.kind == "commit" and event.commit]
    commit_ids = {str(event.commit) for event in commits if event.commit}
    parents = _parents(repo, commit_ids)
    refs = _refs(repo)

    conn.execute("DELETE FROM git_commit_paths")
    conn.execute("DELETE FROM git_commit_parents")
    conn.execute("DELETE FROM git_refs")
    conn.execute("DELETE FROM git_commits")

    for event in commits:
        commit = str(event.commit)
        conn.execute(
            "INSERT INTO git_commits(commit_sha, timestamp, subject, body) VALUES(?, ?, ?, ?)",
            (commit, int(event.timestamp), event.title, event.text),
        )
        for ordinal, parent in enumerate(parents.get(commit, ())):
            conn.execute(
                "INSERT INTO git_commit_parents(commit_sha, ordinal, parent_sha) VALUES(?, ?, ?)",
                (commit, ordinal, parent),
            )
        for path in event.touched_paths:
            conn.execute(
                "INSERT OR IGNORE INTO git_commit_paths(commit_sha, path) VALUES(?, ?)",
                (commit, path),
            )

    for ref_name, kind, commit in refs:
        conn.execute(
            "INSERT INTO git_refs(ref_name, ref_kind, commit_sha) VALUES(?, ?, ?)",
            (ref_name, kind, commit),
        )

    conn.execute(
        "INSERT INTO repository_meta(key, value) VALUES('git_history_complete', ?) "
        "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
        ("true" if complete else "false",),
    )
    conn.commit()
    return {
        "commits": len(commits),
        "parent_edges": sum(len(value) for value in parents.values()),
        "refs": len(refs),
        "commit_paths": sum(len(event.touched_paths) for event in commits),
        "complete": complete,
    }


def git_history_status(conn: sqlite3.Connection) -> dict[str, Any]:
    ensure_git_schema(conn)
    row = conn.execute(
        "SELECT value FROM repository_meta WHERE key='git_history_complete'"
    ).fetchone()
    return {
        "complete": bool(row and str(row[0]).lower() == "true"),
        "commits": int(conn.execute("SELECT count(*) FROM git_commits").fetchone()[0]),
        "parent_edges": int(conn.execute("SELECT count(*) FROM git_commit_parents").fetchone()[0]),
        "refs": int(conn.execute("SELECT count(*) FROM git_refs").fetchone()[0]),
        "commit_paths": int(conn.execute("SELECT count(*) FROM git_commit_paths").fetchone()[0]),
    }
