from pathlib import Path
import sqlite3
import subprocess

from agda_preflight.development_history import read_commit_narrative_events
from agda_preflight.repository_git_store import (
    git_history_status,
    replace_git_history,
)
from agda_preflight.repository_store import ensure_repository_schema


def _git(repo: Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=repo, text=True).strip()


def _repo(tmp_path: Path) -> None:
    _git(tmp_path, "init")
    _git(tmp_path, "config", "user.email", "test@example.com")
    _git(tmp_path, "config", "user.name", "Test")
    for index in range(2):
        (tmp_path / "x.txt").write_text(str(index), encoding="utf-8")
        _git(tmp_path, "add", "x.txt")
        _git(tmp_path, "commit", "-m", f"commit {index}")


def _connection(tmp_path: Path) -> sqlite3.Connection:
    database = tmp_path / ".dashi" / "repository.sqlite3"
    database.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(database)
    conn.row_factory = sqlite3.Row
    ensure_repository_schema(conn)
    return conn


def test_git_history_is_relational_and_complete(tmp_path: Path):
    _repo(tmp_path)
    events = read_commit_narrative_events(tmp_path)
    conn = _connection(tmp_path)
    result = replace_git_history(conn, tmp_path, events)

    assert result["commits"] == 2
    assert result["parent_edges"] == 1
    assert result["commit_paths"] == 2
    assert result["complete"] is True
    assert conn.execute("SELECT count(*) FROM git_commits").fetchone()[0] == 2
    assert conn.execute("SELECT count(*) FROM git_commit_parents").fetchone()[0] == 1
    assert conn.execute(
        "SELECT count(*) FROM git_commit_paths WHERE path='x.txt'"
    ).fetchone()[0] == 2
    status = git_history_status(conn)
    assert status["complete"] is True
    assert status["commits"] == 2
    conn.close()


def test_bounded_git_history_is_relational_but_not_complete(tmp_path: Path):
    _repo(tmp_path)
    events = read_commit_narrative_events(tmp_path, max_commits=1)
    conn = _connection(tmp_path)
    result = replace_git_history(conn, tmp_path, events, complete=False)
    assert result["commits"] == 1
    assert result["complete"] is False
    status = git_history_status(conn)
    assert status["complete"] is False
    assert status["commits"] == 1
    conn.close()
