from __future__ import annotations

from pathlib import Path
import subprocess

from .narrative import NarrativeEvent


def _run_bytes(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=repo)


def _run_text(repo: Path, *args: str) -> str:
    return _run_bytes(repo, *args).decode("utf-8", "replace")


def _changed_paths(repo: Path, commit: str) -> tuple[str, ...]:
    raw = _run_bytes(
        repo,
        "diff-tree",
        "--root",
        "--no-commit-id",
        "--name-only",
        "-r",
        "-z",
        commit,
    )
    return tuple(
        sorted(
            {
                item.decode("utf-8", "replace")
                for item in raw.split(b"\0")
                if item
            }
        )
    )


def read_commit_narrative_events(
    repo: Path,
    *,
    refs: tuple[str, ...] = ("HEAD",),
    max_commits: int | None = None,
) -> list[NarrativeEvent]:
    """Read commit prose and changed paths as development-narrative events.

    Commit prose guides discovery and intent archaeology only. It never becomes
    formal or empirical authority merely by appearing in Git history.
    """

    repo = repo.resolve()
    rev_args = ["rev-list", "--reverse", "--topo-order", *refs]
    commits = [item for item in _run_text(repo, *rev_args).splitlines() if item]
    if max_commits is not None:
        commits = commits[-max(0, max_commits):]

    events: list[NarrativeEvent] = []
    for commit in commits:
        raw = _run_text(
            repo,
            "show",
            "-s",
            "--format=%ct%x00%s%x00%b",
            commit,
        ).rstrip("\n")
        parts = raw.split("\x00", 2)
        if len(parts) != 3:
            continue
        timestamp_text, subject, body = parts
        try:
            timestamp = int(timestamp_text)
        except ValueError:
            timestamp = 0
        events.append(
            NarrativeEvent(
                event_id=f"commit:{commit}",
                timestamp=timestamp,
                kind="commit",
                title=subject.strip(),
                text=body.strip(),
                commit=commit,
                touched_paths=_changed_paths(repo, commit),
            )
        )
    return events
