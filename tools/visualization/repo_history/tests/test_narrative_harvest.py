from pathlib import Path
import subprocess

from dashi_repo_history.narrative_cli import collect_narrative_events


def _git(repo: Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=repo, text=True).strip()


def test_full_vs_bounded_commit_history_completeness_receipt(tmp_path: Path):
    _git(tmp_path, "init")
    _git(tmp_path, "config", "user.email", "test@example.com")
    _git(tmp_path, "config", "user.name", "Test")
    for index in range(2):
        (tmp_path / "x.txt").write_text(str(index), encoding="utf-8")
        _git(tmp_path, "add", "x.txt")
        _git(tmp_path, "commit", "-m", f"commit {index}")

    _events, full = collect_narrative_events(tmp_path)
    _events, bounded = collect_narrative_events(tmp_path, max_commits=1)
    assert full["commit_history_complete"] is True
    assert bounded["commit_history_complete"] is False
