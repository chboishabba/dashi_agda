from pathlib import Path
import subprocess

from dashi_repo_history.narrative_git import read_commit_narrative_events


def _git(repo: Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=repo, text=True).strip()


def test_read_commit_narrative_events_retains_subject_body_and_changed_paths(tmp_path: Path):
    _git(tmp_path, "init")
    _git(tmp_path, "config", "user.email", "test@example.com")
    _git(tmp_path, "config", "user.name", "Test")
    (tmp_path / "x.txt").write_text("x", encoding="utf-8")
    _git(tmp_path, "add", "x.txt")
    _git(tmp_path, "commit", "-m", "Recover C3 owner", "-m", "Actual remaining leaf: A1 covariance.\nKERNEL-PENDING.")

    events = read_commit_narrative_events(tmp_path, refs=("HEAD",))
    event = events[-1]
    assert event.title == "Recover C3 owner"
    assert "remaining leaf" in event.text
    assert "KERNEL-PENDING" in event.text
    assert event.touched_paths == ("x.txt",)
    assert event.authority == "development-narrative"
