from pathlib import Path
import subprocess

from dashi_repo_history.git_history import enrich_commit_messages, read_commit_dag


def _git(repo: Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=repo, text=True).strip()


def test_enrich_commit_messages_retains_subject_and_body(tmp_path: Path):
    _git(tmp_path, "init")
    _git(tmp_path, "config", "user.email", "test@example.com")
    _git(tmp_path, "config", "user.name", "Test")
    (tmp_path / "x.txt").write_text("x", encoding="utf-8")
    _git(tmp_path, "add", "x.txt")
    _git(tmp_path, "commit", "-m", "Recover C3 owner", "-m", "Actual remaining leaf: A1 covariance.\nKERNEL-PENDING.")

    records = read_commit_dag(tmp_path)
    enriched = enrich_commit_messages(tmp_path, records)
    assert enriched[-1].subject == "Recover C3 owner"
    assert "remaining leaf" in enriched[-1].body
    assert "KERNEL-PENDING" in enriched[-1].body
