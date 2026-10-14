from pathlib import Path

from agda_preflight.repo_index_bridge import RepoIndexReader


def test_missing_repo_index_is_explicitly_incomplete(tmp_path: Path):
    with RepoIndexReader(tmp_path) as reader:
        status = reader.coverage_status()
    assert status["available"] is False
    assert status["complete"] is False
    assert status["state"] == "missing"
