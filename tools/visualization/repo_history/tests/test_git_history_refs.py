from pathlib import Path

from dashi_repo_history import git_history


def test_explicit_history_ref_replaces_all(monkeypatch, tmp_path: Path):
    calls = []

    def fake_run_text(repo, *args):
        calls.append(args)
        if args[0] == "for-each-ref":
            return ""
        if args[0] == "rev-list":
            return "100 abcdef\n"
        raise AssertionError(args)

    monkeypatch.setattr(git_history, "_run_text", fake_run_text)

    commits = git_history.read_commit_dag(
        tmp_path,
        history_refs=["HEAD"],
    )

    rev = next(args for args in calls if args[0] == "rev-list")
    assert "--all" not in rev
    assert "HEAD" in rev
    assert commits[0].commit == "abcdef"


def test_default_history_root_is_all(monkeypatch, tmp_path: Path):
    calls = []

    def fake_run_text(repo, *args):
        calls.append(args)
        if args[0] == "for-each-ref":
            return ""
        if args[0] == "rev-list":
            return "100 abcdef\n"
        raise AssertionError(args)

    monkeypatch.setattr(git_history, "_run_text", fake_run_text)

    git_history.read_commit_dag(tmp_path)

    rev = next(args for args in calls if args[0] == "rev-list")
    assert "--all" in rev
