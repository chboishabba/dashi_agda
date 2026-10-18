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


def test_commit_subjects_are_loaded_in_batches(monkeypatch, tmp_path: Path):
    calls = []

    def fake_run_text(repo, *args):
        calls.append(args)
        if args[0] == "show":
            shas = [
                value
                for value in args
                if value.startswith("c")
            ]
            return "".join(
                f"{sha}\x00subject-{sha}\n"
                for sha in shas
            )
        raise AssertionError(args)

    monkeypatch.setattr(git_history, "_run_text", fake_run_text)

    records = [
        git_history.CommitRecord(
            commit=f"c{i}",
            timestamp=i,
            parents=(),
        )
        for i in range(5)
    ]
    enriched = git_history.enrich_commit_subjects(
        tmp_path,
        records,
        batch_size=2,
    )

    assert [record.subject for record in enriched] == [
        f"subject-c{i}"
        for i in range(5)
    ]
    show_calls = [args for args in calls if args[0] == "show"]
    assert len(show_calls) == 3
