from dashi_repo_history.pr_events import parse_pr_records


def test_pr_record_parses_merge_commit_and_times():
    events = parse_pr_records(
        [
            {
                "number": 1016,
                "title": "Temporal semantic visualization",
                "headRefName": "agent/visual",
                "baseRefName": "master",
                "createdAt": "2026-09-20T00:00:00Z",
                "mergedAt": "2026-09-21T01:00:00Z",
                "closedAt": "2026-09-21T01:00:00Z",
                "mergeCommit": {"oid": "abc"},
                "url": "https://example.invalid/pr/1016",
            }
        ]
    )

    assert events[0].number == 1016
    assert events[0].merge_commit == "abc"
    assert events[0].merged_at is not None
