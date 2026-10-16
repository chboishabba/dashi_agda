from dashi_repo_history.pr_events import parse_pr_records


def test_pr_event_retains_body_and_commit_membership_for_narrative_linkage():
    events = parse_pr_records([
        {
            "number": 42,
            "title": "Recover spatial C3",
            "body": "Recovered source-backed C3. Remaining leaf: A1 covariance.",
            "headRefName": "feature/c3",
            "baseRefName": "master",
            "createdAt": "2026-10-15T00:00:00Z",
            "mergedAt": None,
            "closedAt": None,
            "mergeCommit": None,
            "url": "https://example.invalid/pr/42",
            "commits": [{"oid": "abc"}, {"oid": "def"}],
        }
    ])
    event = events[0]
    assert event.body.startswith("Recovered")
    assert event.commits == ("abc", "def")
    narrative = event.to_narrative_event()
    assert narrative.event_id == "pr:42"
    assert narrative.pull_request == 42
    assert narrative.text == event.body
    assert narrative.authority == "development-narrative"
