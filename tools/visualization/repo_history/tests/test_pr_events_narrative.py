from dashi_repo_history.pr_events import PullRequestEvent, parse_pr_records


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


def test_cached_pr_event_round_trips_from_history_json_shape():
    original = PullRequestEvent(
        number=7,
        title="Historical frontier",
        head_ref="feature/x",
        base_ref="master",
        created_at=10,
        merged_at=20,
        closed_at=20,
        merge_commit="merge-sha",
        url="https://example.invalid/pr/7",
        body="Remaining leaf: physical source.",
        commits=("a", "b"),
    )
    restored = PullRequestEvent.from_dict(original.to_dict())
    assert restored == original
