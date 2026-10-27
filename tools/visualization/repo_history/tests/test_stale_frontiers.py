from dashi_repo_history.narrative import NarrativeEvent, stale_frontiers


def test_stale_frontiers_marks_earlier_open_claim_when_later_delta_overlaps():
    events = [
        NarrativeEvent(
            event_id="commit:old",
            timestamp=1,
            kind="commit",
            title="Balaban audit",
            text="Literal spatial C3 action remains open.",
        ),
        NarrativeEvent(
            event_id="commit:new",
            timestamp=2,
            kind="commit",
            title="Recover Balaban C3",
            text="Recovered literal spatial C3 action. Remaining leaf: A1 covariance.",
        ),
    ]
    rows = stale_frontiers(events, "spatial C3")
    assert rows
    assert rows[0]["event_id"] == "commit:old"
    assert rows[0]["potentially_superseded_by"] == "commit:new"
    assert rows[0]["authority"] == "development-narrative-heuristic"
