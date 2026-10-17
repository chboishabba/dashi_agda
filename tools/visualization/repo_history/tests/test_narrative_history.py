from dashi_repo_history.narrative import (
    NarrativeEvent,
    archaeology,
    classify_narrative,
    frontier_genealogy,
    link_event_to_semantic_delta,
)
from dashi_repo_history.model import GraphDelta


def test_classify_narrative_separates_frontier_nonclaims_and_verification():
    text = """
    Recovered the source-backed C3 action and closed the old carrier gap.
    Actual remaining physical leaf: canonical A1 B4 covariance witness.
    This does not establish a measured gravitational backreaction.
    Status: SOURCE-WRITTEN / KERNEL-PENDING.
    """
    result = classify_narrative(text)
    assert any("Recovered" in item for item in result["claimed_delta"])
    assert any("remaining physical leaf" in item for item in result["frontier"])
    assert any("does not establish" in item for item in result["nonclaims"])
    assert any("KERNEL-PENDING" in item for item in result["verification"])


def test_archaeology_prefers_object_and_frontier_overlap_over_raw_text_frequency():
    events = [
        NarrativeEvent(
            event_id="commit:a",
            timestamp=1,
            kind="commit",
            title="Recover Balaban spatial C3 action",
            text="Recovered literal source-backed C3. Remaining leaf is A1 B4 covariance.",
            touched_objects=("DASHI.Physics.BalabanSpatialC3",),
        ),
        NarrativeEvent(
            event_id="pr:2",
            timestamp=2,
            kind="pull_request",
            title="Unrelated C3 prose",
            text="C3 C3 C3 C3 discussion only.",
            touched_objects=("DASHI.Other.Unrelated",),
        ),
    ]
    ranked = archaeology(events, "Balaban C3 covariance")
    assert ranked[0]["event"].event_id == "commit:a"
    assert ranked[0]["score"] > ranked[1]["score"]


def test_frontier_genealogy_tracks_paid_replaced_and_remaining_language_in_time_order():
    events = [
        NarrativeEvent(
            event_id="commit:old",
            timestamp=10,
            kind="commit",
            title="Old frontier",
            text="Literal C3 action remains open.",
        ),
        NarrativeEvent(
            event_id="commit:new",
            timestamp=20,
            kind="commit",
            title="Recover C3",
            text="Recovered literal C3 action. Actual remaining leaf: A1 covariance.",
        ),
    ]
    genealogy = frontier_genealogy(events, "C3")
    assert [item["event_id"] for item in genealogy] == ["commit:old", "commit:new"]
    assert genealogy[0]["frontier"]
    assert genealogy[1]["claimed_delta"]
    assert genealogy[1]["frontier"]


def test_semantic_delta_links_added_and_removed_symbol_ids_without_promoting_narrative_authority():
    event = NarrativeEvent(
        event_id="commit:abc",
        timestamp=1,
        kind="commit",
        title="Introduce object",
        text="Introduce Foo and retire Bar.",
    )
    delta = GraphDelta(
        added_nodes=("foo-id",),
        removed_nodes=("bar-id",),
    )
    linked = link_event_to_semantic_delta(event, delta)
    assert linked.introduced_objects == ("foo-id",)
    assert linked.removed_objects == ("bar-id",)
    assert linked.authority == "development-narrative"
    assert linked.may_establish_formal_fact is False
    assert linked.may_establish_empirical_fact is False
