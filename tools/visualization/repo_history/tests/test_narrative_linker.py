from dashi_repo_history.narrative import NarrativeEvent
from dashi_repo_history.narrative_index import link_events_to_history


def test_link_events_to_history_resolves_delta_ids_to_plain_symbol_names():
    payload = {
        "snapshots": [
            {
                "commit": "parent",
                "graph": {
                    "nodes": [
                        {"symbol_id": "bar-id", "module": "DASHI.Core.Old", "label": "Bar"}
                    ]
                },
                "parent_deltas": {},
            },
            {
                "commit": "child",
                "graph": {
                    "nodes": [
                        {"symbol_id": "foo-id", "module": "DASHI.Core.New", "label": "Foo"}
                    ]
                },
                "parent_deltas": {
                    "parent": {
                        "added_nodes": ["foo-id"],
                        "removed_nodes": ["bar-id"],
                        "added_edges": [],
                        "removed_edges": [],
                    }
                },
            },
        ]
    }
    event = NarrativeEvent(
        event_id="commit:child",
        timestamp=2,
        kind="commit",
        title="Replace Bar with Foo",
        commit="child",
    )
    linked = link_events_to_history([event], payload)[0]
    assert "DASHI.Core.New::Foo" in linked.introduced_objects
    assert "DASHI.Core.Old::Bar" in linked.removed_objects
    assert set(linked.touched_objects) >= {
        "DASHI.Core.New::Foo",
        "DASHI.Core.Old::Bar",
    }
