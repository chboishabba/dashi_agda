from dashi_repo_history.identity import match_node_identity


def _graph(nodes):
    return {"nodes": nodes, "edges": []}


def test_unique_fingerprint_supports_rename_identity():
    before = _graph(
        [
            {
                "symbol_id": "old",
                "label": "foo",
                "kind": "function",
                "fingerprint": "fp",
            }
        ]
    )
    after = _graph(
        [
            {
                "symbol_id": "new",
                "label": "bar",
                "kind": "function",
                "fingerprint": "fp",
            }
        ]
    )

    matches = match_node_identity(before, after)
    assert len(matches) == 1
    assert matches[0].evidence == "unique-structural-fingerprint"
    assert matches[0].confidence == "supported"


def test_ambiguous_fingerprint_is_not_promoted():
    before = _graph(
        [
            {"symbol_id": "a", "label": "a", "kind": "function", "fingerprint": "same"},
            {"symbol_id": "b", "label": "b", "kind": "function", "fingerprint": "same"},
        ]
    )
    after = _graph(
        [
            {"symbol_id": "c", "label": "c", "kind": "function", "fingerprint": "same"},
        ]
    )

    assert match_node_identity(before, after) == []
