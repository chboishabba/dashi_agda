from dashi_repo_history.temporal_focus import track_symbol_history


def _node(symbol_id, label, fingerprint):
    return {
        "symbol_id": symbol_id,
        "label": label,
        "module": "M",
        "kind": "function",
        "scope": None,
        "fingerprint": fingerprint,
    }


def _snapshot(commit, nodes):
    return {
        "commit": commit,
        "graph": {
            "nodes": nodes,
            "edges": [],
        },
        "parent_deltas": {},
    }


def test_temporal_focus_tracks_exact_identity_backwards():
    timeline = {
        "commits": [
            {"commit": "A", "parents": []},
            {"commit": "B", "parents": ["A"]},
        ],
        "snapshots": [
            _snapshot("A", [_node("same", "f", "fp")]),
            _snapshot("B", [_node("same", "f", "fp")]),
        ],
    }

    frames = track_symbol_history(timeline, "f")
    assert [frame.commit for frame in frames] == ["A", "B"]
    assert [frame.root_id for frame in frames] == ["same", "same"]


def test_temporal_focus_tracks_unique_supported_rename():
    timeline = {
        "commits": [
            {"commit": "A", "parents": []},
            {"commit": "B", "parents": ["A"]},
        ],
        "snapshots": [
            _snapshot("A", [_node("old", "before", "same-fingerprint")]),
            _snapshot("B", [_node("new", "after", "same-fingerprint")]),
        ],
    }

    frames = track_symbol_history(timeline, "after")
    assert [frame.root_id for frame in frames] == ["old", "new"]
    assert frames[0].identity_evidence == "introduction-or-earliest-match"
    assert frames[1].identity_evidence == "unique-structural-fingerprint"


def test_temporal_focus_stops_at_symbol_introduction():
    timeline = {
        "commits": [
            {"commit": "A", "parents": []},
            {"commit": "B", "parents": ["A"]},
        ],
        "snapshots": [
            _snapshot("A", []),
            _snapshot("B", [_node("new", "f", "fp")]),
        ],
    }

    frames = track_symbol_history(timeline, "f")
    assert [frame.commit for frame in frames] == ["B"]
