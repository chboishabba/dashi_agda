from copy import deepcopy

from dashi_repo_history.compact_history import (
    compact_timeline,
    expand_timeline,
    graph_patch,
    apply_graph_patch,
)


def _node(symbol_id, *, row=0):
    return {
        "symbol_id": symbol_id,
        "label": symbol_id,
        "kind": "function",
        "module": "M",
        "scope": None,
        "fingerprint": "fp",
        "span": {
            "path": "M.agda",
            "start_byte": row,
            "end_byte": row + 1,
            "start_row": row,
            "start_column": 0,
            "end_row": row,
            "end_column": 1,
        },
    }


def _edge(relation_id, source, target):
    return {
        "source": source,
        "target": target,
        "kind": "calls",
        "evidence": None,
        "relation_id": relation_id,
    }


def _graph(nodes, edges=(), graph_id="g"):
    return {
        "graph_id": graph_id,
        "nodes": list(nodes),
        "edges": list(edges),
        "unresolved_references": [],
        "parse_error_files": [],
    }


def test_graph_patch_roundtrip_handles_same_id_payload_update():
    before = _graph([_node("a", row=1)], graph_id="g1")
    after = _graph([_node("a", row=9), _node("b")], graph_id="g2")

    patch = graph_patch(before, after)
    patch["graph_id"] = after["graph_id"]
    rebuilt = apply_graph_patch(before, patch)

    assert rebuilt == after
    assert [node["symbol_id"] for node in patch["updated_nodes"]] == ["a"]


def test_compact_timeline_roundtrips_exactly():
    a = _graph([_node("a")], graph_id="ga")
    b = _graph(
        [_node("a"), _node("b")],
        [_edge("ab", "a", "b")],
        graph_id="gb",
    )
    c = _graph(
        [_node("a", row=5), _node("b"), _node("c")],
        [_edge("ab", "a", "b"), _edge("bc", "b", "c")],
        graph_id="gc",
    )

    timeline = {
        "schema": "dashi.repo-history.v1",
        "commits": [
            {"commit": "A", "timestamp": 1, "parents": [], "refs": [], "shape": "root"},
            {"commit": "B", "timestamp": 2, "parents": ["A"], "refs": [], "shape": "linear"},
            {"commit": "C", "timestamp": 3, "parents": ["B"], "refs": [], "shape": "linear"},
        ],
        "refs": {},
        "branch_episodes": [],
        "snapshots": [
            {"commit": "A", "graph": a, "parent_deltas": {}},
            {
                "commit": "B",
                "graph": b,
                "parent_deltas": {
                    "A": {
                        "added_nodes": ["b"],
                        "removed_nodes": [],
                        "added_edges": ["ab"],
                        "removed_edges": [],
                    }
                },
            },
            {
                "commit": "C",
                "graph": c,
                "parent_deltas": {
                    "B": {
                        "added_nodes": ["c"],
                        "removed_nodes": [],
                        "added_edges": ["bc"],
                        "removed_edges": [],
                    }
                },
            },
        ],
    }

    compact = compact_timeline(
        timeline,
        checkpoint_interval=10,
    )
    expanded = expand_timeline(compact)

    assert expanded == timeline
    assert len(compact["semantic_states"]) == 3
    assert "checkpoint" in compact["semantic_states"][0]
    assert "patch" in compact["semantic_states"][1]
    assert "patch" in compact["semantic_states"][2]


def test_missing_parent_in_selected_history_forces_checkpoint():
    timeline = {
        "schema": "dashi.repo-history.v1",
        "commits": [
            {"commit": "B", "timestamp": 2, "parents": ["A"], "refs": [], "shape": "linear"},
        ],
        "refs": {},
        "branch_episodes": [],
        "snapshots": [
            {
                "commit": "B",
                "graph": _graph([_node("b")], graph_id="gb"),
                "parent_deltas": {},
            }
        ],
    }

    compact = compact_timeline(timeline)

    assert "checkpoint" in compact["semantic_states"][0]
    assert compact["semantic_states"][0]["parent"] is None


def test_periodic_checkpoint_bounds_replay_length():
    snapshots = []
    commits = []
    for index in range(8):
        sha = f"C{index}"
        parent = [f"C{index - 1}"] if index else []
        commits.append(
            {
                "commit": sha,
                "timestamp": index,
                "parents": parent,
                "refs": [],
                "shape": "linear" if parent else "root",
            }
        )
        snapshots.append(
            {
                "commit": sha,
                "graph": _graph(
                    [_node(f"n{i}") for i in range(index + 1)],
                    graph_id=f"g{index}",
                ),
                "parent_deltas": {},
            }
        )

    compact = compact_timeline(
        {
            "schema": "dashi.repo-history.v1",
            "commits": commits,
            "refs": {},
            "branch_episodes": [],
            "snapshots": snapshots,
        },
        checkpoint_interval=3,
    )

    kinds = [
        "checkpoint" if "checkpoint" in state else "patch"
        for state in compact["semantic_states"]
    ]
    assert kinds == [
        "checkpoint",
        "patch",
        "patch",
        "patch",
        "checkpoint",
        "patch",
        "patch",
        "patch",
    ]


def test_compact_history_preserves_optional_pr_metadata_exactly():
    timeline = {
        "schema": "dashi.repo-history.v1",
        "commits": [
            {
                "commit": "A",
                "timestamp": 1,
                "parents": [],
                "refs": [],
                "shape": "root",
            }
        ],
        "refs": {},
        "branch_episodes": [],
        "pull_requests": [
            {
                "number": 7,
                "title": "Proof episode",
                "merge_commit": "A",
            }
        ],
        "snapshots": [
            {
                "commit": "A",
                "graph": _graph([_node("a")], graph_id="ga"),
                "parent_deltas": {},
            }
        ],
    }

    assert expand_timeline(compact_timeline(timeline)) == timeline
