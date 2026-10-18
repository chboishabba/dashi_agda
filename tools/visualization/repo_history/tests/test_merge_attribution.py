from dashi_repo_history.merge_attribution import attribute_merge


def _snapshot(commit, nodes, edges=()):
    return {
        "commit": commit,
        "graph": {
            "nodes": [{"symbol_id": n} for n in nodes],
            "edges": [{"relation_id": e} for e in edges],
        },
    }


def test_merge_attribution_separates_parent_and_merge_contributions():
    snapshots = {
        "left": _snapshot("left", ["common", "left-only"], ["e-common", "e-left"]),
        "right": _snapshot("right", ["common", "right-only"], ["e-common", "e-right"]),
        "merge": _snapshot(
            "merge",
            ["common", "left-only", "right-only", "merge-only"],
            ["e-common", "e-left", "e-right", "e-merge"],
        ),
    }
    commit = {
        "commit": "merge",
        "parents": ["left", "right"],
    }

    result = attribute_merge(
        merge_commit=commit,
        snapshots_by_commit=snapshots,
    )

    assert result.common_nodes == ("common",)
    assert result.parent_only_nodes["left"] == ("left-only",)
    assert result.parent_only_nodes["right"] == ("right-only",)
    assert result.introduced_nodes == ("merge-only",)
    assert result.introduced_edges == ("e-merge",)
