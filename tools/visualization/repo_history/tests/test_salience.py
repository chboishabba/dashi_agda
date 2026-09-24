from dashi_repo_history.salience import rank_episodes, score_episode


def test_episode_salience_counts_real_branch_deltas_and_merge_only_nodes():
    timeline = {
        "commits": [
            {"commit": "B", "parents": []},
            {"commit": "L", "parents": ["B"]},
            {"commit": "R", "parents": ["B"]},
            {"commit": "M", "parents": ["L", "R"]},
        ],
        "branch_episodes": [
            {
                "fork_base": "B",
                "left_tip": "L",
                "right_tip": "R",
                "merge_commit": "M",
                "left_path": ["B", "L"],
                "right_path": ["B", "R"],
            }
        ],
        "snapshots": [
            {
                "commit": "B",
                "graph": {"nodes": [{"symbol_id": "base"}], "edges": []},
                "parent_deltas": {},
            },
            {
                "commit": "L",
                "graph": {
                    "nodes": [
                        {"symbol_id": "base"},
                        {"symbol_id": "left"},
                    ],
                    "edges": [],
                },
                "parent_deltas": {
                    "B": {
                        "added_nodes": ["left"],
                        "removed_nodes": [],
                        "added_edges": [],
                        "removed_edges": [],
                    }
                },
            },
            {
                "commit": "R",
                "graph": {
                    "nodes": [
                        {"symbol_id": "base"},
                        {"symbol_id": "right"},
                    ],
                    "edges": [],
                },
                "parent_deltas": {
                    "B": {
                        "added_nodes": ["right"],
                        "removed_nodes": [],
                        "added_edges": [],
                        "removed_edges": [],
                    }
                },
            },
            {
                "commit": "M",
                "graph": {
                    "nodes": [
                        {"symbol_id": "base"},
                        {"symbol_id": "left"},
                        {"symbol_id": "right"},
                        {"symbol_id": "merge-only"},
                    ],
                    "edges": [],
                },
                "parent_deltas": {
                    "L": {
                        "added_nodes": ["right", "merge-only"],
                        "removed_nodes": [],
                        "added_edges": [],
                        "removed_edges": [],
                    },
                    "R": {
                        "added_nodes": ["left", "merge-only"],
                        "removed_nodes": [],
                        "added_edges": [],
                        "removed_edges": [],
                    },
                },
            },
        ],
    }

    score = score_episode(timeline, 0)
    assert score.branch_node_churn == 2
    assert score.branch_steps == 2
    assert score.merge_only_nodes == 1
    assert score.score == 15


def test_rank_episodes_is_descending_and_stable_by_original_index():
    timeline = {
        "commits": [],
        "snapshots": [],
        "branch_episodes": [
            {
                "fork_base": "A",
                "left_tip": "A",
                "right_tip": "A",
                "merge_commit": "X",
                "left_path": ["A"],
                "right_path": ["A"],
            },
            {
                "fork_base": "B",
                "left_tip": "B",
                "right_tip": "B",
                "merge_commit": "Y",
                "left_path": ["B"],
                "right_path": ["B"],
            },
        ],
    }
    ranked = rank_episodes(timeline)
    assert [item.episode_index for item in ranked] == [0, 1]
