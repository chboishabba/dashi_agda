from dashi_repo_history.scene_program import (
    compile_branch_episode_program,
    compile_first_parent_program,
    compile_merge_episode_program,
    compile_symbol_focus_program,
    compile_temporal_symbol_program,
)


def test_first_parent_program_uses_parent_relative_delta():
    timeline = {
        "commits": [
            {"commit": "A", "parents": []},
            {"commit": "B", "parents": ["A"]},
        ],
        "snapshots": [
            {"commit": "A", "parent_deltas": {}},
            {
                "commit": "B",
                "parent_deltas": {
                    "A": {
                        "added_nodes": ["n"],
                        "removed_nodes": [],
                        "added_edges": [],
                        "removed_edges": [],
                    }
                },
            },
        ],
    }

    commands = compile_first_parent_program(timeline)
    kinds = [command.kind for command in commands]
    assert kinds == [
        "show-snapshot",
        "advance-commit",
        "add-node",
        "settle-layout",
    ]
    assert commands[2].payload["node"] == "n"


def test_merge_program_contains_both_parent_deltas_and_convergence():
    timeline = {
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
            {"commit": "L", "parent_deltas": {}},
            {"commit": "R", "parent_deltas": {}},
            {
                "commit": "M",
                "parent_deltas": {
                    "L": {
                        "added_nodes": ["from-r"],
                        "removed_nodes": [],
                        "added_edges": [],
                        "removed_edges": [],
                    },
                    "R": {
                        "added_nodes": ["from-l"],
                        "removed_nodes": [],
                        "added_edges": [],
                        "removed_edges": [],
                    },
                },
            },
        ],
    }

    commands = compile_merge_episode_program(timeline, episode_index=0)
    parent_deltas = [
        command
        for command in commands
        if command.kind == "show-parent-delta"
    ]
    assert {command.payload["parent"] for command in parent_deltas} == {"L", "R"}
    assert any(command.kind == "converge-parents" for command in commands)


def test_branch_episode_program_walks_both_real_paths_before_merge():
    timeline = {
        "commits": [
            {"commit": "B", "parents": []},
            {"commit": "L1", "parents": ["B"]},
            {"commit": "R1", "parents": ["B"]},
            {"commit": "L2", "parents": ["L1"]},
            {"commit": "M", "parents": ["L2", "R1"]},
        ],
        "branch_episodes": [
            {
                "fork_base": "B",
                "left_tip": "L2",
                "right_tip": "R1",
                "merge_commit": "M",
                "left_path": ["B", "L1", "L2"],
                "right_path": ["B", "R1"],
            }
        ],
        "snapshots": [
            {"commit": "B", "parent_deltas": {}},
            {
                "commit": "L1",
                "parent_deltas": {
                    "B": {
                        "added_nodes": ["l1"],
                        "removed_nodes": [],
                        "added_edges": [],
                        "removed_edges": [],
                    }
                },
            },
            {
                "commit": "R1",
                "parent_deltas": {
                    "B": {
                        "added_nodes": ["r1"],
                        "removed_nodes": [],
                        "added_edges": [],
                        "removed_edges": [],
                    }
                },
            },
            {
                "commit": "L2",
                "parent_deltas": {
                    "L1": {
                        "added_nodes": ["l2"],
                        "removed_nodes": [],
                        "added_edges": [],
                        "removed_edges": [],
                    }
                },
            },
            {
                "commit": "M",
                "parent_deltas": {
                    "L2": {
                        "added_nodes": ["r1"],
                        "removed_nodes": [],
                        "added_edges": [],
                        "removed_edges": [],
                    },
                    "R1": {
                        "added_nodes": ["l1", "l2"],
                        "removed_nodes": [],
                        "added_edges": [],
                        "removed_edges": [],
                    },
                },
            },
        ],
    }

    commands = compile_branch_episode_program(
        timeline,
        episode_index=0,
    )
    assert [command.kind for command in commands[:2]] == [
        "show-fork-snapshot",
        "split-branches",
    ]

    advances = [
        command.payload
        for command in commands
        if command.kind == "advance-branch"
    ]
    assert advances == [
        {
            "side": "left",
            "parent": "B",
            "commit": "L1",
            "delta": timeline["snapshots"][1]["parent_deltas"]["B"],
        },
        {
            "side": "right",
            "parent": "B",
            "commit": "R1",
            "delta": timeline["snapshots"][2]["parent_deltas"]["B"],
        },
        {
            "side": "left",
            "parent": "L1",
            "commit": "L2",
            "delta": timeline["snapshots"][3]["parent_deltas"]["L1"],
        },
    ]
    assert commands[-2].kind == "converge-parents"
    assert commands[-1].kind == "show-snapshot"


def test_symbol_focus_program_reveals_root_before_layers():
    graph = {
        "nodes": [
            {"symbol_id": "x", "label": "x", "module": "M", "kind": "binder"},
            {"symbol_id": "g", "label": "g", "module": "M", "kind": "function"},
            {"symbol_id": "f", "label": "f", "module": "M", "kind": "function"},
        ],
        "edges": [
            {
                "relation_id": "x-g",
                "source": "x",
                "target": "g",
                "kind": "argument-to",
            },
            {
                "relation_id": "g-f",
                "source": "g",
                "target": "f",
                "kind": "calls",
            },
        ],
    }
    commands = compile_symbol_focus_program(
        graph,
        "f",
        upstream_depth=2,
    )
    assert commands[0].kind == "show-focus-root"
    assert commands[0].payload["node_ids"] == ["f"]
    assert [command.kind for command in commands[1:-1]] == [
        "expand-focus-layer",
        "expand-focus-layer",
    ]
    assert commands[-1].kind == "settle-focus"


def test_temporal_symbol_program_serializes_identity_evidence():
    timeline = {
        "commits": [
            {"commit": "A", "parents": []},
            {"commit": "B", "parents": ["A"]},
        ],
        "snapshots": [
            {
                "commit": "A",
                "graph": {
                    "nodes": [
                        {
                            "symbol_id": "old",
                            "label": "before",
                            "module": "M",
                            "kind": "function",
                            "scope": None,
                            "fingerprint": "fp",
                        }
                    ],
                    "edges": [],
                },
                "parent_deltas": {},
            },
            {
                "commit": "B",
                "graph": {
                    "nodes": [
                        {
                            "symbol_id": "new",
                            "label": "after",
                            "module": "M",
                            "kind": "function",
                            "scope": None,
                            "fingerprint": "fp",
                        }
                    ],
                    "edges": [],
                },
                "parent_deltas": {},
            },
        ],
    }
    commands = compile_temporal_symbol_program(timeline, "after")
    assert [command.kind for command in commands] == [
        "show-temporal-focus",
        "advance-temporal-focus",
    ]
    assert commands[1].payload["identity_evidence"] == (
        "unique-structural-fingerprint"
    )
