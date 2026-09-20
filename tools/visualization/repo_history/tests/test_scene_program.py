from dashi_repo_history.scene_program import (
    compile_first_parent_program,
    compile_merge_episode_program,
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
