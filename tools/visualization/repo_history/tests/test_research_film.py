from dashi_repo_history.research_film import (
    compile_research_film,
    programme_key,
)


def _node(symbol_id, label, module):
    return {
        "symbol_id": symbol_id,
        "label": label,
        "module": module,
        "kind": "function",
        "scope": None,
        "fingerprint": None,
        "span": {
            "path": module.replace(".", "/") + ".agda",
            "start_byte": 0,
            "end_byte": 1,
            "start_row": 0,
            "start_column": 0,
            "end_row": 0,
            "end_column": 1,
        },
    }


def _snapshot(commit, nodes, edges=(), delta=None, parent=None):
    return {
        "commit": commit,
        "graph": {
            "graph_id": commit,
            "nodes": list(nodes),
            "edges": list(edges),
            "unresolved_references": [],
            "parse_error_files": [],
        },
        "parent_deltas": (
            {parent: delta}
            if parent and delta is not None
            else {}
        ),
    }


def test_programme_inference_normalises_known_research_names():
    assert programme_key(
        "DASHI.Physics.NavierStokes.NSTriad",
        "R571Bound",
    ) == "NavierStokes"
    assert programme_key(
        "DASHI.Math.Riemann.Gamma",
        "zetaMain",
    ) == "RiemannHypothesis"
    assert programme_key(
        "DASHI.Cuisine.Flavour",
        "stock",
    ) == "Cuisine"


def test_film_returns_camera_to_existing_programme_region():
    ns_a = _node("ns-a", "NSTriadR571", "DASHI.Physics.NavierStokes")
    rh = _node("rh", "GammaDeficit", "DASHI.Math.Riemann")
    ns_b = _node("ns-b", "FixedOutput", "DASHI.Physics.NavierStokes")

    timeline = {
        "commits": [
            {"commit": "A", "timestamp": 0, "parents": []},
            {"commit": "B", "timestamp": 10, "parents": ["A"]},
            {"commit": "C", "timestamp": 20, "parents": ["B"]},
        ],
        "snapshots": [
            _snapshot("A", [ns_a]),
            _snapshot(
                "B",
                [ns_a, rh],
                delta={
                    "added_nodes": ["rh"],
                    "removed_nodes": [],
                    "added_edges": [],
                    "removed_edges": [],
                },
                parent="A",
            ),
            _snapshot(
                "C",
                [ns_a, rh, ns_b],
                delta={
                    "added_nodes": ["ns-b"],
                    "removed_nodes": [],
                    "added_edges": [],
                    "removed_edges": [],
                },
                parent="B",
            ),
        ],
        "refs": {},
        "branch_episodes": [],
    }

    plan = compile_research_film(timeline)
    programmes = [episode.programme for episode in plan.episodes]

    assert programmes == [
        "NavierStokes",
        "RiemannHypothesis",
        "NavierStokes",
    ]
    assert plan.episodes[-1].return_to_existing_region is True

    returning = [
        beat
        for beat in plan.beats
        if beat.kind == "episode-title"
        and beat.programme == "NavierStokes"
    ][-1]
    assert returning.camera is not None
    assert returning.camera.reason == "return-to-existing-programme"


def test_low_level_commits_same_topic_coalesce_into_episode():
    a = _node("a", "R571Bound", "DASHI.Physics.NavierStokes")
    b = _node("b", "R571Estimate", "DASHI.Physics.NavierStokes")

    timeline = {
        "commits": [
            {"commit": "A", "timestamp": 0, "parents": []},
            {"commit": "B", "timestamp": 60, "parents": ["A"]},
        ],
        "snapshots": [
            _snapshot("A", [a]),
            _snapshot(
                "B",
                [a, b],
                delta={
                    "added_nodes": ["b"],
                    "removed_nodes": [],
                    "added_edges": [],
                    "removed_edges": [],
                },
                parent="A",
            ),
        ],
        "refs": {},
        "branch_episodes": [],
    }

    plan = compile_research_film(timeline)
    assert len(plan.episodes) == 1
    assert plan.episodes[0].commits == ("A", "B")
