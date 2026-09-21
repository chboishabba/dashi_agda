from dashi_repo_history.research_film import ProgrammeRegion
from dashi_repo_history.research_layout import ResearchAtlasLayout


def _node(symbol_id, module):
    return {
        "symbol_id": symbol_id,
        "label": symbol_id,
        "module": module,
        "kind": "function",
        "scope": None,
    }


def test_programmes_get_persistent_separate_territories():
    atlas = ResearchAtlasLayout(
        {
            "NavierStokes": ProgrammeRegion("NavierStokes", -10.0, 0.0),
            "RiemannHypothesis": ProgrammeRegion("RiemannHypothesis", 10.0, 0.0),
        }
    )
    graph = {
        "nodes": [
            _node("ns", "DASHI.Physics.NavierStokes"),
            _node("rh", "DASHI.Math.Riemann"),
        ],
        "edges": [],
    }

    positions = atlas.solve(graph)

    assert positions["ns"][0] < 0
    assert positions["rh"][0] > 0
    assert abs(positions["rh"][0] - positions["ns"][0]) > 10


def test_existing_programme_geometry_survives_other_programme_growth():
    atlas = ResearchAtlasLayout(
        {
            "NavierStokes": ProgrammeRegion("NavierStokes", -10.0, 0.0),
            "RiemannHypothesis": ProgrammeRegion("RiemannHypothesis", 10.0, 0.0),
        }
    )
    first = {
        "nodes": [_node("ns", "DASHI.Physics.NavierStokes")],
        "edges": [],
    }
    second = {
        "nodes": [
            _node("ns", "DASHI.Physics.NavierStokes"),
            _node("rh", "DASHI.Math.Riemann"),
        ],
        "edges": [],
    }

    before = atlas.solve(first)["ns"]
    after = atlas.solve(second)["ns"]

    assert before == after
