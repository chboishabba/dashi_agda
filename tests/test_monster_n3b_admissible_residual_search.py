from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "monster_n3b_admissible_residual_search.py"


def load_runtime():
    spec = importlib.util.spec_from_file_location("monster_n3b_admissible_residual_search", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def seventeen_worlds():
    return [
        {
            "world_id": f"fusion-{i:02d}",
            "character_compatible": True,
            "character_observer": "same-17-way-character-fibre",
            "d8_conjugacy_class": None,
            "monster_class_fusion": None,
            "power_42b14_to_3b": None,
            "power_42b7_to_6b": None,
            "five_orbit_character": [5, 5, 1, 3, 3],
            "action_intertwiner_paid": False,
        }
        for i in range(17)
    ]


def test_character_observer_is_a_17_way_collision_and_scheduler_opens_r1_only():
    runtime = load_runtime()
    report = runtime.analyze_worlds(seventeen_worlds())

    assert report["candidate_count"] == 17
    assert report["character_collision_size"] == 17
    assert report["opened_coordinates"] == ["d8_conjugacy_class"]
    assert report["next_coordinate"] == "d8_conjugacy_class"
    assert report["matrix_payload_loaded"] is False


def test_scheduler_reopens_only_the_remaining_collision_fibre():
    runtime = load_runtime()
    worlds = seventeen_worlds()
    for i, world in enumerate(worlds):
        world["d8_conjugacy_class"] = f"class-{i // 2}"
    report = runtime.analyze_worlds(worlds)

    assert report["opened_coordinates"] == ["d8_conjugacy_class", "monster_class_fusion"]
    assert report["largest_remaining_collision"] == 2
    assert report["matrix_payload_loaded"] is False


def test_quotient_permutation_route_pareto_dominates_matrix_route_for_current_consumer():
    runtime = load_runtime()
    costs = runtime.route_costs()

    assert runtime.weakly_dominates(costs["quotient-permutation"], costs["matrix-78"])
    assert not runtime.weakly_dominates(costs["matrix-78"], costs["quotient-permutation"])
    assert costs["quotient-permutation"]["matrix_dimension"] == 0
    assert costs["matrix-78"]["matrix_dimension"] == 78


def test_runtime_keeps_same_object_and_action_authority_unpaid():
    runtime = load_runtime()
    report = runtime.analyze_worlds(seventeen_worlds())

    assert report["consumer"] == "which admissible D8 realization/fusion supplies the five-orbit action?"
    assert report["character_table_observer_sufficient"] is False
    assert report["quotient_route_creates_selected_action"] is False
    assert report["runtime_search_creates_factors_through_theorem"] is False
