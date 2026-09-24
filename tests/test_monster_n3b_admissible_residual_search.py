from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "monster_n3b_admissible_residual_search.py"
FIXTURE = ROOT / "build" / "monster_3b_five_orbit_d4_n3b_screen.json"


def load_runtime():
    spec = importlib.util.spec_from_file_location("monster_n3b_admissible_residual_search", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def load_literal_worlds(runtime):
    assert FIXTURE.exists(), "run scripts/monster_3b_five_orbit_d4_n3b_screen.g first"
    return runtime.load_worlds_from_screen_receipt(FIXTURE)


def test_loader_consumes_all_17_literal_fusion_rows_and_preserves_central_split():
    runtime = load_runtime()
    worlds = load_literal_worlds(runtime)

    assert len(worlds) == 17
    assert all(world["character_compatible"] is True for world in worlds)
    assert all(world["d8_conjugacy_class"] is not None for world in worlds)
    assert all(world["monster_class_fusion"] is not None for world in worlds)
    assert all(len(world["monster_class_fusion"]) == 5 for world in worlds)

    labels = [world["central_monster_class"] for world in worlds]
    assert labels.count("2A") == 9
    assert labels.count("2B") == 8


def test_loader_rejects_count_only_or_placeholder_receipts(tmp_path):
    runtime = load_runtime()
    count_only = tmp_path / "count-only.json"
    count_only.write_text(json.dumps({"character_compatible_fusion_count": 17}))

    try:
        runtime.load_worlds_from_screen_receipt(count_only)
    except ValueError as exc:
        assert "literal character-compatible fusion rows" in str(exc)
    else:
        raise AssertionError("count-only receipt must not create scheduler worlds")


def test_character_observer_is_a_17_way_collision_on_real_worlds():
    runtime = load_runtime()
    report = runtime.analyze_worlds(load_literal_worlds(runtime))

    assert report["candidate_count"] == 17
    assert report["character_collision_size"] == 17
    assert report["character_table_observer_sufficient"] is False
    assert report["matrix_payload_loaded"] is False


def test_real_fusion_coordinate_is_opened_before_any_matrix_route():
    runtime = load_runtime()
    worlds = load_literal_worlds(runtime)
    report = runtime.analyze_worlds(worlds)

    assert "monster_class_fusion" in report["opened_coordinates"]
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
    report = runtime.analyze_worlds(load_literal_worlds(runtime))

    assert report["consumer"] == "which admissible D8 realization/fusion supplies the five-orbit action?"
    assert report["character_table_observer_sufficient"] is False
    assert report["quotient_route_creates_selected_action"] is False
    assert report["runtime_search_creates_factors_through_theorem"] is False
