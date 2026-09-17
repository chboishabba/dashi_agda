from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "monster369_oeis_acquisition_snapshot.py"


def load_runtime():
    spec = importlib.util.spec_from_file_location("monster369_oeis_acquisition", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_a005052_ladder_snapshot_retains_90_65610_196830():
    runtime = load_runtime()
    node = runtime.SEQUENCES["A005052"]

    assert node["formula"] == "10*3^n"
    assert node["selected_terms"] == {2: 90, 8: 65610, 9: 196830}
    assert node["authority"] == "numerical-navigation"


def test_a025616_parent_lattice_contains_90_729_65610_196830():
    runtime = load_runtime()
    node = runtime.SEQUENCES["A025616"]

    assert node["formula"] == "3^i*10^j"
    assert node["selected_values"] == {90, 729, 65610, 196830}
    relation = runtime.RELATIONS["a025616-parent-lattice"]
    assert relation["paid"] is True
    assert relation["same_object_paid"] is False


def test_42d_snapshot_retains_17496_eta_product_bridge_candidate():
    runtime = load_runtime()
    node = runtime.SEQUENCES["A058678"]

    assert node["class_label"] == "42d"
    assert 17496 in node["selected_values"]
    assert "eta(q^3)" in node["formula"]
    relation = runtime.RELATIONS["42d-17496-to-n3b-restriction"]
    assert relation["paid"] is True
    assert relation["same_object_paid"] is False


def test_42_class_eta_family_retains_native_14_and_42_levels():
    runtime = load_runtime()

    assert runtime.SEQUENCES["A058674"]["class_label"] == "42D"
    assert "eta(q^14)" in runtime.SEQUENCES["A058674"]["formula"]
    assert "eta(q^42)" in runtime.SEQUENCES["A058674"]["formula"]
    assert runtime.SEQUENCES["A058676"]["class_label"] == "42b"
    assert runtime.SEQUENCES["A058677"]["class_label"] == "42c"
    assert runtime.SEQUENCES["A058678"]["class_label"] == "42d"
    relation = runtime.RELATIONS["42-class-eta-level-family"]
    assert relation["paid"] is True
    assert relation["levels"] == {3, 7, 14, 21, 42}
    assert relation["fifteen_minus_one_explanation_paid"] is False


def test_ternary27_reduces_as_three_preserved_phases_times_five_inner_orbits():
    runtime = load_runtime()
    probe = runtime.build_ternary27_phase_preserving_reduction_probe()

    assert probe["raw_state_count"] == 27
    assert probe["outer_phase_count"] == 3
    assert probe["inner_sheet_state_count"] == 9
    assert probe["inner_global_inversion_orbit_count"] == 5
    assert probe["phase_preserving_reduced_state_count"] == 15
    assert probe["image_state_count"] == 15
    assert probe["fiber_size_histogram"] == {1: 3, 2: 12}
    assert probe["full_global_inversion_orbit_count"] == 14
    assert probe["phase_preserving_reduction_is_full_global_inversion"] is False
    assert probe["twenty_seven_to_three_times_five_reduction_paid"] is True
    assert probe["three_times_five_carrier_is_monster_class_42d_paid"] is False


def test_42d_five_mode_phase_probe_realizes_15_14_42_without_authority_promotion():
    runtime = load_runtime()
    probe = runtime.build_42d_five_mode_phase_probe()

    assert probe["mode_count"] == 5
    assert probe["phase_count"] == 3
    assert probe["lane_count"] == 15
    assert probe["binary_oriented_lane_count"] == 10
    assert probe["five_plus_ten"] == 15
    assert probe["distinguished_lane"] == ("mode09", 0)
    assert probe["residual_lane_count"] == 14
    assert probe["outer_phase_count"] == 3
    assert probe["outer_phase_times_residual"] == 42
    assert probe["twenty_seven_to_five_mode_selection_paid"] is False
    assert probe["twenty_seven_to_three_times_five_reduction_paid"] is True
    assert probe["forty_two_carrier_is_monster_class_42d_paid"] is False


def test_ssp14_global14_weld_is_bijective_but_not_canonical_lift_induced():
    runtime = load_runtime()
    probe = runtime.build_ssp14_global14_weld_probe()

    assert probe["residual_lane_count"] == 14
    assert probe["global_inversion_orbit_count"] == 14
    assert probe["canonical_lift_image_count"] == 13
    assert probe["canonical_lift_duplicate_orbit"] == (-1, 0, 0)
    assert probe["canonical_lift_missing_orbit"] == (0, 0, 0)
    assert probe["explicit_weld_image_count"] == 14
    assert probe["explicit_weld_is_bijection"] is True
    assert probe["explicit_weld_is_canonical_lift_induced"] is False
    assert probe["exceptional_lane"] == ("mode09", 1)
    assert probe["exceptional_lane_target"] == (0, 0, 0)
    assert probe["weld_creates_monster_action"] is False


def test_6b_normalization_family_retains_q6_32772_across_three_manifests():
    runtime = load_runtime()

    family = [runtime.SEQUENCES[key] for key in ("A007255", "A045485", "A121665")]
    assert {node["class_label"] for node in family} == {"6B"}
    assert {node["q0"] for node in family} == {0, 7, 12}
    assert {node["positive_coefficients"][6] for node in family} == {32772}
    assert all(node["positive_coefficients"][1] == 78 for node in family)


def test_power_family_trace_nodes_are_acquired_but_not_action_authority():
    runtime = load_runtime()

    assert runtime.SEQUENCES["A007244"]["positive_coefficients"][1] == 54
    assert runtime.SEQUENCES["A007246"]["positive_coefficients"][1] == 276
    assert runtime.SEQUENCES["A014708"]["positive_coefficients"][1] == 196884
    assert all(
        runtime.SEQUENCES[key]["authority"] == "source-navigation"
        for key in ("A007244", "A007246", "A014708")
    )


def test_snapshot_keeps_positive_bridge_signal_separate_from_proof_authority():
    runtime = load_runtime()
    report = runtime.build_report()

    assert report["positive_bridge_candidates"]["a005052-heisenberg-ladder"] is True
    assert report["positive_bridge_candidates"]["a025616-parent-lattice"] is True
    assert report["positive_bridge_candidates"]["6b-q6-to-c6-spectrum-32772"] is True
    assert report["positive_bridge_candidates"]["17496-42d-to-n3b-restriction"] is True
    assert report["positive_bridge_candidates"]["42d-five-mode-phase-carrier"] is True
    assert report["positive_bridge_candidates"]["42-class-eta-level-family"] is True
    assert report["positive_bridge_candidates"]["ternary27-phase-preserving-3x5-reduction"] is True
    assert report["authority"]["oeis_snapshot_creates_same_object"] is False
    assert report["authority"]["oeis_snapshot_creates_monster_action"] is False
    assert report["authority"]["positive_bridge_signal_creates_theorem"] is False
