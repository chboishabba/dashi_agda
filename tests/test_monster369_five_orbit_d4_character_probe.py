from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "monster369_five_orbit_d4_character_probe.py"


def load_probe():
    spec = importlib.util.spec_from_file_location("monster369_five_orbit_d4_probe", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_five_inversion_orbit_permutation_character_decomposes_without_a2_or_e():
    probe = load_probe().build_report()

    assert probe["orbit_count"] == 5
    assert probe["conjugacy_class_sizes"] == [1, 1, 2, 2, 2]
    assert probe["permutation_character"] == [5, 5, 1, 3, 3]
    assert probe["irrep_multiplicities"] == {
        "A1": 3,
        "A2": 0,
        "B1": 1,
        "B2": 1,
        "E": 0,
    }
    assert probe["dimension_check"] == 5
    assert probe["one_to_one_orbit_to_irrep_semantic_map_paid"] is False
    assert probe["quotient_character_decomposition_paid_by_python"] is True
    assert probe["monster_42d_action_paid"] is False


def test_signed_weighted_inner_product_splits_match_kernel_arithmetic():
    probe = load_probe().build_report()

    assert probe["weighted_inner_product_splits"] == {
        "A1": {"positive": 24, "negative": 0, "multiplicity": 3},
        "A2": {"positive": 12, "negative": 12, "multiplicity": 0},
        "B1": {"positive": 16, "negative": 8, "multiplicity": 1},
        "B2": {"positive": 16, "negative": 8, "multiplicity": 1},
        "E": {"positive": 10, "negative": 10, "multiplicity": 0},
    }
    assert all(
        split["positive"] == 8 * split["multiplicity"] + split["negative"]
        for split in probe["weighted_inner_product_splits"].values()
    )


def test_quotient_character_is_raw_nine_character_with_two_e_copies_removed():
    probe = load_probe().build_report()

    assert probe["raw_nine_irrep_multiplicities"] == {
        "A1": 3,
        "A2": 0,
        "B1": 1,
        "B2": 1,
        "E": 2,
    }
    assert probe["quotient_irrep_multiplicities"] == {
        "A1": 3,
        "A2": 0,
        "B1": 1,
        "B2": 1,
        "E": 0,
    }
    assert probe["removed_dimension"] == 4
    assert probe["removed_irrep_content"] == {"E": 2}


def test_d4_to_n3b_screen_retains_occurrences_without_promoting_action_identity():
    probe = load_probe().build_report()
    screen = probe["d4_to_n3b_screen"]

    assert screen["n3b_degree_occurrences_paid"] == {17496: True, 113724: True}
    assert screen["selected3b_normalizer_monster_action_weld_paid"] is False
    assert screen["d4_subgroup_embedding_paid"] is False
    assert screen["d4_quotient_character_restriction_same_object_paid"] is False
    assert screen["d4_quotient_equals_n3b_character"] is False
    assert screen["monster_42d_action_paid"] is False
